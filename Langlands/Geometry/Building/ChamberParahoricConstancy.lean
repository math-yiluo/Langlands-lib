import Langlands.Geometry.Building.ChamberFiltration
import Langlands.Geometry.Building.ChamberIwahori

/-! # Point-preserving facet parahoric identifications -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme

namespace Langlands.Geometry.Building.KPApartmentData

variable {k : Type u} [Field k]
  {S : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}
  {i : S.toGrp ⟶ G} [Mono i.hom.hom.left] [IsAffineHom G.X.hom]
  {ω : kˣ → ℝ} (D : KPApartmentData i ω)
  (hAS4 : ∀ ψ ∈ D.extendedAffineRoots,
    ψ ∈ D.affineRoots ∨ (2 : ℝ) • ψ ∈ D.affineRoots)

include hAS4

/-- On a facet, the root-generated sharp subgroup is the subgroup at any
one of its points. -/
theorem sharpFixer_eq_singleton_of_isFacet {Fa : Set D.Apartment}
    (hFa : AffineRootSystem.IsFacet D.affineRoots Fa)
    {x : D.Apartment} (hx : x ∈ Fa) :
    D.sharpFixer Fa = D.sharpFixer {x} := by
  unfold sharpFixer
  apply iSup_congr
  intro a
  rw [(D.rootFixer_eq_filtration_of_isFacet hAS4 hFa hx a.property).1,
    D.rootFixer_singleton]

/-- The sharp normalizer intersection is constant on a facet. -/
theorem sharpNormalizer_eq_singleton_of_isFacet {Fa : Set D.Apartment}
    (hFa : AffineRootSystem.IsFacet D.affineRoots Fa)
    {x : D.Apartment} (hx : x ∈ Fa) :
    D.sharpNormalizer Fa = D.sharpNormalizer {x} := by
  unfold sharpNormalizer
  rw [D.sharpFixer_eq_singleton_of_isFacet hAS4 hFa hx]

/-- The sharp centralizer intersection is constant on a facet. -/
theorem sharpCentralizer_eq_singleton_of_isFacet {Fa : Set D.Apartment}
    (hFa : AffineRootSystem.IsFacet D.affineRoots Fa)
    {x : D.Apartment} (hx : x ∈ Fa) :
    D.sharpCentralizer Fa = D.sharpCentralizer {x} := by
  unfold sharpCentralizer
  rw [D.sharpFixer_eq_singleton_of_isFacet hAS4 hFa hx]

/-- The identity of rational points identifies the sharp facet group with
the sharp group at a chosen point of the facet. -/
def sharpFacetEquivAt {Fa : Set D.Apartment}
    (hFa : AffineRootSystem.IsFacet D.affineRoots Fa)
    {x : D.Apartment} (hx : x ∈ Fa) :
    D.sharpFixer Fa ≃* D.sharpFixer {x} :=
  MulEquiv.subgroupCongr (D.sharpFixer_eq_singleton_of_isFacet hAS4 hFa hx)

@[simp]
theorem coe_sharpFacetEquivAt {Fa : Set D.Apartment}
    (hFa : AffineRootSystem.IsFacet D.affineRoots Fa)
    {x : D.Apartment} (hx : x ∈ Fa) (g : D.sharpFixer Fa) :
    (D.sharpFacetEquivAt hAS4 hFa hx g : rationalPoints G) = g :=
  MulEquiv.subgroupCongr_apply
    (D.sharpFixer_eq_singleton_of_isFacet hAS4 hFa hx) g

end Langlands.Geometry.Building.KPApartmentData

namespace Langlands.Geometry.Building.ParahoricBuildingData

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  (P : ParahoricBuildingData G)
  (hD : P.apartment.SatisfiesApartmentAxioms P.centralizer)

include hD

/-- Adjoining the actual mapped centralizer zero subgroup preserves the
facet constancy of the sharp group. -/
theorem parahoric_eq_parahoricAt_of_isFacet {Fa : Set P.Apartment}
    (hFa : AffineRootSystem.IsFacet P.affineRoots Fa)
    {x : P.Apartment} (hx : x ∈ Fa) :
    P.parahoric Fa = P.parahoricAt x := by
  unfold parahoricAt parahoric
  change _ ⊔ P.apartment.sharpFixer Fa = _ ⊔ P.apartment.sharpFixer {x}
  rw [P.apartment.sharpFixer_eq_singleton_of_isFacet
    hD.mem_or_two_smul_mem hFa hx]

/-- The point parahoric does not depend on the chosen point in a facet. -/
theorem parahoricAt_eq_of_mem_isFacet {Fa : Set P.Apartment}
    (hFa : AffineRootSystem.IsFacet P.affineRoots Fa)
    {x y : P.Apartment} (hx : x ∈ Fa) (hy : y ∈ Fa) :
    P.parahoricAt x = P.parahoricAt y :=
  (P.parahoric_eq_parahoricAt_of_isFacet hD hFa hx).symm.trans
    (P.parahoric_eq_parahoricAt_of_isFacet hD hFa hy)

/-- The actual chamber Iwahori is the full parahoric at any point of the
chamber. This is the first equality of `ChamberIwahoriConclusion`. -/
theorem chamberIwahori_eq_parahoricAt {C : Set P.Apartment}
    (hC : AffineRootSystem.IsChamber P.affineRoots C)
    {x : P.Apartment} (hx : x ∈ C) :
    P.chamberIwahori C = P.parahoricAt x :=
  P.parahoric_eq_parahoricAt_of_isFacet hD hC.isFacet hx

/-- The identity of rational points identifies the actual full facet
parahoric with the full parahoric at a chosen point of the facet. -/
def parahoricFacetEquivAt {Fa : Set P.Apartment}
    (hFa : AffineRootSystem.IsFacet P.affineRoots Fa)
    {x : P.Apartment} (hx : x ∈ Fa) :
    P.parahoric Fa ≃* P.parahoricAt x :=
  MulEquiv.subgroupCongr (P.parahoric_eq_parahoricAt_of_isFacet hD hFa hx)

@[simp]
theorem coe_parahoricFacetEquivAt {Fa : Set P.Apartment}
    (hFa : AffineRootSystem.IsFacet P.affineRoots Fa)
    {x : P.Apartment} (hx : x ∈ Fa) (g : P.parahoric Fa) :
    (P.parahoricFacetEquivAt hD hFa hx g : rationalPoints G) = g :=
  MulEquiv.subgroupCongr_apply
    (P.parahoric_eq_parahoricAt_of_isFacet hD hFa hx) g

end Langlands.Geometry.Building.ParahoricBuildingData
