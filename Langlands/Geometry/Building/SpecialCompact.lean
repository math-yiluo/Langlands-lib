import Langlands.Geometry.Building.KPBuilding

/-!
# The chosen apartment point and its actual compact stabilizer

This module fixes the subgroup used by the special maximal compact statements.
It adds no compactness, maximality, building-existence or Weyl-surjectivity assertion.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Pointwise
open Langlands.GroupScheme

namespace Langlands.Geometry.Building.KPApartmentData

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))}
  {i : S.toGrp ⟶ G} [Mono i.hom.hom.left] [IsAffineHom G.X.hom]
  (D : KPApartmentData i (localFieldOrder F))

/-- A special vertex in the chosen actual reduced apartment: the geometric
special-point predicate and the geometric vertex predicate for the same roots. -/
def IsSpecialApartmentVertex (x : D.Apartment) : Prop :=
  AffineRootSystem.IsSpecialPoint D.affineRoots x ∧
    AffineRootSystem.IsVertex D.affineRoots x

/-- The actual subgroup `K₀ = G(F)^1 ∩ Stab([x])` for the chosen apartment point.
It is called the special compact subgroup when `D.IsSpecialApartmentVertex x`
holds. Its topological and maximality properties require separate statements. -/
def specialCompactSubgroup (x : D.Apartment) : Subgroup (rationalPoints G) :=
  D.compactStabilizer (D.apartmentMap x)

theorem mem_specialCompactSubgroup {x : D.Apartment} {g : rationalPoints G} :
    g ∈ D.specialCompactSubgroup x ↔
      g ∈ Plancherel.rationalCommonNormKernel G ∧
        g • D.apartmentMap x = D.apartmentMap x :=
  D.mem_compactStabilizer

theorem specialCompactSubgroup_le_reducedFixer (x : D.Apartment) :
    D.specialCompactSubgroup x ≤ D.reducedFixer (D.apartmentMap x) :=
  D.compactStabilizer_le_reducedFixer _

theorem specialCompactSubgroup_le_rationalCommonNormKernel (x : D.Apartment) :
    D.specialCompactSubgroup x ≤ Plancherel.rationalCommonNormKernel G :=
  D.compactStabilizer_le_rationalCommonNormKernel _

/-- The actual normalizing points lying in the same chosen `K₀`, as a subgroup
of `N(F)`. Its elements represent `N(F) ∩ K₀`. -/
def specialCompactNormalizer (x : D.Apartment) : Subgroup (normalizerPoints i) :=
  (D.specialCompactSubgroup x).subgroupOf (normalizerPoints i)

theorem mem_specialCompactNormalizer {x : D.Apartment} {n : normalizerPoints i} :
    n ∈ D.specialCompactNormalizer x ↔
      (n : rationalPoints G) ∈ D.specialCompactSubgroup x :=
  Iff.rfl

/-- The restriction of the actual quotient map `N(F) → N(F)/Z(F)` to
`N(F) ∩ K₀`. Surjectivity is a separate target. -/
def specialCompactWeylMap (x : D.Apartment) :
    D.specialCompactNormalizer x →* relativeWeylGroup i :=
  (QuotientGroup.mk' ((centralizerPoints i).subgroupOf (normalizerPoints i))).comp
    (D.specialCompactNormalizer x).subtype

@[simp]
theorem specialCompactWeylMap_apply (x : D.Apartment)
    (n : D.specialCompactNormalizer x) :
    D.specialCompactWeylMap x n = (QuotientGroup.mk (n : normalizerPoints i) :
      relativeWeylGroup i) :=
  rfl

end Langlands.Geometry.Building.KPApartmentData
