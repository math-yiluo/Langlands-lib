import Langlands.Geometry.Building.ChamberProductInjective
import Langlands.Geometry.Building.ChamberParahoricConstancy

/-!
# Sharp normalizer separation from the sharp product range

The affine opposite-cell separation theorem removes a central factor from a
normalizing triple product. Applied to the sharp product, this identifies the
sharp normalizer and centralizer under an explicit factorization premise.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme

namespace Langlands.Geometry.Building

section Restriction

variable {k : Type u} [Field k]
  {S : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  (i : S.toGrp ⟶ G) (ν : cocharacterLattice S)

/-- A normalizing point in an opposite-unipotent/centralizer/unipotent
product equals its central factor. -/
theorem normalizer_eq_centralizer_of_unipotent_triple_product
    (n v z u : rationalPoints G)
    (hn : n ∈ normalizerPoints i)
    (hv : v ∈ (Dynamic.unipotent
      (CommGroupScheme.groupHom (-ν) ≫ i)).carrier (Over.mk (𝟙 _)))
    (hz : z ∈ centralizerPoints i)
    (hu : u ∈ (Dynamic.unipotent
      (CommGroupScheme.groupHom ν ≫ i)).carrier (Over.mk (𝟙 _)))
    (h : n = v * z * u) : n = z := by
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let χ := CommGroupScheme.groupHom ν ≫ i
  have hzχ : z ∈ (Dynamic.centralizer χ).carrier (Over.mk (𝟙 _)) := by
    apply torusCentralizer_le_dynamicCentralizer i (CommGroupScheme.groupHom ν)
      (Over.mk (𝟙 _))
    change z ∈ (torusCentralizer i).carrier (Over.mk (𝟙 _))
    rw [torusCentralizer_carrier_base]
    exact hz
  have hzu : z * u * z⁻¹ ∈ (Dynamic.unipotent χ).carrier (Over.mk (𝟙 _)) :=
    Dynamic.conj_mem_unipotent χ (Dynamic.centralizer_le_parabolic χ _ hzχ) hu
  let n' : normalizerPoints i :=
    ⟨n * z⁻¹, (normalizerPoints i).mul_mem hn
      ((normalizerPoints i).inv_mem (centralizerPoints_le_normalizerPoints i hz))⟩
  let v' : RationalPoint.unipotent
      (CommGroupScheme.groupHom (Gm.powerHom (Spec (CommRingCat.of k)) (-1)) ≫ χ) :=
    ⟨v, by
      rw [groupHom_neg_comp_eq_oppositeCocharacter i ν] at hv
      exact hv⟩
  let u' : RationalPoint.unipotent χ := ⟨z * u * z⁻¹, hzu⟩
  have hn' : n' = 1 := normalizer_eq_one_of_unipotent_product i ν n' v' u' (by
    change n * z⁻¹ = v * (z * u * z⁻¹)
    rw [h]
    simp only [mul_assoc])
  have hquot : n * z⁻¹ = 1 :=
    congrArg (fun m : normalizerPoints i => (m : rationalPoints G)) hn'
  exact mul_inv_eq_one.mp hquot

end Restriction

namespace KPApartmentData

variable {k : Type u} [Field k]
  {S : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}
  {i : S.toGrp ⟶ G} [Mono i.hom.hom.left] [IsAffineHom G.X.hom]
  {ω : kˣ → ℝ} (D : KPApartmentData i ω)

/-- Equality of the sharp normalizer and centralizer follows from the
sharp triple range and equality of the sharp fixers at the subset and point. -/
theorem sharpNormalizer_eq_sharpCentralizer_of_sharpProductRange
    (C : Set D.Apartment) (x : D.Apartment) (ν : cocharacterLattice S)
    (hfixer : D.sharpFixer C = D.sharpFixer {x})
    (hrange : Set.range (D.sharpUnipotentProduct C x ν) =
      (D.sharpFixer C : Set (rationalPoints G))) :
    D.sharpNormalizer {x} = D.sharpCentralizer {x} := by
  apply le_antisymm
  · intro n hn
    have hnC : n ∈ D.sharpFixer C := hfixer ▸ hn.2
    have hnR : n ∈ Set.range (D.sharpUnipotentProduct C x ν) := by
      rw [hrange]
      exact hnC
    obtain ⟨p, hp⟩ := hnR
    have hnz : n = (p.2.1 : rationalPoints G) :=
      normalizer_eq_centralizer_of_unipotent_triple_product i ν
        n p.1 p.2.1 p.2.2 hn.1 p.1.property.1 p.2.1.property.1 p.2.2.property.1
        hp.symm
    exact ⟨hnz ▸ p.2.1.property.1, hn.2⟩
  · intro z hz
    exact ⟨centralizerPoints_le_normalizerPoints i hz.1, hz.2⟩

/-- On a facet the sharp product range suffices for normalizer separation;
the fixer comparison is the published facet constancy theorem. -/
theorem sharpNormalizer_eq_sharpCentralizer_of_isFacet_of_sharpProductRange
    (hAS4 : ∀ ψ ∈ D.extendedAffineRoots,
      ψ ∈ D.affineRoots ∨ (2 : ℝ) • ψ ∈ D.affineRoots)
    {Fa : Set D.Apartment} (hFa : AffineRootSystem.IsFacet D.affineRoots Fa)
    {x : D.Apartment} (hx : x ∈ Fa) (ν : cocharacterLattice S)
    (hrange : Set.range (D.sharpUnipotentProduct Fa x ν) =
      (D.sharpFixer Fa : Set (rationalPoints G))) :
    D.sharpNormalizer {x} = D.sharpCentralizer {x} :=
  D.sharpNormalizer_eq_sharpCentralizer_of_sharpProductRange Fa x ν
    (D.sharpFixer_eq_singleton_of_isFacet hAS4 hFa hx) hrange

/-- Under the explicit sharp product range, the identity on rational points
identifies the sharp normalizer at a facet point with the sharp centralizer. -/
def sharpNormalizerCentralizerEquivOfSharpProductRange
    (hAS4 : ∀ ψ ∈ D.extendedAffineRoots,
      ψ ∈ D.affineRoots ∨ (2 : ℝ) • ψ ∈ D.affineRoots)
    {Fa : Set D.Apartment} (hFa : AffineRootSystem.IsFacet D.affineRoots Fa)
    {x : D.Apartment} (hx : x ∈ Fa) (ν : cocharacterLattice S)
    (hrange : Set.range (D.sharpUnipotentProduct Fa x ν) =
      (D.sharpFixer Fa : Set (rationalPoints G))) :
    D.sharpNormalizer {x} ≃* D.sharpCentralizer {x} :=
  MulEquiv.subgroupCongr
    (D.sharpNormalizer_eq_sharpCentralizer_of_isFacet_of_sharpProductRange
      hAS4 hFa hx ν hrange)

@[simp]
theorem coe_sharpNormalizerCentralizerEquivOfSharpProductRange
    (hAS4 : ∀ ψ ∈ D.extendedAffineRoots,
      ψ ∈ D.affineRoots ∨ (2 : ℝ) • ψ ∈ D.affineRoots)
    {Fa : Set D.Apartment} (hFa : AffineRootSystem.IsFacet D.affineRoots Fa)
    {x : D.Apartment} (hx : x ∈ Fa) (ν : cocharacterLattice S)
    (hrange : Set.range (D.sharpUnipotentProduct Fa x ν) =
      (D.sharpFixer Fa : Set (rationalPoints G)))
    (n : D.sharpNormalizer {x}) :
    (D.sharpNormalizerCentralizerEquivOfSharpProductRange hAS4 hFa hx ν hrange n :
      rationalPoints G) = n :=
  MulEquiv.subgroupCongr_apply
    (D.sharpNormalizer_eq_sharpCentralizer_of_isFacet_of_sharpProductRange
      hAS4 hFa hx ν hrange) n

end KPApartmentData

end Langlands.Geometry.Building
