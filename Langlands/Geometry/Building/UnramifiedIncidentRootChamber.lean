import Langlands.Geometry.Building.UnramifiedSplitTorusFixedDirections

/-! # A same-apartment chamber from incident root restrictions -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.GroupScheme.GaloisPointComparison

namespace Langlands.Geometry.Building

variable (k K : Type u) [Field k] [Field K] [Algebra k K]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  (i : T.toGrp ⟶ G)
  {S : CommGroupScheme (Spec (CommRingCat.of k))}
  (hS : IsSplitTorus S.toGrp) (f : S ⟶ T)

local notation "b" => algebraBaseMap k K
local notation "T_K" => CategoryTheory.Functor.obj (CommGroupScheme.baseChange b) T
local notation "i_K" => CategoryTheory.Functor.map (GroupScheme.baseChange b) i
local notation "f_K" => CategoryTheory.Functor.map (CommGroupScheme.baseChange b) f

include hS

/-- The raw nonzero composite is precisely nonzero rational-character
restriction, so it supplies a common coefficient-fixed direction. -/
theorem exists_galois_fixed_direction_of_root_comp_ne_zero
    (a : relativeRoots (T := T_K) i_K) (ha : f_K ≫ a.val ≠ 0) :
    ∃ v : TranslationSpace (S := T_K) i_K,
      (∀ σ : K ≃ₐ[k] K, galoisTranslationAction k K i σ v = v) ∧
        rootForm (S := T_K) i_K a v ≠ 0 := by
  apply exists_galois_fixed_direction_of_root_restrict_ne_zero k K i hS f a
  change f_K ≫ a.val ≠ 0
  exact ha

namespace KPApartmentData

variable [Mono ((GroupScheme.baseChange (algebraBaseMap k K)).map i).hom.hom.left]
  {ω : Kˣ → ℝ}
  (D : KPApartmentData
    (S := (CommGroupScheme.baseChange (algebraBaseMap k K)).obj T)
    ((GroupScheme.baseChange (algebraBaseMap k K)).map i) ω)

/-- Raw nonzero compositions of incident derivative roots give the direction
condition in the same supplied apartment. -/
theorem hasIncidentGaloisDirections_of_root_comp_ne_zero (p : D.Apartment)
    (hroot : ∀ a : relativeRoots (T := T_K) i_K,
      (∃ ψ ∈ D.affineRoots, ψ p = 0 ∧ ψ.linear = rootForm (S := T_K) i_K a) →
        f_K ≫ a.val ≠ 0) :
    HasIncidentGaloisDirections k K i D p := by
  apply hasIncidentGaloisDirections_of_root_restrict_ne_zero k K i hS f D p
  intro a ha
  change f_K ≫ a.val ≠ 0
  exact hroot a ha

variable {v : Valuation K (WithZero (Multiplicative ℤ))}
  (D' : KPApartmentData
    (S := (CommGroupScheme.baseChange (algebraBaseMap k K)).obj T)
    ((GroupScheme.baseChange (algebraBaseMap k K)).map i) (IntegerValuation.order v))
  (hG : IsConnectedReductive (baseChanged k K G))
  (hi : IsMaximalSplitTorus
    (T := (CommGroupScheme.baseChange (algebraBaseMap k K)).obj T)
    ((GroupScheme.baseChange (algebraBaseMap k K)).map i))
  (C : CentralizerDatum
    (S := (CommGroupScheme.baseChange (algebraBaseMap k K)).obj T)
    ((GroupScheme.baseChange (algebraBaseMap k K)).map i))
  (h6 : IntegerValuation.IsOmegaCompatible v D' C)
  (hD : GaloisStable k K i D')

include hG hi C h6

/-- Incident root nonvanishing on a supplied split torus produces an ordinary
stable chamber inside the same compatible integer-valued apartment. -/
theorem exists_regular_galois_stable_facet_of_root_comp_ne_zero
    (p : D'.Apartment)
    (hp : ∀ σ : K ≃ₐ[k] K, galoisAffineAction k K i D' hD σ p = p)
    (hroot : ∀ a : relativeRoots (T := T_K) i_K,
      (∃ ψ ∈ D'.affineRoots, ψ p = 0 ∧ ψ.linear = rootForm (S := T_K) i_K a) →
        f_K ≫ a.val ≠ 0) :
    ∃ x : D'.Apartment, AffineRootSystem.GalleryGeometry.IsRegular D'.affineRoots x ∧
      ∀ σ : K ≃ₐ[k] K,
        galoisAffineAction k K i D' hD σ '' AffineRootSystem.facet D'.affineRoots x =
          AffineRootSystem.facet D'.affineRoots x :=
  exists_regular_galois_stable_facet_of_directions k K i D' hG hi C h6 hD p hp
    (hasIncidentGaloisDirections_of_root_comp_ne_zero k K i hS f D' p hroot)

/-- A chosen ordinary chamber point in the supplied apartment, retaining
regularity and invariance of its whole sign facet. -/
def incidentRootChamberPoint
    (p : D'.Apartment)
    (hp : ∀ σ : K ≃ₐ[k] K, galoisAffineAction k K i D' hD σ p = p)
    (hroot : ∀ a : relativeRoots (T := T_K) i_K,
      (∃ ψ ∈ D'.affineRoots, ψ p = 0 ∧ ψ.linear = rootForm (S := T_K) i_K a) →
        f_K ≫ a.val ≠ 0) :
    {x : D'.Apartment // AffineRootSystem.GalleryGeometry.IsRegular D'.affineRoots x ∧
      ∀ σ : K ≃ₐ[k] K,
        galoisAffineAction k K i D' hD σ '' AffineRootSystem.facet D'.affineRoots x =
          AffineRootSystem.facet D'.affineRoots x} :=
  ⟨(exists_regular_galois_stable_facet_of_root_comp_ne_zero
      k K i hS f D' hG hi C h6 hD p hp hroot).choose,
    (exists_regular_galois_stable_facet_of_root_comp_ne_zero
      k K i hS f D' hG hi C h6 hD p hp hroot).choose_spec⟩

end KPApartmentData
end Langlands.Geometry.Building
