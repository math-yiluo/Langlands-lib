import Langlands.GroupScheme.Torus.NilpotentDiagonalizableDeformation
import Langlands.GroupScheme.Torus.CompleteLocalSimultaneousSplitting
import Langlands.GroupScheme.HomScheme.FibreComparison
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! # Diagonalizable models and Hom restriction on local adic quotients -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme.CompleteLocalDeformation

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

namespace LocalAdic

variable (A : Type u) [CommRing A] [IsLocalRing A]

/-- The local ring of the `n`th infinitesimal neighbourhood of the closed point. -/
abbrev Ring (n : ℕ) := A ⧸ IsLocalRing.maximalIdeal A ^ (n + 1)

instance nontrivial (n : ℕ) : Nontrivial (Ring A n) := by
  have hm : (IsLocalRing.maximalIdeal A).IsMaximal := inferInstance
  exact Ideal.Quotient.nontrivial_iff.mpr
    (ne_top_of_le_ne_top hm.ne_top (Ideal.pow_le_self (by omega)))

instance isLocalRing (n : ℕ) : IsLocalRing (Ring A n) :=
  IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective

instance isLocalHom (n : ℕ) : IsLocalHom (algebraMap A (Ring A n)) :=
  IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective

/-- The maximal ideal of the adic quotient is killed by the defining exponent. -/
theorem maximalIdeal_pow_eq_bot (n : ℕ) :
    IsLocalRing.maximalIdeal (Ring A n) ^ (n + 1) = ⊥ := by
  have hm := IsLocalRing.map_maximalIdeal_of_surjective
    (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A ^ (n + 1)))
    Ideal.Quotient.mk_surjective
  rw [← hm, ← Ideal.map_pow, Ideal.map_quotient_self]

theorem maximalIdeal_isNilpotent (n : ℕ) :
    IsNilpotent (IsLocalRing.maximalIdeal (Ring A n)) :=
  ⟨n + 1, maximalIdeal_pow_eq_bot A n⟩

/-- A diagonalizable special fibre gives diagonalizable actual groups on every
local adic quotient when the original group is flat and affine. -/
theorem isDiagonalizable (G : GroupScheme (Spec (CommRingCat.of A)))
    [IsAffine G.X.left] [Flat G.X.hom]
    (hG : RelativeMultiplicativeType.IsDiagonalizable
      ((GroupScheme.baseChange
        (Spec.algebraMap A (IsLocalRing.ResidueField A))).obj G)) (n : ℕ) :
    RelativeMultiplicativeType.IsDiagonalizable
      ((GroupScheme.baseChange (Spec.algebraMap A (Ring A n))).obj G) := by
  let B := Ring A n
  let c := Spec.algebraMap A B
  let Gn := (GroupScheme.baseChange c).obj G
  have : IsAffine Gn.X.left := by
    change IsAffine (CategoryTheory.Limits.pullback G.X.hom c)
    infer_instance
  have : Flat Gn.X.hom := by
    change Flat (CategoryTheory.Limits.pullback.snd _ _)
    infer_instance
  have hGn : RelativeMultiplicativeType.IsDiagonalizable
      ((GroupScheme.baseChange (Spec.algebraMap B (IsLocalRing.ResidueField B))).obj Gn) :=
    RelativeMultiplicativeType.IsDiagonalizable.of_iso (specialFibreBaseChangeIso G)
      (hG.baseChange
        (Spec.algebraMap (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B)))
  exact isDiagonalizable_of_nilpotent_reduction Gn (IsLocalRing.maximalIdeal B)
    (maximalIdeal_isNilpotent A n) hGn

end LocalAdic

/-- Restriction of actual relative Hom families is bijective when their groups
over the larger local test scheme are diagonalizable. -/
theorem evaluate_bijective_of_isDiagonalizable
    {S : Scheme.{u}} {H G : GroupScheme S}
    {A B : Type u} [CommRing A] [IsLocalRing A] [CommRing B] [IsLocalRing B]
    (s : Spec (CommRingCat.of A) ⟶ S) (s' : Spec (CommRingCat.of B) ⟶ S)
    (a : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of A)) (ha : a ≫ s = s')
    (hH : RelativeMultiplicativeType.IsDiagonalizable ((GroupScheme.baseChange s).obj H))
    (hG : RelativeMultiplicativeType.IsDiagonalizable ((GroupScheme.baseChange s).obj G)) :
    Function.Bijective (HomScheme.evaluate (H := H) (G := G)
      (show Over.mk s' ⟶ Over.mk s from Over.homMk a ha)) := by
  let e := Iso.homCongr
    (Descent.pullbackComparison s a s' ha H)
    (Descent.pullbackComparison s a s' ha G)
  change Function.Bijective (fun f => e ((GroupScheme.baseChange a).map f))
  exact e.bijective.comp (diagonalizable_baseChange_hom_bijective a hH hG)

/-- The actual family-restriction equivalence on local diagonalizable tests. -/
def diagonalizableEvaluationEquiv
    {S : Scheme.{u}} {H G : GroupScheme S}
    {A B : Type u} [CommRing A] [IsLocalRing A] [CommRing B] [IsLocalRing B]
    (s : Spec (CommRingCat.of A) ⟶ S) (s' : Spec (CommRingCat.of B) ⟶ S)
    (a : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of A)) (ha : a ≫ s = s')
    (hH : RelativeMultiplicativeType.IsDiagonalizable ((GroupScheme.baseChange s).obj H))
    (hG : RelativeMultiplicativeType.IsDiagonalizable ((GroupScheme.baseChange s).obj G)) :
    HomScheme.RelativeHom H G (Over.mk s) ≃ HomScheme.RelativeHom H G (Over.mk s') :=
  Equiv.ofBijective _ (evaluate_bijective_of_isDiagonalizable s s' a ha hH hG)

end Langlands.GroupScheme.CompleteLocalDeformation
