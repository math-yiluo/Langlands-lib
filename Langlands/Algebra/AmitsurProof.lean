import Langlands.Algebra.AmitsurStatements
import Langlands.Algebra.NonnilpotentLeftResolventProof
import Mathlib.RingTheory.Nilpotent.Basic

/-!
# Renard B.I: proof of Amitsur's theorem

Proof of `Langlands.Renard.AmitsurTheoremStatement` (Renard, *Représentations des groupes
réductifs p-adiques*, 2026, Appendix B.I, printed pages 271–272). Instead of repeating the
source's resolvent argument, the spectrum assertions are derived from the one-sided result
`nonnilpotentLeftResolvent` of B.III: a nonnilpotent element `a` has a nonzero scalar `z`
such that `a - z` has no left inverse, so `z` is a nonzero spectral value. A nilpotent
element has spectrum `{0}` by the geometric series. In a division algebra, a spectral
value `z` of `d` makes `z - d` a noninvertible, hence zero, element, so `d` is a scalar.
-/

universe u

namespace Langlands.Renard

/-- If `a - z` has no left inverse, then `z` lies in the spectrum of `a`. -/
theorem mem_spectrum_of_forall_mul_sub_ne_one {A : Type u} [Ring A] [Algebra ℂ A] {a : A}
    {z : ℂ} (hz : ∀ b : A, b * (a - algebraMap ℂ A z) ≠ 1) : z ∈ spectrum ℂ a := by
  rw [spectrum.mem_iff]
  intro hu
  have hu' : IsUnit (a - algebraMap ℂ A z) := by
    rw [← neg_sub]
    exact hu.neg
  exact hz _ hu'.val_inv_mul

/-- In a nontrivial complex algebra, a nilpotent element has spectrum `{0}`: it is not a
unit, and each nonzero shift `z - a` is a unit by the geometric series. -/
theorem spectrum_eq_singleton_zero_of_isNilpotent {A : Type u} [Ring A] [Algebra ℂ A]
    [Nontrivial A] {a : A} (ha : IsNilpotent a) : spectrum ℂ a = ({0} : Set ℂ) := by
  ext z
  rw [Set.mem_singleton_iff]
  constructor
  · intro hz
    by_contra hz0
    apply spectrum.mem_iff.mp hz
    rw [sub_eq_add_neg]
    exact ha.neg.isUnit_add_left_of_commute ((IsUnit.mk0 z hz0).map (algebraMap ℂ A))
      (Algebra.commute_algebraMap_right z (-a))
  · rintro rfl
    exact (spectrum.zero_mem_iff ℂ).mpr ha.not_isUnit

/-- **Renard B.I, Théorème b), first assertion.** In a nontrivial unital complex algebra
of at most countable dimension, every element has nonempty spectrum. -/
theorem amitsurSpectrumNonempty (A : Type u) [Ring A] [Algebra ℂ A] [Nontrivial A] :
    AmitsurSpectrumNonemptyStatement A := by
  intro hrank a
  by_cases ha : IsNilpotent a
  · exact ⟨0, (spectrum.zero_mem_iff ℂ).mpr ha.not_isUnit⟩
  · obtain ⟨z, -, hz⟩ := nonnilpotentLeftResolvent A hrank a ha
    exact ⟨z, mem_spectrum_of_forall_mul_sub_ne_one hz⟩

/-- **Renard B.I, Théorème b), second assertion.** In a nontrivial unital complex algebra
of at most countable dimension, the spectrum of `a` is `{0}` exactly when `a` is
nilpotent. -/
theorem amitsurSpectrumSingletonZero (A : Type u) [Ring A] [Algebra ℂ A] [Nontrivial A] :
    AmitsurSpectrumSingletonZeroStatement A := by
  intro hrank a
  constructor
  · intro hspec
    by_contra ha
    obtain ⟨z, hz0, hz⟩ := nonnilpotentLeftResolvent A hrank a ha
    have hmem := mem_spectrum_of_forall_mul_sub_ne_one hz
    rw [hspec, Set.mem_singleton_iff] at hmem
    exact hz0 hmem
  · exact spectrum_eq_singleton_zero_of_isNilpotent

/-- **Renard B.I, Théorème a).** In a complex division algebra of at most countable
dimension, the canonical map `algebraMap ℂ D` is bijective. -/
theorem amitsurDivisionAlgebra (D : Type u) [DivisionRing D] [Algebra ℂ D] :
    AmitsurDivisionAlgebraStatement D := by
  intro hrank
  refine ⟨(algebraMap ℂ D).injective, fun d => ?_⟩
  obtain ⟨z, hz⟩ := amitsurSpectrumNonempty D hrank d
  refine ⟨z, sub_eq_zero.mp ?_⟩
  by_contra hne
  exact spectrum.mem_iff.mp hz (Ne.isUnit hne)

/-- Renard B.I, Théorème a), as an algebra isomorphism `ℂ ≃ₐ[ℂ] D` agreeing with
`algebraMap ℂ D`, obtained from `amitsurDivisionAlgebra` through
`amitsurDivisionAlgebraStatement_iff_equivStatement`. -/
theorem amitsurDivisionAlgebraEquiv (D : Type u) [DivisionRing D] [Algebra ℂ D] :
    AmitsurDivisionAlgebraEquivStatement D :=
  (amitsurDivisionAlgebraStatement_iff_equivStatement D).mp (amitsurDivisionAlgebra D)

/-- **Renard B.I, Théorème d'Amitsur**, for all carriers in universe `u`. -/
theorem amitsurTheorem : AmitsurTheoremStatement.{u} :=
  ⟨fun A _ _ _ => ⟨amitsurSpectrumNonempty A, amitsurSpectrumSingletonZero A⟩,
    fun D _ _ => amitsurDivisionAlgebra D⟩

end Langlands.Renard
