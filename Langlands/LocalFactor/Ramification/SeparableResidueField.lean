import Mathlib.RingTheory.DedekindDomain.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Separable

/-!
# Separable residue field extensions over a local Dedekind domain

Mathlib states the order of an inertia group (`Ideal.card_inertia_eq_ramificationIdxIn`) under
`Algebra.HasSeparableResidueFieldsAt R S p`: the residue field extension `κ(q)/κ(p)` is separable
for every prime `q` over `p`. When `S` is a local Dedekind domain, torsion-free over a local
domain `R`, and `p` is the non-zero maximal ideal of `R`, the only prime over `p` is the maximal
ideal of `S`, so the condition is the separability of `R ⧸ p → S ⧸ maximalIdeal S`. This file
proves that reduction.
-/

namespace Langlands.Ramification

open IsLocalRing

/-- Over the non-zero maximal ideal of a local domain `A`, a local Dedekind domain `B` that is
torsion-free over `A` has separable residue fields as soon as `A ⧸ m_A → B ⧸ m_B` is separable. -/
theorem hasSeparableResidueFieldsAt_maximalIdeal_of_isSeparable
    {A B : Type*} [CommRing A] [IsLocalRing A] [IsDomain A]
    [CommRing B] [IsDedekindDomain B] [IsLocalRing B]
    [Algebra A B] [Module.IsTorsionFree A B]
    [(maximalIdeal B).LiesOver (maximalIdeal A)]
    [Algebra.IsSeparable (A ⧸ maximalIdeal A) (B ⧸ maximalIdeal B)]
    (hp : maximalIdeal A ≠ ⊥) :
    Algebra.HasSeparableResidueFieldsAt A B (maximalIdeal A) := by
  refine ⟨fun q _ hq => ?_⟩
  -- the only prime of `B` over `m_A` is `m_B`
  have hq0 : q ≠ ⊥ := by
    rintro rfl
    apply hp
    rw [hq.over, Ideal.under, Ideal.comap_bot_of_injective _ (FaithfulSMul.algebraMap_injective A B)]
  have : q.IsMaximal := Ideal.isMaximal_of_isPrime_of_ne_bot q hq0
  obtain rfl : q = maximalIdeal B := IsLocalRing.eq_maximalIdeal this
  let := Localization.AtPrime.algebraOfLiesOver (maximalIdeal A) (maximalIdeal B)
  exact Algebra.isSeparable_residueField_iff.mpr inferInstance

end Langlands.Ramification
