import Langlands.Algebra.NonUnitalModuleCornerInduction

/-!
# Renard I.3.2: the two complex structures on `A ⊗_{eAe} Z` coincide

Renard (9 July 2026), I.3.2, the remark after the Lemma (I.3.2.1), printed p.20 / PDF p.26.
A unital `eAe`-module `Z` is a complex vector space through `c ↦ c e`; the complex algebra `A`
is one as well, and the two complex structures induced on the actual balanced quotient
`A ⊗_{eAe} Z` coincide.
-/

set_option autoImplicit false

namespace Langlands.Algebra.NonUnitalModuleCornerInduction

universe uA uZ

/-- Renard I.3.2, remark after (I.3.2.1): for a complex algebra `A`, an idempotent `e` and a
unital `eAe`-module `Z`,
(1) `Z` is a complex vector space on which `c` acts as the corner element `c e`;
(2) the actual quotient `A ⊗_{eAe} Z` carries a complex structure that is at the same time the
one induced from `A`, `c • (a ⊗ z) = (c a) ⊗ z`, and the one induced from `Z`,
`c • (a ⊗ z) = a ⊗ ((c e) · z)`. -/
def ComplexScalarsStatement : Prop :=
  ∀ (A : Type uA) [NonUnitalRing A] [Module ℂ A] [IsScalarTower ℂ A A] [SMulCommClass ℂ A A]
    (e : Idempotent A) (Z : Type uZ) [AddCommGroup Z] [Module (Idempotent.Corner e) Z],
    (∃ MZ : Module ℂ Z, ∀ c : ℂ, ∃ s : Idempotent.Corner e,
        Idempotent.Corner.toAmbient e s = c • (e : A) ∧
          ∀ z : Z, (letI := MZ; c • z) = s • z) ∧
    (letI := tensorAddCommGroup e Z
      ∃ MT : Module ℂ (Tensor e Z),
        ∀ (c : ℂ) (s : Idempotent.Corner e), Idempotent.Corner.toAmbient e s = c • (e : A) →
          ∀ (a : A) (z : Z),
            (letI := MT; c • tmul e a z) = tmul e (c • a) z ∧
              (letI := MT; c • tmul e a z) = tmul e a (s • z))

end Langlands.Algebra.NonUnitalModuleCornerInduction
