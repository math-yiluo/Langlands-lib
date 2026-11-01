import Langlands.AlgebraicGeometry.Modules.EulerCharacteristic

/-! # Basic identities for actual cohomological Euler characteristics -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.Modules.DerivedSections

/-- Cutoff, isomorphism invariance and elementary vanishing identities for
actual finite sheaf cohomology. -/
def EulerCharacteristicBasicStatement : Prop :=
  ∀ (K : Type u) [Field K] (X : Scheme.{u})
    (f : X ⟶ Spec (CommRingCat.of K)),
    (∀ (M : X.Modules) (hM : HasFiniteCohomology f M) (N : ℕ),
      (∀ n : ℕ, N ≤ n → IsZero ((relativeCohomology f n).obj M)) →
        eulerCharacteristic f M hM = ∑ n ∈ Finset.range N,
          (-1 : ℤ) ^ n * (Module.finrank K ((relativeCohomology f n).obj M) : ℤ)) ∧
    (∀ (M N : X.Modules) (_e : M ≅ N),
      HasFiniteCohomology f M ↔ HasFiniteCohomology f N) ∧
    (∀ (M N : X.Modules) (hM : HasFiniteCohomology f M)
      (hN : HasFiniteCohomology f N) (_e : M ≅ N),
      eulerCharacteristic f M hM = eulerCharacteristic f N hN) ∧
    (∀ (M : X.Modules) (hM : HasFiniteCohomology f M),
      (∀ n : ℕ, IsZero ((relativeCohomology f n).obj M)) →
        eulerCharacteristic f M hM = 0) ∧
    (∀ (M : X.Modules) (hM : HasFiniteCohomology f M),
      (∀ n : ℕ, 0 < n → IsZero ((relativeCohomology f n).obj M)) →
        eulerCharacteristic f M hM =
          (Module.finrank K ((relativeCohomology f 0).obj M) : ℤ))

end Langlands.AlgebraicGeometry.Modules.DerivedSections
