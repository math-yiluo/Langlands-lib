import Langlands.GroupScheme.Quaternionic.SkewUnitaryGaloisAssembly
import Langlands.GroupScheme.Quaternionic.SkewUnitaryGaloisWitt
import Langlands.GroupScheme.Quaternionic.SkewUnitaryGaloisRankOne

/-! # The special unitary Hasse principle at the Galois level

For a central quaternion division algebra over a number field with its canonical conjugation,
special unitary crossed homomorphisms of every invertible antihermitian Gram matrix satisfy the
Hasse principle: coboundary data at every completion give a global special unitary primitive.
-/

noncomputable section

universe u

namespace Langlands.GroupScheme.Quaternionic.SkewUnitary

variable {F D : Type u} [Field F] [NumberField F] [DivisionRing D] [Algebra F D]
  [Algebra.IsCentral F D] [FiniteDimensional F D]
  (σ : FirstKindInvolution F D) (hdim : Module.finrank F D = 4)
  (hsym : Module.finrank F σ.symmetricSubspace = 3)

/-- The special unitary Hasse principle for Gram matrices of every positive size. -/
theorem suHasse (n : ℕ) [NeZero n] : SUHasse σ hdim hsym n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := Nat.exists_eq_succ_of_ne_zero (NeZero.ne n)
  exact suHasse_of_rankOne σ hdim hsym
    (fun N _ hN K _ _ _ => properWittAt σ hdim hsym K N hN) (suHasse_one σ hdim hsym) m

end Langlands.GroupScheme.Quaternionic.SkewUnitary
