import Langlands.AlgebraicGeometry.Modules.TensorCoherenceMaps

/-! # Isomorphisms for actual sheaf tensor powers -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.Scheme.Modules

variable {X : Scheme.{u}}

/-- The first tensor power is identified with the original sheaf by the right unitor. -/
def tensorPowOneIso (P : X.Modules) : tensorPow P 1 ≅ P :=
  tensorRightUnitor P

/-- An isomorphism of module sheaves induces an isomorphism of all tensor powers. -/
def tensorPowIso {P Q : X.Modules} (e : P ≅ Q) :
    (n : ℕ) → tensorPow P n ≅ tensorPow Q n
  | 0 => Iso.refl _
  | n + 1 => (tensorFunctor X).mapIso (e.prod (tensorPowIso e n))

/-- The induced isomorphism has exactly the previously defined tensor-power map as its hom. -/
@[simp]
lemma tensorPowIso_hom {P Q : X.Modules} (e : P ≅ Q) (n : ℕ) :
    (tensorPowIso e n).hom = tensorPowMap e.hom n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change tensorMap e.hom (tensorPowIso e n).hom = tensorMap e.hom (tensorPowMap e.hom n)
      rw [ih]

/-- Combine two right-associated tensor powers by recursion on the first exponent. -/
def tensorPowAddIso (P : X.Modules) :
    (a b : ℕ) → tensorObj (tensorPow P a) (tensorPow P b) ≅ tensorPow P (a + b)
  | 0, b => by
      simpa only [Nat.zero_add, tensorPow] using tensorLeftUnitor (tensorPow P b)
  | a + 1, b => by
      simpa only [Nat.succ_add, tensorPow] using
        (tensorAssociator P (tensorPow P a) (tensorPow P b) ≪≫
          (tensorFunctor X).mapIso ((Iso.refl P).prod (tensorPowAddIso P a b)))

/-- Flatten a tensor power of a tensor power by recursion on the outer exponent. -/
def tensorPowMulIso (P : X.Modules) (n : ℕ) :
    (m : ℕ) → tensorPow (tensorPow P n) m ≅ tensorPow P (n * m)
  | 0 => Iso.refl _
  | m + 1 => by
      simpa only [Nat.mul_succ, Nat.add_comm, tensorPow] using
        ((tensorFunctor X).mapIso ((Iso.refl (tensorPow P n)).prod (tensorPowMulIso P n m)) ≪≫
          tensorPowAddIso P n (n * m))

end Langlands.Scheme.Modules
