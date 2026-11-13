import Langlands.GroupScheme.Rational.QuasiSplitInnerForm
import Langlands.GroupScheme.Symplectic.Basic

/-! # Inner forms of `Sp_{2n}` are symplectic groups of antihermitian division forms:
statement -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Let `K` be a field, `G` a group scheme over `K` and `n ≥ 2`. Suppose `G` is presented as an
inner form of a quasi-split group whose model is isomorphic to the standard symplectic group
scheme `Sp_{2n}` over `K`. Then there are a central division `K`-algebra `D` of degree
`degree`, with `m * degree = 2 * n`, an involution of the first kind `σ` of `D` whose symmetric
space has dimension `degree * (degree + 1) / 2`, and an invertible trace-valued
`σ`-antihermitian Gram matrix `H ∈ M_m(D)`, such that `G` is isomorphic to the symplectic group
`σ.symplecticGroup H`. -/
def SymplecticInnerFormAntihermitianStatement : Prop :=
  ∀ (K : Type u) [Field K] (G : GroupScheme (Spec (CommRingCat.of K))) (n : ℕ)
    (q : QuasiSplitInnerForm G),
    2 ≤ n → Nonempty (q.model ≅ Symplectic.groupScheme K n) →
      ∃ (degree m : ℕ) (_ : NeZero m)
        (D : Type u) (_ : DivisionRing D) (_ : Algebra K D)
        (_ : Algebra.IsCentral K D) (_ : FiniteDimensional K D),
        0 < degree ∧ m * degree = 2 * n ∧
        Module.finrank K D = degree ^ 2 ∧
          ∃ σ : Quaternionic.FirstKindInvolution K D,
            Module.finrank K σ.symmetricSubspace = degree * (degree + 1) / 2 ∧
              ∃ H : Matrix (Fin m) (Fin m) D,
                σ.IsAntihermitian H ∧ IsUnit H ∧ Nonempty (G ≅ σ.symplecticGroup H)

end Langlands.GroupScheme
