import Langlands.GroupScheme.Quaternionic.CocharacterWeightSpace
import Langlands.GroupScheme.Rational.SplitTorus

/-!
# Weights of a maximal split torus of `O(q)⁰` on `D^n`

This unproved statement describes the weights of every maximal split torus of the connected
isometry group of a nondegenerate `σ`-quadratic form over a central division algebra with
an involution of the first kind of type `1`: they are `±χ_1, …, ±χ_r`, each with `D`-multiplicity one,
and `0` with the remaining multiplicity, where `r` is the Witt index and the `χ_k` form a
basis of the rational character space.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme.Quaternionic

/-- Let `D` be a finite-dimensional central division algebra of degree `degree` over a
field `K`, `σ` an involution of the first kind of `D` whose symmetric subspace has dimension
`degree * (degree + 1) / 2` (Tits type `1`), and `q` a nondegenerate `σ`-quadratic form on `D^n`
whose isometry group `O(q)` is smooth. Write `r` for the Witt index of `q`. For every
maximal split torus `i : S ⟶ O(q)⁰` there are characters `χ_1, …, χ_r` of `S`, linearly
independent and detecting every cocharacter, such that for every cocharacter `ν` of `S`
and every integer `c` the weight space of weight `c` of `ν` acting on `D^n` through
`S ⟶ O(q)⁰ ⟶ O(q)` has `D`-dimension the number of pairs `(k, s)`, `s = ±1`, with
`s ⟨χ_k, ν⟩ = c`, plus `n - 2r` when `c = 0`. -/
def IsometryMaximalSplitTorusWeightsStatement : Prop :=
  ∀ (K D : Type u) [Field K] [DivisionRing D] [Algebra K D] [Algebra.IsCentral K D]
    [FiniteDimensional K D] (degree : ℕ), Module.finrank K D = degree ^ 2 →
    ∀ (σ : FirstKindInvolution K D),
    Module.finrank K σ.symmetricSubspace = degree * (degree + 1) / 2 →
    ∀ (n : Type) [Fintype n] [DecidableEq n] (q : σ.QuadraticForms n)
    [Smooth (σ.isometryGroup q).X.hom],
    σ.IsNondegenerateQuadratic q →
    ∀ (S : CommGroupScheme (Spec (CommRingCat.of K)))
      (i : S.toGrp ⟶ σ.connectedIsometryGroup q),
      IsMaximalSplitTorus i →
      ∃ χ : Fin (σ.quadraticWittIndex q) → characterLattice S,
        LinearIndependent ℤ χ ∧
        (∀ ν : cocharacterLattice S, (∀ k, latticePairing S (χ k) ν = 0) → ν = 0) ∧
        ∀ (ν : cocharacterLattice S) (c : ℤ),
          Module.finrank D (σ.cocharacterWeightSpace q
              (CommGroupScheme.groupHom ν ≫ i ≫ identityComponentι (σ.isometryGroup q)) c) =
            Nat.card {p : Fin (σ.quadraticWittIndex q) × ℤˣ //
                (p.2 : ℤ) * latticePairing S (χ p.1) ν = c} +
              if c = 0 then Fintype.card n - 2 * σ.quadraticWittIndex q else 0

end Langlands.GroupScheme.Quaternionic
