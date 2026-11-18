# Schur's lemma for unitary representations and irreducible subspaces of Hilbert sums

`Langlands.TraceFormula.UnitarySchurHilbertSumStatement` is a Prop-valued definition
with independent universe parameters `u` and `v`. The module imports
`Mathlib.Analysis.InnerProductSpace.l2Space`.

## Setting

- `E : Type u` is a complex Hilbert space with instances `NormedAddCommGroup E`,
  `InnerProductSpace ℂ E`, and `CompleteSpace E`.
- `M : Type v` is an abstract group. The action is a monoid homomorphism
  `ρ : M →* (E →L[ℂ] E)` into the bounded complex-linear endomorphisms of `E`.
  The hypothesis `∀ a x, ‖ρ a x‖ = ‖x‖` makes each `ρ a` an isometry.
  Its inverse is `ρ a⁻¹`, so each operator is unitary.
- A submodule `R : Submodule ℂ E` is closed when `IsClosed (R : Set E)` holds.
  Invariance means `∀ a, ∀ x ∈ R, ρ a x ∈ R`. The irreducibility criterion
  for a closed invariant `R` is that every closed invariant submodule `R' ≤ R`
  is `⊥` or `R`.

## Statement

1. **Schur's lemma.** For every `E`, `M`, and `ρ` as above, assume that every
   closed invariant submodule of `E` is `⊥` or `⊤`. Every bounded operator
   `B : E →L[ℂ] E` satisfying `B ∘L ρ a = ρ a ∘L B` for all `a : M` then
   equals `c • ContinuousLinearMap.id ℂ E` for some `c : ℂ`.

2. **Irreducible subspaces of a Hilbert sum.** For every `E`, `M`, and `ρ`
   as above, let `A : Set (Submodule ℂ E)` have the instance
   `[∀ P : A, CompleteSpace (P : Submodule ℂ E)]`. Suppose each `P ∈ A` is
   invariant and satisfies the irreducibility criterion. Completeness in the
   subspace norm makes each `P` closed in `E`. Assume
   `IsHilbertSum ℂ (fun P : A => (P : Submodule ℂ E)) (fun P => (P : Submodule ℂ E).subtypeₗᵢ)`.
   The inclusions `subtypeₗᵢ` give a pairwise orthogonal family whose
   canonical isometry from the external Hilbert sum to `E` is surjective.
   Equivalently, the algebraic sum of these orthogonal subspaces is dense in `E`.

   Let `Q : Submodule ℂ E` be nonzero (`Q ≠ ⊥`), closed, invariant with
   proof `hQ`, and irreducible. There exist `P ∈ A` and a complex-linear
   isometric equivalence `U : Q ≃ₗᵢ[ℂ] P` satisfying
   `(U ⟨ρ a x, hQ a x x.2⟩ : E) = ρ a (U x)` for every `a : M` and
   `x : Q`. The subtype term `⟨ρ a x, hQ a x x.2⟩` is the restricted
   action on `Q`. Both sides of the intertwining equation are read in `E`.
   The irreducibility criterion permits zero summands, and the chosen
   `P` is nonzero because it is equivalent to `Q`.

## Source and proof sketch

Clause 1 is the implication from irreducibility to a scalar commutant in
Folland, *A Course in Abstract Harmonic Analysis*, 2nd ed. (CRC Press, 2015),
§3.1, Theorem 3.5(a), printed p. 77. On printed p. 73 (one-based PDF p. 86),
Folland defines a unitary representation of a locally compact group on a
nonzero Hilbert space and requires continuity in the strong operator topology.
Page 75 defines the commutant, intertwiners, unitary equivalence, and invariant
subspaces. The argument uses only the group law and unitarity, so it applies
to abstract groups. For `E = 0`, the scalar conclusion holds with `c = 0`.

For nonzero `E`, the commutant is closed under taking adjoints because
`(ρ a)⋆ = ρ a⁻¹`. Decompose a commuting operator into its self-adjoint real
and imaginary parts. If a self-adjoint part `D` has two distinct spectral
points `s` and `t`, choose continuous real functions `f` and `g` with
disjoint supports, `f(s) = 1`, and `g(t) = 1`. Continuous functional calculus
gives nonzero operators `f(D)` and `g(D)` in the commutant with
`f(D) g(D) = 0`. The closure of the range of `g(D)` is a nonzero closed
invariant subspace contained in the proper kernel of `f(D)`, contradicting
irreducibility. Its spectrum is nonempty since `E` is nonzero, so it is a
singleton `{c}`. For a self-adjoint operator the spectral radius equals the
norm, so `D - c • id` is zero. This gives the scalar conclusion for the
original operator.

Clause 2 is derived content. It combines the Hilbert sum with Folland's
Propositions 3.1 and 3.4 (printed pp. 76–77) and the normalization argument in
Theorem 3.5(b) (printed p. 77). Choose a nonzero vector of `Q`. Some projection
`p_P` onto a summand `P ∈ A` is nonzero on it, since the summands have dense
span. The restriction `T = p_P ∘ ι_Q : Q → P`, with `ι_Q` the inclusion,
intertwines because both `P` and `Pᗮ` are invariant. Then `T⋆ T` commutes
with the restricted unitary action on `Q`. Clause 1 on `Q` gives
`T⋆ T = c • id_Q`. Evaluating `‖Tx‖² = c ‖x‖²` at any `x` with `Tx ≠ 0`
shows that `c` is real and positive. The isometry `c^(-1/2) • T` has
closed range by completeness of `Q`. That range is nonzero and invariant,
so irreducibility of `P` makes the isometry surjective.

## Cuspidal application

For `GL_n`, let `S` be the Library's full almost-everywhere cuspidal subspace
of `L²([GL_n])` on the positive-central rational quotient.
`fullAEL2Cuspidal_completeSpace` supplies completeness, and
`norm_fullAEL2CuspidalBoundedRightAction` supplies the isometry hypothesis
for the action `πc = fullAEL2CuspidalBoundedRightAction`.

Given a Hilbert-sum decomposition of `S` as in clause 2, that clause gives
an intertwining isometric equivalence from any nonzero irreducible closed
invariant `Q` onto some `P ∈ A`. The summand `P` is closed by completeness
and nonzero by equivalence with `Q`. The Library's multiplicity-one
proposition uses the same closedness, invariance, irreducibility, and
intertwining conditions. Instantiating it with `Q` as the source and `P`
as the target gives `Q = P`. [Cuspidal multiplicity one for GL_n](../Automorphic/GeneralLinearCuspidalMultiplicityOneStatement.md)

For the twisted spectral expansion of Task 7698, suppose the twist `I_Θ`
restricts to a unitary on `S` and intertwines `πc` with its twist by the
group automorphism `Θ`. The image `I_Θ(P)` of a nonzero summand is then
nonzero, closed, invariant, and irreducible. Clause 2 and multiplicity one
give `I_Θ(P) ∈ A`, so the choice `τ(P) = I_Θ(P)` provides the required
map on summands. If `A` contains the zero summand, its image is itself.
