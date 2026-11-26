# Interpolation on one twist orbit at fixed central character

This is an internal, derived version of the interpolation step in
Henniart–Lemaire (2011), II.5.13, proof, printed p. 113. In this version the
interpolating function on the orbit is evaluation at a fixed test function.
The normalization of the twist operator matters: when a twist is equivalent
to the original representation, the equivalence can conjugate the two
operators only up to a scalar. The construction does not assume that this
scalar is one or take a quotient that forgets it.

## Orbit and interpolation

`IsUnramifiedTwistOf θ ρ π` means that `π` is equivalent to `twist ψ ρ` for an
unramified character `ψ` satisfying `ψ ∘ θ = ψ`. There is no condition on a
chosen operator. The twist is the Library representation `twist`.

`exists_twistOrbit_test_values` starts with a Hausdorff, locally compact,
totally disconnected topological group `G` with its Borel sigma-algebra and
a Haar measure `μ`. It assumes that every open subgroup contains a compact
open subgroup `K` with `θ⁻¹(K) ⊆ K` and that the group of unramified characters
trivial on the centre is finite. For an irreducible admissible `ρ`, its
central character `χ` and `A : ρ ≅ ρ ∘ θ`, this produces one test function `f`
with the following values:

- The twisted trace at `(ρ, A)` is `1`.
- The twisted trace at `(π, B)` is `0` whenever `π` is admissible, has central
  character `χ`, is inequivalent to `ρ`, and lies in the unramified twist orbit
  of `ρ` under `θ`-invariant characters, for any `B : π ≅ π ∘ θ`.

It says nothing about a representation outside that orbit. Neither `ρ` nor
`π` is required to be tempered. The universe of the carrier of `π` is
independent of that of `ρ`.

Proof. Form the finite type of `θ`-invariant unramified characters trivial
on the centre whose twists of `ρ` are not equivalent to `ρ`. Quotient this
finite type by equivalence of the twisted representations, and choose one
character representative in each class. These representation twists are
irreducible and admissible: use `isIrreducible_twist_iff`,
`isAdmissible_twist_iff`, and openness of the character kernel. Use the same
operator `A` on each twist, as `twistTwistedIntertwiner` permits. Adjoin the
actual pair `(ρ, A)` to the family, so this family is pairwise inequivalent.
By `exists_twistedDistribution_test_values`, one test function has value `1`
at the adjoined pair and `0` at the others.

If `π` satisfies the second condition, being equivalent to a twist with the
same central character forces the character of the twist to be trivial on
the centre (`center_le_ker_of_equiv_twist_same_centralCharacter`). Its twist
thus occurs in the finite quotient. Transport from the selected member of
that class using `exists_twistedDistribution_eq_smul_of_equiv`: the scalar
is immaterial to the value `0`. The value `1` was imposed directly with the
supplied operator `A`; no scalar transport is used there.

For positive-rank `GL_n(E)`, `finite_unramifiedCharacter_trivialCenter` supplies
the finiteness input, and `exists_regular_twistedDistribution_twist` supplies
regularity of evaluation at `f` as the unramified character varies on the
whole orbit. Those are separate lemmas. This module does not extend the
functional to the other representations needed in Paley–Wiener.

## Iterating the entrywise action

`entrywiseAut_iterate_eq_pow` identifies the `N`-fold iterate of the entrywise
field-algebra automorphism with the entrywise action of its `N`-th power.
The induction uses `entrywiseAut_one_apply` and `entrywiseAut_mul_apply`.
This lets a caller use `IsCyclicAlgebra.pow_eq_one` when applying the
finite-order compact open subgroup lemma.
