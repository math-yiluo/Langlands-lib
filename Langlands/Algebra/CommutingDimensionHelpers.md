# Algebraic helpers for the commuting-endomorphism dimension estimate

This module supports Bernstein–Zelevinsky (1976),
Lemma 4.10, without claiming the general estimate. The source is registered
as `bernstein-zelevinsky-1976-representations-gln`; the statement is on
printed p.39 and its proof in §4.12 on printed p.40.

The helpers hold over any field. With no generators, the generated algebra
is the scalar subalgebra, of dimension at most one, including the zero
vector space. With one generator, the powers below the degree of its
minimal polynomial span the generated algebra. The minimal polynomial
divides the characteristic polynomial, whose degree is the vector-space
dimension. This proves the singleton dimension bound, and squaring gives
the proposed natural-power estimate for one generator. These deductions
are implemented using Mathlib's polynomial and finite-dimensional results.

The restriction helper assumes a subspace `L` whose images under a
commuting subalgebra `C` span `V`. If an element `c` of `C` vanishes on `L`,
commutativity makes it vanish on every `d(x)` with `d` in `C` and `x` in
`L`. Its kernel therefore contains the spanning subspace and is all of
`V`. This proves that the linear restriction map `C → Hom(L,V)` is
injective. Taking dimensions gives `dim C ≤ dim L * dim V`, the first
dimension inequality in the source's nilpotent argument. Injectivity
itself does not require finite dimension.

`span_action_of_sup_radical_eq_top` supplies the generating hypothesis
when `L + J·V = V` and the ideal `J` is contained in the nilradical of `C`.
View `V` as a finite module over `C` and put `N = span_C L`. Then
`N + J·V = V`; the nilradical is contained in the Jacobson radical, so
Mathlib's Nakayama lemma gives `N = V`. The scalar-tower span identity
identifies `N`, restricted to `K`, with the linear span of all `c(x)`.
This replaces the source's descending-power argument with Nakayama.

`dimension_le_radical_codimension` chooses a vector-space complement
to `J·V` and combines these results with the complement dimension formula.
It gives `dim C ≤ (dim V - dim J·V) * dim V`.

`restrictionAlgHom` sends an algebra of endomorphisms to its action on an
invariant subspace `W`. If `f(V) ⊆ W`, an element whose restriction to `W`
vanishes has zero product with `f`, by commutativity. Kernel containment
and rank-nullity therefore give `dim(f C) ≤ dim(C|W)`, implemented as
`multiplication_dimension_le_restriction`.

`dimension_adjoin_insert` works in an abstract finite-dimensional
commutative algebra `E`. If adjoining `f` to a subalgebra `B` gives `E`,
then `E = B + f E`: the latter subspace contains one, contains the
generators, and is closed under multiplication by explicit expansion.
The dimension of a sum gives `dim E ≤ dim B + dim(f E)`.

Worker 307 authored these internal supporting deductions. They provide
the algebraic inequalities used by the nilpotent induction, but do not themselves assemble that induction or the primary-decomposition
step for arbitrary commuting generators.
