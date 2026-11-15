# Swapping two adjacent unlinked characters of a complex standard module

Lean module: `Langlands.Representation.Archimedean.ComplexStandardUnlinkedSwap`.

This module states one proposition, `Langlands.Archimedean.ComplexStandardUnlinkedSwapStatement`
(T5). It proves nothing. T5 says that two adjacent characters of a complex principal series may
be swapped, up to isomorphism of `(𝔤𝔩_n(ℂ), U(n))`-modules, whenever they are not linked. It is
a prerequisite shared by the two halves of the split in `ComplexLargeStandardIrreducibleSplit.md`:
the irreducibility criterion `ComplexStandardIrreducibleCriterionStatement` (Sp_C) and the
statement `ComplexLinkedLanglandsQuotientNotLargeStatement` (NL_C), where a linked pair that is not
adjacent must be moved next to each other past unlinked characters.

## Notation

As in `ComplexLargeStandardIrreducibleSplit.md`: `ComplexCharacterData` is the character
`z ↦ (z/|z|)^l |z|^{2t}` of `ℂˣ` with weight `l ∈ ℤ` and exponent `t ∈ ℂ`, `|z|` the usual
absolute value. For a list `ls` of `n` complex characters, `X(ls)` is the space
`kFiniteFunctions (complexStandardModule n ls) (unitaryCompact ℂ n)` of `U(n)`-finite functions
of the Library's standard module, with the `(𝔤𝔩_n(ℂ), U(n))`-action
`(complexStandardRep n ls, complexStandardLie n ls)` (right translation and right derivatives).
The `j`-th entry of `ls` is the character on the `j`-th diagonal entry of the Borel subgroup of
upper triangular matrices, so `X(ls)` is the Harish-Chandra module of Tadić's
`λ = δ₁ × ⋯ × δ_n` for `ls = [δ₁, …, δ_n]` (see `ComplexGenericParameterReduction.md` for the
passage from the Library's left-equivariant functions to the usual induced picture).

`IsComplexLinked d e` (module `ComplexLargeStandardIrreducibleSplit`) says that there are integers
`p, q` with `0 < p * q`, `(t_d + l_d/2) - (t_e + l_e/2) = p` and `(t_d - l_d/2) - (t_e - l_e/2) = q`.
It is Tadić's linkage relation (2009, p. 11) and is symmetric in `d`, `e`.

`IsComplexStandardIntertwining n ρ π ls A` (module `ComplexGenericParameterReduction`) says that
the linear map `A` out of `X(ls)` carries right translation by `k ∈ U(n)` and the right
derivative along `X ∈ 𝔤𝔩_n(ℂ)` on `X(ls)` to `ρ(k)` and `π(1 ⊗ X)`.

## The statement

`ComplexStandardUnlinkedSwapStatement`: for every `n : ℕ`, all lists `pre`, `post` of complex
characters and all complex characters `d`, `e` with `(pre ++ d :: e :: post).length = n` and
`¬ IsComplexLinked d e`, there is a linear map

  `T : X(pre ++ e :: d :: post) →ₗ[ℂ] X(pre ++ d :: e :: post)`

that is bijective (`Function.Bijective T`) and satisfies
`IsComplexStandardIntertwining n (complexStandardRep n (pre ++ d :: e :: post))
(complexStandardLie n (pre ++ d :: e :: post)) (pre ++ e :: d :: post) T`.

In words: `X(…, d, e, …)` and `X(…, e, d, …)` are isomorphic `(𝔤, K)`-modules when `d` and `e`
are not linked. No condition is imposed on the real parts of `t_d`, `t_e` (equal real parts are
allowed), on the other characters, or on the order of the list. The case `d = e` is included
(`d` is never linked to itself) and is trivial. The conclusion has the same shape as that of
`ComplexStandardPermutationStatement` (module `ComplexStandardSurjectionInjectiveReduction`),
which allows any rearrangement but assumes that `X(ds)` is irreducible; T5 assumes only that the
two swapped characters are not linked, and the whole principal series may be reducible.

## Why T5 is true

Write `ls = pre ++ d :: e :: post` and `σ = δ₁ × ⋯ × δ_k` for `pre = [δ₁, …, δ_k]`, `τ` likewise
for `post` (an empty product is the trivial representation of `GL_0`).

1. `δ_d × δ_e` is an irreducible Harish-Chandra module of `GL_2(ℂ)`: by definition (Tadić 2009,
   p. 11) `δ_d` and `δ_e` are linked if and only if `δ_d × δ_e` is reducible, and Tadić states
   (p. 11) that this happens if and only if `δ_d δ_e⁻¹ = γ(p, q)`, `z ↦ z^p z̄^q`, with `p, q ∈ ℤ`
   and `p q > 0`, which is `IsComplexLinked d e`.
2. If `σ₁ × σ₂` is irreducible, then `σ₁ × σ₂ ≅ σ₂ × σ₁` (Tadić 2009, p. 6, the sentence after
   (1-2), a consequence of Vogan's result on induction from associated parabolic subgroups). So
   `δ_d × δ_e ≅ δ_e × δ_d`.
3. Parabolic induction is a functor, so the isomorphism of step 2 induces an isomorphism
   `σ × (δ_d × δ_e) × τ ≅ σ × (δ_e × δ_d) × τ` of Harish-Chandra modules of `GL_n(ℂ)`. Induction
   in stages, (1-1) of Tadić 2009 (pp. 5–6), identifies the two sides with
   `δ₁ × ⋯ × δ_k × δ_d × δ_e × ⋯` and `δ₁ × ⋯ × δ_k × δ_e × δ_d × ⋯`, that is, with `X(ls)` and
   `X(pre ++ e :: d :: post)`.

A proof in Lean may follow another route: for example, a nonzero intertwining map between the two
principal series obtained from a rank-one Jacquet functional and Frobenius reciprocity, together
with a proof that it is injective when `d`, `e` are not linked and the equality of the finite
`U(n)`-multiplicities of the two sides.

## Provenance

Derived. T5 combines three facts recorded in Tadić 2009: the definition and description of linked
characters (p. 11), the isomorphism `σ₁ × σ₂ ≅ σ₂ × σ₁` for irreducible `σ₁ × σ₂` (p. 6), and
induction in stages (1-1) (pp. 5–6), with functoriality of parabolic induction. The statement
itself, with the swap at an arbitrary position of a list, is internal; it is formulated for the
Library's `complexStandardModule` and its `U(n)`-finite part, whose identification with the
classical principal series is described in `ComplexGenericParameterReduction.md` and
`ComplexLargeStandardIrreducibleSplit.md`.

Source:

* M. Tadić, `GL(n, ℂ)^` and `GL(n, ℝ)^`, in: Automorphic Forms and L-functions II. Local
  Aspects, Contemp. Math. 489, Amer. Math. Soc., 2009, pp. 285–313
  (`tadic-2009-gl-n-c-gl-n-r-unitary-duals`, author's PDF; PDF page = page number of the
  running head). §1: parabolic induction `σ₁ × σ₂` and induction in stages (1-1) (p. 5, with the
  justification on p. 6); (1-2) and the sentence after it, "if `σ₁ × σ₂ ∈ Irr`, then
  `σ₁ × σ₂ ≅ σ₂ × σ₁`" (p. 6). §3: the parametrizations `δ(β, n)`, `γ(x, y)` and linked
  characters (p. 11).
