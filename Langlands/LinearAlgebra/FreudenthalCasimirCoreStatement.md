# Freudenthal's recursion for a weight-graded Lie algebra of endomorphisms

Module `Langlands.LinearAlgebra.FreudenthalCasimirCoreStatement`, namespace
`Langlands.LinearAlgebra`.

`FreudenthalCasimirCoreStatement` is an unproved proposition (a `Prop`-valued
definition), universe-polymorphic in six universes. It is an abstract,
coordinate-level form of Freudenthal's multiplicity formula (Humphreys,
*Introduction to Lie Algebras and Representation Theory*, GTM 9, §22.3), stated
for a Lie algebra of endomorphisms graded by a character lattice. It is an
internal intermediate statement of this project: the group-scheme form
`FreudenthalMultiplicityStatement` follows from it by taking for `g` the
tangent Lie algebra of a pair of representations, graded by the weights of a
split maximal torus (`Langlands.GroupScheme.Rational.FreudenthalMultiplicityProof`). The Lie bracket on `Module.End k U` is the commutator
(`LieRing.ofAssociativeRing`, a local instance).

## Data

For every

- field `k` of characteristic zero;
- finite-dimensional `k`-space `U`;
- torsion-free additive group `X` (characters) and additive group `Y`
  (cocharacters) with a basis `yb : Basis ι ℤ Y`, `ι` finite with decidable
  equality;
- finite type `J` (root indices);
- pairing `P : X →ₗ[ℤ] Y →ₗ[ℤ] ℤ`, written `⟨χ, y⟩`;
- family of subspaces `W : X → Submodule k U` (weight spaces);
- Lie subalgebra `g` of `Module.End k U`;
- map `root : J → X`, subspace `V` of `U`, weight `lam : X`, and predicate
  `pos : J → Prop` (selecting the positive roots);

write `g_χ = g ⊓ WeightGraded.shift W χ` for the endomorphisms in `g` mapping
every `W μ` into `W (μ + χ)`, and say that `x` acts by the cocharacter `y` if
`x u = ⟨μ, y⟩ u` for all `u ∈ W μ` and all `μ`
(`WeightGraded.IsScalarOn W (fun μ => ⟨μ, y⟩) x`).

## Hypotheses (in order)

1. the `W μ` are independent (`iSupIndep W`);
2. they span `U`;
3. `g ≤ ⨆ χ, g_χ`;
4. for every `y : Y` some element of `g` acts by `y`;
5. `g_0` is contained in the span of the elements acting by cocharacters;
6. `g_χ = 0` for `χ ≠ 0` not of the form `root j`;
7. `dim g_{root j} = 1` for every `j`;
8. every nonzero `y` pairs nontrivially with some `μ` having `W μ ≠ 0`;
9. `root j ≠ 0` for every `j`;
10. `root` is injective;
11. for every `j` there is `j'` with `root j' = -root j`;
12. every Lie ideal of `g` all of whose elements are nilpotent endomorphisms
    is zero;
13. `V` is `g`-stable;
14. every nonzero `g`-stable subspace `K ≤ V` equals `V`;
15. `dim (V ⊓ W lam) = 1`;
16. `V ⊓ W (lam + root j) = 0` whenever `pos j`;
17. `V ⊓ W (lam - root j) = 0` whenever `¬ pos j`.

## Conclusion

Let `F = GramDual.form P yb m` with `m ν = dim W ν` (the form of
`Langlands.LinearAlgebra.GramDualForm`), and `n μ = dim (V ⊓ W μ)`. For every
`μ : X`,

`(F(lam, lam) + ∑ᶠ_{j, pos j} F(lam, root j) - F(μ, μ)) · n(μ)
  = ∑ᶠ_{j : J} ∑ᶠ_{i : ℕ} F(μ + (i + 1) root j, root j) · n(μ + (i + 1) root j)`

in `ℚ`.

## Relation to Freudenthal's formula

In Humphreys' notation, with `(·,·)` the form `F`, `Φ` the roots and `Φ⁺` the
positive ones, the scalar by which the Casimir element acts on `V` is
`(lam, lam) + ∑_{α ∈ Φ⁺} (lam, α) = (lam + δ, lam + δ) - (δ, δ)` where
`2δ = ∑_{α ∈ Φ⁺} α`. The right side sums over all roots, not only positive
ones, and starts at `j = 1`; Humphreys' form (§22.3) is obtained by pairing the
terms of `α` and `-α`. The form `F` here is the dual of the trace form of `U`
restricted to the torus part of `g`, rather than of the Killing form; the
formula holds for any such invariant nondegenerate form, which is how Humphreys
derives it (§22.2–22.3).
