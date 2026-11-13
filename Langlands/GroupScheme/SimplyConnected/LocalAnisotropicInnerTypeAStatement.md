# Anisotropic absolutely almost-simple local groups have inner type A

Author: Worker 160.

This module states two local arithmetic facts behind Bruhat–Tits (1967),
Proposition 6. They are written on the published actual Tits-index data
`TitsIndexData G`. The module supplies no proof. These statements are
prerequisites of the published target
`Langlands.GroupScheme.LocalAnisotropicSimplyConnectedClassificationStatement`
(Task 5636). That target also needs the identification
`Langlands.GroupScheme.InnerTypeANormOneStatement` of inner type `A_n`
with a reduced-norm-one group, which these statements do not contain.

## Common hypotheses

Both statements quantify over the following data:

- `K : Type u` with `[Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]`, so `K` is a nonarchimedean local field
  of any characteristic. Residue characteristic 2 and characteristic 2
  are included.
- A group scheme `G` over `Spec K` with `[IsAffineHom G.X.hom]` and
  `[LocallyOfFiniteType G.X.hom]`. These are the instances required by
  the published index interface. The semisimple groups in question
  satisfy both of them, so they add no mathematical restriction.
- An arbitrary actual index datum `d : TitsIndexData G`. The statements
  hold for every such datum. Neither statement asserts that a datum
  exists; that is `TitsIndexExistenceStatement`.

`IsAbsolutelyAlmostSimple G` is the published absolute almost-simplicity
predicate. It includes semisimplicity and noncommutativity. Its finite-center
convention is the source's convention for absolutely almost simple groups.
`IsAnisotropic G` means `splitRank G = 0`, so `G` contains no nontrivial split
subtorus. This is the source's notion of a `K`-anisotropic reductive group.

Type `A_n` is written as follows:

`∃ e : d.Vertex ≃ Fin n, ∀ a b, d.cartan a b = CartanMatrix.A n (e a) (e b)`.

The bijection `e` numbers every actual simple vertex. It carries every
actual integral Cartan pairing to the entry of Mathlib's matrix
`CartanMatrix.A n`. That matrix has `n` rows and columns, diagonal entries
2, entry minus 1 between consecutive indices and 0 elsewhere. So `n` is
the absolute rank and the diagram is `A_n`. The imported Mathlib docstring
calls this matrix `A_{n-1}`; the convention here follows its `Fin n`
indices and formula, as in `TitsIndexData.HasInnerTypeA`. This is the same
type condition as the second conjunct of `TitsIndexData.HasInnerTypeA n`.

## `LocalAnisotropicTypeAStatement`

If `G` is absolutely almost simple and anisotropic, then
`∃ n : ℕ, 0 < n ∧` type `A_n` holds for `d`. The conclusion says nothing
about the star action. Simple connectedness is not assumed.

## `LocalAnisotropicTypeAInnerStatement`

Fix also `n : ℕ`. Assume that `G` is simply connected
(`IsSimplyConnected G`), absolutely almost simple and anisotropic, and that
type `A_n` holds for `d`. Then `d.star σ a = a` for every
`σ : SeparableClosure K ≃ₐ[K] SeparableClosure K` and every vertex
`a : d.Vertex`. So the actual star action of the full absolute Galois group
on the simple vertices is trivial. By Tits's definition (Tits 1966, §2.3) this
means that `G` is of inner type. In contrapositive form: a simply connected
absolutely almost-simple group of outer type `A_n` over `K` is isotropic. If
`n ≤ 1`, the diagram has at most one vertex, so the conclusion holds
trivially. The content of the statement is the case `n ≥ 2`.

## `LocalAnisotropicInnerTypeAStatement`

This is the conjunction
`LocalAnisotropicTypeAStatement.{u} ∧ LocalAnisotropicTypeAInnerStatement.{u}`.
Applied to one `G` and `d`, the two conjuncts yield
`d.HasInnerTypeA n` for some `n`. That is exactly the hypothesis of
`InnerTypeANormOneStatement`.

## Sources

T. Kaletha and G. Prasad, *Bruhat–Tits Theory: A New Approach*, Cambridge
University Press, 2023, registered as
`kaletha-prasad-2023-bruhat-tits-new-approach`:

- Theorem 10.3.1, printed pp. 391–392 / PDF pp. 422–423, in Chapter 10.
  Its standing hypothesis is that the residue field has dimension at most
  one. The statement: an absolutely almost simple anisotropic `k`-group
  splits over the maximal unramified extension and is of type `A_n`. The
  proof goes through the building: `B(G)` is a single point, and `Γ` acts
  transitively on the vertices of a `Γ`-stable chamber, so it acts
  transitively on the affine Dynkin diagram. The book attributes the
  result to [BT87a, 4.4–4.5]. `LocalAnisotropicTypeAStatement` is its
  specialization to nonarchimedean local fields, whose residue fields are
  finite. It keeps only the type conclusion.
- The paragraph after Remark 10.3.2, printed pp. 392–393 / PDF
  pp. 423–424. Over a nonarchimedean local field every absolutely almost
  simple anisotropic group is of inner type `A_n`. The book attributes this
  to Kneser in characteristic zero and to Bruhat and Tits in general. Given
  Theorem 10.3.1, it reduces the claim to the isotropy of every simply
  connected absolutely almost simple group of outer type `A_n` with
  `n ≥ 2`. It proves that isotropy in two ways. The first writes such a
  group as `SU(h)` for a hermitian form over a quadratic Galois extension
  and uses the isotropy of quadratic forms in more than four variables. The
  second uses Corollary 10.6.2 and §10.7. `LocalAnisotropicTypeAInnerStatement`
  is this isotropy claim in the contrapositive form above.

The authors' corrections (version of 1 November 2024, registered as
`kaletha-prasad-2024-corrections`) contain no entry for §10.3.

F. Bruhat and J. Tits, *Groupes algébriques simples sur un corps local*, in
T. A. Springer (ed.), *Proceedings of a Conference on Local Fields*
(Driebergen 1966), Springer, 1967, pp. 23–36, registered as
`springer-1967-conference-local-fields`. §8, Proposition 6, printed p. 35 /
PDF p. 41, concerns a complete discretely valued field with perfect residue
field `k`, where groups are simple and simply connected (introduction,
printed p. 23 / PDF p. 29). It says: if `dim k ≤ 1` and `G` is anisotropic,
then `G` is of type `A_n`. If moreover the Galois group of the maximal
unramified extension is commutative, then `G` is an inner form. For a local
field the residue field is finite, so `dim k ≤ 1`, and that Galois group is
procyclic and hence commutative. The two statements here are these two
conclusions, specialized to local fields. The source's final
identification with reduced-norm-one elements of a division algebra is not
part of this module.

Two points of scope:

- The type conclusion of Theorem 10.3.1 does not need simple connectedness,
  so `LocalAnisotropicTypeAStatement` omits it.
- The inner-type statement assumes simple connectedness, as Kaletha–Prasad's
  isotropy argument and Bruhat–Tits's standing convention do. Both type and
  inner/outer type are invariant under central isogeny, so this hypothesis
  only restricts the statement to the case the sources prove.

The splitting over the maximal unramified extension, also asserted in
Theorem 10.3.1, is not stated here.

Over arbitrary complete discretely valued fields with residue field of
dimension at most one, the inner-type conclusion can fail. Kaletha–Prasad,
Example 10.3.3, printed p. 393 / PDF p. 424, gives an anisotropic group of
outer type `A_{r-1}` over `C(x)((t))`. The local-field hypothesis is
therefore essential for the second statement.
