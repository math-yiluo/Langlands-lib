# Fibrewise detection of isogenies

`Langlands.GroupScheme.FiberwiseIsogenyStatement` is a proposition-valued
definition in `Langlands.AbelianScheme.FiberwiseIsogenyStatement`. For every
scheme `S`, group objects `G H : Grp (Over S)` with smooth and proper structure
maps, and homomorphism `f : G ⟶ H`, it states that `f` is an isogeny if its
pullback to every residue-field point of `S` is an isogeny.

Here an isogeny has exactly the published convention
`Langlands.GroupScheme.IsIsogeny`: the underlying scheme morphism
`f.hom.hom.left` is finite, flat, and surjective. The fibre homomorphism is the
actual functorial pullback
`((Over.pullback (S.fromSpecResidueField s)).mapGrp.map f)`.
Its source and target are the group schemes over `Spec κ(s)` obtained by base
change. The quantifier ranges over all points `s : S`, not merely closed or
geometric points; the hypothesis concerns scheme morphisms, not just maps on
rational points or an abstract indexed family.

The statement has one universe parameter and no noetherian, quasicompact,
field, constant-dimension, connectedness, commutativity, or invertibility
hypothesis on the base or the group schemes. Both structure maps are assumed
smooth and proper, although some of these hypotheses can be weakened in the
component arguments. In particular, setting `H = G` includes endomorphisms.
No proof of the criterion is supplied here, and the criterion is not installed
as an assumption, axiom, or field in a new structure.

## Componentwise mathematical justification

Write `X` and `Y` for the underlying schemes of `G` and `H`.
The following explains the mathematical provenance of the target; these
arguments remain a separate Lean proof obligation.

**Finite.** The map `f : X → Y` is proper because `X → S` is proper and
`Y → S` is separated. This is Stacks tag
[01W6](https://stacks.math.columbia.edu/tag/01W6), Lemma 29.42.7(2).
For `y ∈ Y`, let `s` be its image in `S`. The point `y` lifts uniquely to a
point `y_s` of `Y_s`, using the identification of the residue-field fibre's
underlying space with the topological fibre (tag
[01K1](https://stacks.math.columbia.edu/tag/01K1), Lemma 26.18.5).
The same identification on `X` identifies the points of `f⁻¹(y)` with the
points of `f_s⁻¹(y_s)`. The latter set is finite since `f_s` is finite.
Thus `f` is proper with finite fibres, and hence finite by tag
[02LS](https://stacks.math.columbia.edu/tag/02LS), Lemma 37.44.1.
Equivalently, properness supplies finite type, finite fibres give local
quasi-finiteness, and proper plus locally quasi-finite gives finite.

**Flat.** Smoothness makes `X → S` flat and locally of finite presentation;
it also makes `Y → S` locally of finite type. Each `f_s` is flat by the
fibrewise isogeny hypothesis. The finite-presentation fibrewise flatness
criterion, Stacks tag
[039E](https://stacks.math.columbia.edu/tag/039E), Lemma 37.16.4, then makes
`f` flat over the arbitrary base `S`. This is the specialization to the
structure sheaf of the criterion in Section 37.16, Theorem 37.16.2.
In particular, this application does not require noetherian local rings.

**Surjective.** Given `y ∈ Y`, use its lift `y_s ∈ Y_s` as above.
Surjectivity of `f_s` provides `x_s ∈ X_s` above `y_s`. Its image in `X`
maps to `y` by the pullback square. Thus `f` is surjective. This uses
scheme-theoretic base fibres and their underlying points, without claiming
that an arbitrary scheme fibre product is a fibre product of sets.

The group operations play no role in these three geometric arguments; the
group-object formulation is the interface required by multiplication
homomorphisms and the published relative isogeny predicate.

## Original-source scope and provenance

The target is a **derived** general criterion, not a verbatim statement from
Milne. Milne, *Abelian Varieties* (1986 article, author revision 2022),
Section 20, Proposition 20.7, printed/PDF page 44, uses the same flatness and
proper-with-finite-fibres route for multiplication on an abelian scheme.
Section 20 begins on page 42 with the arbitrary-base definition of an abelian
scheme. The present statement isolates the geometric detection step and
does not assert multiplication, its degree, or an étaleness criterion.

Milne cites SGA 1, Exposé IV, Corollary 5.9 for flatness. We checked that
original in the recomposed edition: printed page 81 (original pagination
99–100 in the margin), PDF page 97. It explicitly assumes noetherian local
rings and a finite module. Consequently, that corollary alone is not the
arbitrary-base justification here. The finite-presentation version in the
Stacks Project, whose hypotheses follow from smoothness as explained above,
supplies the required scope.

The registered sources are:

- `milne-abelian-varieties-1986-author-2022`, Section 20, pages 42 and 44;
  SHA256 `bffdf81c57c77420b5454b31270007989d12f332abea62424be15c424079fc7c`.
- `sga1-arxiv-math-0206203v2`, Exposé IV, Corollary 5.9, recomposed
  page 81, PDF page 97; used to delimit the cited noetherian criterion;
  SHA256 `8e64218d356456c534eebf996940f0f957e43b54f1a080241debe12cbaf60d3c`.
- `stacks-fiberwise-isogeny-2026-10-22`, retained HTML files `01W6.html`,
  `01K1.html`, `02LS.html`, `039E.html`, and `039A.html`, at the tags and
  results cited above; folder SHA256
  `db82f1556e926672cc2278329e279f7fcaceb540c23e323a7c266a6a6b1f0dca`.

## Proof interface

A later proof must prove exactly
`Langlands.GroupScheme.FiberwiseIsogenyStatement` in the published Library,
without changing this statement or its imports. The finite, flat, and
surjective conclusions must concern the actual underlying morphism, with
the stated pullbacks. In the pinned Mathlib, useful starting points for
finiteness are `IsProper.of_comp`,
`LocallyQuasiFinite.of_finite_preimage_singleton`, and
`IsFinite.iff_isProper_and_locallyQuasiFinite`. The relative fibrewise
flatness step requires its own justified infrastructure if no existing
theorem supplies it. Positive multiplication over fields and integer sign
reduction belong to separate work.
