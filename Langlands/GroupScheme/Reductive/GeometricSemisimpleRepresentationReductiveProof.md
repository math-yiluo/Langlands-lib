# Proof: a geometrically semisimple faithful representation forces reductivity

This module proves the Library statement
`Langlands.GroupScheme.GeometricallySemisimpleRepresentationReductiveStatement` (Milne,
*Algebraic Groups* (2017), Corollary 19.18, printed p. 401) at every universe `u`, as the
theorem `Langlands.GroupScheme.geometricallySemisimpleRepresentationReductive`. The theorem has
no hypotheses beyond those of the statement.

The proof follows Milne's one-line proof ("The hypothesis implies that the unipotent radical
of `G_{k^a}` is trivial"): it applies Proposition 19.17 over the algebraic closure. In the
Library, 19.17 is the second conjunct of
`Langlands.GroupScheme.SemisimpleRepresentationUnipotentStatement`, proved as
`Langlands.GroupScheme.semisimpleRepresentationUnipotent` (module
`Langlands.GroupScheme.Reductive.SemisimpleRepresentationUnipotentProof`).

## The two theorems

* `geometricallySemisimpleRepresentationReductive_of_semisimpleRepresentationUnipotent`
  `(h : SemisimpleRepresentationUnipotentStatement.{u}) :`
  `GeometricallySemisimpleRepresentationReductiveStatement.{u}`.
  This is the reduction of Corollary 19.18 to Proposition 19.17. It is stated separately
  because it uses `h` only through its second conjunct, applied to one field and one group.
* `geometricallySemisimpleRepresentationReductive :`
  `GeometricallySemisimpleRepresentationReductiveStatement.{u}`.
  This is the reduction applied to `semisimpleRepresentationUnipotent`.

## Proof of the reduction

Let `k : Type u` be a field and `G` a group scheme over `Spec k` with `[IsAffineHom G.X.hom]`,
`Smooth G.X.hom` and `ConnectedSpace G.X.left`. Let `ρ : MatrixRepresentation G (Fin n)` with
`IsClosedSubgroup ρ`, and assume that `ρ.baseChange (toAlgebraicClosure k)` is semisimple
(the local `IsSemisimpleRep` of the statement). The proof does not use the hypothesis that `ρ`
itself is semisimple over `k`.

`IsConnectedReductive G` has four fields. The first three, `Smooth G.X.hom`,
`IsAffineHom G.X.hom` and `ConnectedSpace G.X.left`, are hypotheses. For the fourth, write
`b = toAlgebraicClosure k` and `G_{k^a} = (GroupScheme.baseChange b).obj G`. The structure
morphism of `G_{k^a}` is, by definition, `pullback.snd G.X.hom b`, so:

1. `IsAffineHom` and `Smooth` hold for `G_{k^a}`: both properties are stable under base
   change, and Lean finds the instances for `pullback.snd G.X.hom b` (after a `change`).
   `LocallyOfFiniteType`, required by `SemisimpleRepresentationUnipotentStatement`, follows from
   smoothness by instance search.
2. `ConnectedSpace G_{k^a}.X.left` is the Library's
   `GroupScheme.connectedSpace_baseChange_of_smooth_affine` (module
   `Langlands.GroupScheme.GeometricConnectedness`): a connected group scheme of finite type over
   a field is geometrically connected (Milne, Summary 1.36, printed p. 17).
3. `IsClosedSubgroup (ρ.baseChange b)`. By definition
   `ρ.baseChange b = (GroupScheme.baseChange b).map ρ ≫ (GeneralLinear.baseChangeIso n b).hom`.
   The Library's `IsClosedSubgroup.baseChange` (module `Langlands.GroupScheme.SubgroupBaseChange`)
   says that the base change of a closed immersion is a closed immersion, and
   `IsClosedSubgroup.comp_iso` (module `Langlands.GroupScheme.Rational.SplitRankTransport`) says
   that composing with an isomorphism keeps it one.

The second conjunct of `h (AlgebraicClosure k) G_{k^a}`, applied to the smoothness and
connectedness of steps 1 and 2, to `n`, to `ρ.baseChange b`, to step 3 and to the semisimplicity
hypothesis, gives `HasTrivialUnipotentRadical G_{k^a}`, the fourth field. The semisimplicity
predicate of the target statement (with implicit field and group) and that of
`SemisimpleRepresentationUnipotentStatement` (for the fixed field `AlgebraicClosure k`) have the
same body, so the hypothesis is passed unchanged.

## Axioms

The axiom check of both theorems reports only `propext`, `Classical.choice` and
`Quot.sound`.
