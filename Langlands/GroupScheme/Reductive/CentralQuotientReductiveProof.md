# Proof: quotients of connected reductive groups by central subgroups

Authors: Worker 1428 (Lean proof and Markdown) and Worker 1499 (Markdown
revision and submission).

`Langlands.GroupScheme.centralQuotientReductive` proves the proposition
`Langlands.GroupScheme.CentralQuotientReductiveStatement.{u}` (module
`Reductive/CentralQuotientReductiveStatement`). Let `k` be any field, `G` a
connected reductive group over `k`, and `N` a subgroup functor of `G`
contained in `center G`. Let `q : G ⟶ Q` be a homomorphism with
`RelativeRoot.IsFppfQuotient N q`, where `Q` is affine and locally of finite
type. Then `Q` is connected reductive. The module also proves one helper.

## Helper result

- `SubgroupFunctor.baseChange_le_center`: for a morphism `b : S' ⟶ S` and a
  subgroup functor `N ≤ center G`, the base change `N.baseChange b` lies in
  the centre of the base-changed group. The published `center_baseChange`
  (`Reductive/CenterBaseChangeProof`) identifies that centre with
  `(center G).baseChange b`. The published `SubgroupFunctor.baseChange_mono`
  (`SubgroupFunctor/FpqcDescent`) preserves the inclusion.

## Main proof

The proof is the reduction of the published `centerQuotientReductive_of_geometricCore`
(`Adjoint/CenterQuotientReduction`), with the full centre replaced by `N`.
`IsConnectedReductive Q` has four fields.

1. Smoothness and connectedness of `Q` follow from those of `G` and the fppf
   quotient `q`, by the published `RelativeRoot.IsFppfQuotient.smooth_target`
   and `RelativeRoot.IsFppfQuotient.connectedSpace`.
2. `Q` is affine by hypothesis.
3. Trivial geometric unipotent radical. Let `b` be the base change to
   `AlgebraicClosure k` (`toAlgebraicClosure k`). The base-changed `G` is
   smooth and affine, and the base-changed `Q` is affine and locally of
   finite type, since these properties are stable under pullback. The
   base-changed `G` is connected (`connectedSpace_toAlgebraicClosure`) and
   has trivial unipotent radical; this is part of `IsConnectedReductive G`.
   The base-changed `q` is an fppf quotient by `N.baseChange b` (the
   published `RelativeRoot.IsFppfQuotient.baseChange`,
   `FppfQuotientComparison`), and `N.baseChange b` is central by the helper.
   The geometric core `CentralQuotient.hasTrivialUnipotentRadical_of_isFppfQuotient`
   (`CentralQuotientCore`) then gives a trivial unipotent radical for the
   base-changed `Q`.

The axioms used are `propext`, `Classical.choice` and `Quot.sound`.

## Module structure

The proof uses three helper modules in `Reductive/`:

- `CentralQuotientCommutator`: rational points of `G` over central points of
  a unipotent subgroup of `Q` commute. This is the published full-centre
  argument with `N ≤ center G`.
- `CentralPreimageTrivial`: finiteness lemmas. A smooth connected group with
  finitely many rational points is trivial. The reduced identity component
  has finite index on rational points. Centrality can be tested on rational
  points. A central smooth connected subgroup of a group with trivial
  unipotent radical has finite image on rational points in every unipotent
  group (Lemma D, in characteristic zero and in characteristic `p`).
- `CentralQuotientCore`: the algebraically closed case.

## Provenance

The statement and a suggested argument are in the statement's Markdown
(Milne, *Algebraic Groups*, 2017, source `milne-2017-algebraic-groups`;
Corollary 17.62(e), printed p.372–373, and the paragraph defining the
adjoint group at the end of Remark 17.63, printed p.373, for the full-centre
case; 6.46, 14.18, 14.21 and 16.48 for the suggested argument). The
implemented Lean route reduces to an algebraically closed field, as Milne's
definition of reductivity (6.46, printed p.135) does. Over the algebraically
closed field it follows the Library full-centre proof
(`Adjoint/CenterQuotientCore`) rather than the suggested argument. It replaces
the nilpotent splitting (16.48) by the finiteness lemmas of
`CentralPreimageTrivial`. These are derived from Library results on
commutative groups, tori and unipotent groups.

Checked with `lean_check` in environment `3b864ddf-f0af-4c18-8903-c6f813a0ce0f`
against Library commit `dd78edadc914cf56ca81c595cee581a3570d415c`, together
with the three helper modules (diagnostic
`980ecc53-e56b-4d35-a240-bd6dc92d1068`, Lake build): 0 errors, 0 warnings,
axioms `propext`, `Classical.choice`, `Quot.sound`.
