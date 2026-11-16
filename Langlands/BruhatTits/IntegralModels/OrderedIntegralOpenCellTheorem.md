# Ordered integral open cells over the maximal unramified integers (proof)

Module `Langlands.BruhatTits.IntegralModels.OrderedIntegralOpenCellTheorem`.

## Statement proved

`Langlands.BruhatTits.IntegralModels.unramifiedOrderedIntegralOpenCell` proves
the unchanged published proposition
`UnramifiedOrderedIntegralOpenCellStatement.{u}` (module
`Langlands.BruhatTits.IntegralModels.OrderedIntegralOpenCell`) at an arbitrary
universe `u`, with no extra hypotheses.

For every nonarchimedean local field `F`, put `K = inertiaFixedField F` and
`O = fixedFieldIntegers F`. Take an affine group scheme `G` over `K`, building
data `C`, and a zero datum `E` with
`(torusCentralizer C.i).IsRepresentedBy E.i`. Take an apartment point `x`, a
nonempty `Ω` that is bounded above under every real affine functional, and a
smooth integral model `N` with

```text
N.integralPoints = E.zeroPoints ⊓ C.pointwiseFixer (C.apartmentMap '' Ω).
```

Then there is an actual `A : TorusRootModelFamilyData C E x Ω N` with the
following property. Let `ν` be any generic cocharacter. Let `aneg` and `apos`
be any injective finite enumerations of the indivisible roots in
`RelativeRoot.indivisiblePositiveRoots C.i (-ν)` and
`RelativeRoot.indivisiblePositiveRoots C.i ν` respectively. Then the
underlying scheme morphism of `A.orderedIntegralMultiplication aneg apos` is
an open immersion. The order of factors is negative roots, then torus, then
positive roots, and empty side products are allowed. This is the
open-immersion clause, with family existence, of Kaletha–Prasad
Proposition 8.3.14(3). The statement's paired Markdown gives the precise
scope.

## Implemented proof

The proof applies one published theorem to two other published theorems:

1. `unramifiedOrderedIntegralOpenCellReduction` (module
   `OrderedIntegralOpenCellReduction`) proves
   `UnramifiedOrderedIntegralOpenCellReductionStatement.{u}`. That statement
   is the implication
   `UnramifiedTorusConnectedBoundStatement.{u} →
   UnramifiedTorusIwahoriConnectedImageStatement.{u} →
   UnramifiedOrderedIntegralOpenCellStatement.{u}`.
2. `unramifiedTorusConnectedBound` (module
   `UnramifiedTorusConnectedBoundProof`) proves the first premise. Integral
   points of a smooth torus model with geometrically connected fibres lie in
   the norm-defined Iwahori subgroup (KP Corollary B.8.7, using the argument
   of Proposition B.8.8(3)).
3. `unramifiedTorusIwahoriConnectedImage` (module
   `UnramifiedTorusIwahoriConnectedImageProof`) proves the second premise.
   The norm-defined Iwahori subgroup is the image of the integral points of
   such a model (KP Lemma B.3.1 and Definition 2.5.13).

The three imported modules are these three proof modules. Each application
uses the same universe `u` explicitly.

The construction of the family and the open-immersion argument are in the
reduction and its supporting modules. Their Markdown describes the
implemented route and how it differs from the source. In brief:

- the root models are the SplitRoot root models of a closed integral split
  torus of `N`;
- the torus model is the relative identity component of the integral
  centralizer of that torus;
- the open immersion comes from the dynamic open cell of `N`;
- the integral ordered root products are identified with the dynamic
  unipotent subgroups by an integral-point criterion for smooth affine models
  over a strictly henselian discrete valuation ring.

The two torus theorems are used only to show that the integral points of the
torus model are exactly `E.torusIwahori`.

Compilation (`lean_check`, lake-build) reports no errors and no warnings.
The theorem depends only on the axioms `propext`, `Classical.choice` and
`Quot.sound`.

## Provenance

This module adds no definitions or statements. It proves a statement that is
already published, by composing the three Library theorems named above.

The mathematical target is Kaletha–Prasad, *Bruhat–Tits Theory: A New
Approach* (2023), Proposition 8.3.14(3) together with Theorem 8.3.13, printed
pp. 299–300 / PDF pp. 330–331. The source is registered as
`kaletha-prasad-2023-bruhat-tits-new-approach`. The registered
`kaletha-prasad-2024-corrections`, PDF pp. 37–38, add the perfect-residue
assumption and correct the connected-model argument. Both are already taken
into account in the statement and the reduction.
