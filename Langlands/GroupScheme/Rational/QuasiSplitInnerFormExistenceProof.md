# Proof: existence of quasi-split inner forms of connected reductive field groups

Author: Worker 4768.

This module proves the published Library proposition
`Langlands.GroupScheme.QuasiSplitInnerFormExistenceStatement`
(module `Langlands.GroupScheme.Rational.QuasiSplitInnerFormExistenceStatement`)
at an arbitrary universe `u`:

```
theorem quasiSplitInnerFormExistence : QuasiSplitInnerFormExistenceStatement.{u}
```

So for every field `K : Type u` and every group scheme `G` over `Spec K` with
`IsConnectedReductive G`, there is a `QuasiSplitInnerForm G`. The theorem adds
no hypotheses: the field is arbitrary (any characteristic, not necessarily
perfect or infinite), and there is no dimension, norm or supplied-structure
premise. The statement's Lean/Markdown pair and the `QuasiSplitInnerForm`
structure are used unchanged. The theorem therefore supplies every field of the
structure as output:

- a quasi-split ground-field model `H`, with a field-defined Borel that remains
  Borel over the algebraic closure;
- an actual adjoint quotient `H ⟶ A` by the full scheme-theoretic centre, with
  `A` quasi-split;
- a finite Galois field extension `L/K` with `L : Type u`;
- natural local multiplicative equivalences from `H` to `G` on every relative
  test scheme over the cover `Spec L ⟶ Spec K`;
- an `A`-valued natural cocycle with the discrepancy equation for the actual
  inner action of `A` on `H`.

The module adds no definitions and no axioms. A `lean_check` inspection of
`quasiSplitInnerFormExistence` reports only `propext`, `Classical.choice` and
`Quot.sound`.

## Proof

The proof applies one published Library reduction to two published Library
theorems:

```
quasiSplitInnerFormExistence_of_rootDatum_adjoint rootDatumExistence
  adjointQuotientExistence
```

1. `quasiSplitInnerFormExistence_of_rootDatum_adjoint`
   (module `Rational.QuasiSplitInnerFormExistenceReduction`) states that
   `RootDatumExistenceStatement.{u}` and `AdjointQuotientExistenceStatement.{u}`
   together imply `QuasiSplitInnerFormExistenceStatement.{u}`. For a connected
   reductive `G` over `K`, its proof constructs every component of the inner-form
   presentation:
   - a maximal `K`-torus, by `maximalTorusExistence`;
   - a finite Galois extension `L/K` in `Type u` splitting that torus, by
     `torusFiniteGaloisSplitting`;
   - a split pinning of `G_L`, from the root datum that the first hypothesis
     supplies for the split maximal torus of `G_L`;
   - the Galois action on that root datum, corrected by Weyl elements to an
     action on the based root datum;
   - the quasi-split model `H`, as the descent of the pinned Galois datum, with
     an isomorphism `H_L ≅ G_L`;
   - an adjoint quotient `H ⟶ A`, from the second hypothesis, with `A`
     quasi-split by `adjointQuotientQuasiSplitStatement`;
   - the local equivalences `LocalGroupIso.ofBaseChangeIso` of `H_L ≅ G_L`, with
     inner discrepancy on every relative test by
     `SplitPinning.hasInnerDiscrepancy_solution`;
   - the natural adjoint cocycle, which `QuasiSplitInnerForm.ofInnerDiscrepancy`
     builds from the inner discrepancies using faithfulness of the actual inner
     action.

   The paired Markdown of that module records each step.
2. `rootDatumExistence` (module `Reductive.RootDatumExistence`) proves
   `RootDatumExistenceStatement.{u}`. Every split maximal torus of a connected
   reductive field group has a reduced root datum indexed by a finite type in
   `Type u`.
3. `adjointQuotientExistence` (module `Adjoint.ExistenceProof`) proves
   `AdjointQuotientExistenceStatement.{u}`. Every connected reductive group over
   an arbitrary field has an actual adjoint quotient by its full scheme-theoretic
   centre.

All three results are taken at the same universe `u` as the target, so the
splitting field is in the universe of `K`, as the target requires.

## Provenance

The target statement cites Conrad, *Reductive group schemes* (2014),
Proposition 7.2.11 (printed/PDF p.258) and the field discussion of Section 7.2
(printed/PDF pp.250–252), source `conrad-2014-reductive-group-schemes`. There,
the quasi-split inner form is built from the section of the automorphism scheme
defined by a pinning. The Library reduction follows this route with a
finite-Galois split pinning and a based Galois action. This proof contributes
only the final composition; the mathematical content is in the three cited
Library modules.
