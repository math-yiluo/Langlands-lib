# Henselian discrete quasi-splitness from rational strongly regular classes

Author: Worker 4699.

Lean module: `Langlands.GroupScheme.Rational.HenselianDiscreteQuasiSplitReduction`,
namespace `Langlands.GroupScheme`.

This module reduces
`Langlands.GroupScheme.HenselianDiscreteQuasiSplitStatement.{u}` to one
proposition that the Library states but does not yet prove:
`Langlands.GroupScheme.QuasiSplitRegularClassRationalStatement.{u}`
(module `Rational/QuasiSplitRegularClassRationalStatement`). That proposition
is the rationality of Galois-stable strongly regular classes in simply
connected quasi-split groups, the form of Steinberg (1965), Theorem 1.7, as
extended by Borel–Springer (1968), 8.6, that the Library uses. This module
does not prove it, so it does not prove the Henselian target by itself. Every
other input is a published Library proof.

## Declarations

- `HenselianDiscreteQuasiSplitReductionStatement` (a `Prop`-valued `def`,
  universe `u`):

  ```lean
  def HenselianDiscreteQuasiSplitReductionStatement : Prop :=
    QuasiSplitRegularClassRationalStatement.{u} → HenselianDiscreteQuasiSplitStatement.{u}
  ```

- `dimensionLEOneQuasiSplit_of_classRational (h : QuasiSplitRegularClassRationalStatement.{u}) :
  DimensionLEOneQuasiSplitStatement.{u}` (theorem). The same input gives
  Steinberg's quasi-splitness theorem for every field satisfying the
  finite-separable norm criterion `Langlands.FieldTheory.HasDimensionLEOne`.
- `henselianDiscreteQuasiSplit_of_dimensionLEOne (h : DimensionLEOneQuasiSplitStatement.{u}) :
  HenselianDiscreteQuasiSplitStatement.{u}` (theorem). The Henselian target
  follows from the dimension-at-most-one target.
- `henselianDiscreteQuasiSplitReduction :
  HenselianDiscreteQuasiSplitReductionStatement.{u}` (theorem). The
  composite of the two preceding theorems.

The statement `HenselianDiscreteQuasiSplitStatement` is unchanged. Its
hypotheses are a field `K : Type u`, a surjective valuation
`v : Valuation K (WithZero (Multiplicative ℤ))`, Henselianity of
`v.valuationSubring`, and algebraic closedness of its actual residue field.
Its conclusion is `IsQuasiSplit H` for every connected reductive group scheme
`H` over `Spec K`. The reduction adds no premise on `K`: no completeness,
perfectness, separability of the completion, or characteristic restriction.
Its only premise is the displayed proposition about simply connected
quasi-split groups over arbitrary fields.

## Proof

`henselianDiscreteQuasiSplit_of_dimensionLEOne`: given `K`, `v` and the three
valuation hypotheses, the published theorem
`Langlands.FieldTheory.henselianDiscreteDimensionLEOne` (module
`FieldTheory/HenselianDiscreteDimensionLEOneProof`) gives
`HasDimensionLEOne K`. Applying the hypothesis
`DimensionLEOneQuasiSplitStatement` to `K`, this fact, `H` and its connected
reductivity gives `IsQuasiSplit H`.

`dimensionLEOneQuasiSplit_of_classRational h` applies the published
conditional assembly `dimensionLEOneQuasiSplit_of_structural_inputs` (module
`Rational/SteinbergAssembly`). It needs three propositions, supplied as
follows.

1. *Quasi-split inner forms.* `QuasiSplitInnerFormExistenceStatement` is
   `quasiSplitInnerFormExistence_of_rootDatum_adjoint rootDatumExistence
   adjointQuotientExistence`. The reduction comes from module
   `Rational/QuasiSplitInnerFormExistenceReduction`. Its two inputs are the
   published proofs `rootDatumExistence` (module
   `Reductive/RootDatumExistence`) and `adjointQuotientExistence` (module
   `Adjoint/ExistenceProof`).
2. *Torus reduction of cocycles.* `QuasiSplitCocycleTorusReductionStatement`
   is `quasiSplitCocycleTorusReduction_of_prerequisites` (module
   `Rational/QuasiSplitCocycleTorusReduction`). It is applied to three
   inputs:
   - `simplyConnectedCoverExistence` (module
     `SimplyConnected/CoverExistenceProof`);
   - `infiniteFieldStronglyRegularPoint` (module
     `Rational/InfiniteFieldStronglyRegularPoint`);
   - `quasiSplitSimplyConnectedRegularConjugate_of_classRational h
     regularConjugateFiniteGalois`. This is the published conditional
     reduction in module `Rational/QuasiSplitRegularConjugateReduction`,
     applied to the hypothesis `h` and the published proof
     `regularConjugateFiniteGalois` (module
     `Rational/RegularConjugateFiniteGaloisProof`).
3. *Torus cocycle vanishing.* `DimensionLEOneTorusCocycleVanishingStatement`
   is the published proof `dimensionLEOneTorusCocycleVanishing` (module
   `Rational/DimensionLEOneTorusCocycleVanishingProof`).

`henselianDiscreteQuasiSplitReduction` sends `h` to
`henselianDiscreteQuasiSplit_of_dimensionLEOne
(dimensionLEOneQuasiSplit_of_classRational h)`.

The development check used only the standard axioms `propext`,
`Classical.choice` and `Quot.sound`.

## Provenance

The conclusion is the integer-normalized formulation of Kaletha–Prasad,
*Bruhat–Tits Theory: A New Approach* (2023), Corollary 2.3.8, printed p.81
(PDF p.112), source `kaletha-prasad-2023-bruhat-tits-new-approach`. Their
proof combines Corollary 2.3.7 (dimension at most one, same page) with
Theorem 2.3.3(2), printed p.79 (PDF p.110). For that theorem they refer to
Serre's *Galois Cohomology*, III §2.2, Theorem 1, and note that the
quasi-split part does not need a perfect base field. The Lean route follows
the same structure: field dimension, then the quasi-split inner form,
Steinberg's torus reduction of cocycles and the vanishing of torus cocycles.
The order of the composition is internal to this Library.

The hypothesis `QuasiSplitRegularClassRationalStatement` corresponds to
Steinberg, *Regular elements of semi-simple algebraic groups* (1965),
Theorem 1.7, printed p.51 (PDF p.4), source
`steinberg-1965-regular-elements-semisimple-groups`, extended to arbitrary
fields by Borel–Springer, *Rationality properties of linear algebraic groups
II* (1968), 8.6, printed pp.483–484 (PDF pp.41–42), source
`borel-springer-1968-rationality-properties-ii`. Its own Markdown describes
the exact Lean form. Its proof task is
`dd1d7a92-2f47-4d25-b340-c9e4a1ab4ed0`. Once that proof is published,
applying `henselianDiscreteQuasiSplitReduction` to it proves the Henselian
target.
