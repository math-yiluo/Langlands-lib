# Steinberg's quasi-splitness theorem for fields of dimension at most one

Task `0367ba06-f71f-44ff-83b2-e9de61795702` (Task 4733). Author: Worker 15.

Lean module: `Langlands.GroupScheme.Rational.DimensionLEOneQuasiSplitProof`,
namespace `Langlands.GroupScheme`.

This module proves the published proposition
`Langlands.GroupScheme.DimensionLEOneQuasiSplitStatement.{u}`
(module `Rational/DimensionLEOneQuasiSplitStatement`) with the closing theorem

```lean
theorem dimensionLEOneQuasiSplit : DimensionLEOneQuasiSplitStatement.{u}
```

The statement pair and every pair it imports are unchanged. The universe `u` is arbitrary.
Here is what the theorem says. Let `K : Type u` be a field satisfying
`Langlands.FieldTheory.HasDimensionLEOne K`, the finite-separable/Galois unit-norm criterion.
Then every group scheme `H` over `Spec K` with `IsConnectedReductive H` satisfies
`IsQuasiSplit H`. The theorem has no hypotheses. It adds no premise of perfectness,
characteristic, valuation, Henselianity, integral model, supplied Borel or descent datum. It
also uses no unproved Library statement as a premise.

## Declaration

- `dimensionLEOneQuasiSplit : DimensionLEOneQuasiSplitStatement.{u}` (theorem). Its proof term
  is

  ```lean
  dimensionLEOneQuasiSplit_of_classRational
    (quasiSplitRegularClassRationalReduction quasiSplitSteinbergQuotient)
  ```

## Proof

The proof composes three published Library results. Each is imported by its Lean name.

1. `quasiSplitSteinbergQuotient : QuasiSplitSteinbergQuotientStatement.{u}`
   (module `Rational/QuasiSplitSteinbergQuotient`, Task 4945,
   `d49e6c73-9af7-436f-9fd6-9c447baa4271`). Every simply connected quasi-split group `G` over a
   field `K` has a class quotient `ρ : G → V` with three properties:
   - `ρ` is invariant under conjugation;
   - its strongly regular fibres are geometric conjugacy classes;
   - strongly regular rational points of `V` lift to rational points of `G`.
2. `quasiSplitRegularClassRationalReduction :
   QuasiSplitSteinbergQuotientStatement.{u} → QuasiSplitRegularClassRationalStatement.{u}`
   (module `Rational/QuasiSplitRegularClassRationalReduction`). Applied to item 1, it gives
   `QuasiSplitRegularClassRationalStatement.{u}`: every Galois-stable strongly regular geometric
   conjugacy class of a simply connected quasi-split group contains a `K`-rational point.
3. `dimensionLEOneQuasiSplit_of_classRational
   (h : QuasiSplitRegularClassRationalStatement.{u}) : DimensionLEOneQuasiSplitStatement.{u}`
   (module `Rational/HenselianDiscreteQuasiSplitReduction`). Applied to item 2, it gives the
   target. Internally it is the published assembly `dimensionLEOneQuasiSplit_of_structural_inputs`
   (module `Rational/SteinbergAssembly`), which takes three published inputs:
   - quasi-split inner forms: `quasiSplitInnerFormExistence_of_rootDatum_adjoint
     rootDatumExistence adjointQuotientExistence`;
   - torus reduction of cocycles: `quasiSplitCocycleTorusReduction_of_prerequisites
     simplyConnectedCoverExistence infiniteFieldStronglyRegularPoint
     (quasiSplitSimplyConnectedRegularConjugate_of_classRational h regularConjugateFiniteGalois)`;
   - vanishing of torus cocycles over fields satisfying the norm criterion:
     `dimensionLEOneTorusCocycleVanishing`.

   Given `K`, `HasDimensionLEOne K` and a connected reductive `H`, the assembly writes `H` as an
   inner twist of a quasi-split group by a cocycle with values in the adjoint quotient. Torus
   reduction replaces that cocycle by a cocycle with values in a maximal torus. That cocycle is
   trivial by the torus vanishing, so `H` is quasi-split.

The proof needs no tactic. The theorem is the term above, and Lean checks that its type is
definitionally `DimensionLEOneQuasiSplitStatement.{u}`. The development check
(`lean_check`, environment `5c94c648-e8dc-4002-a50a-071ebf3f6096`) compiled the module with no
errors or warnings. The inspected declaration depends only on the standard axioms `propext`,
`Classical.choice` and `Quot.sound`.

## Sources

- T. Kaletha and G. Prasad, *Bruhat–Tits Theory: A New Approach* (2023), Theorem 2.3.3(2),
  printed p.79 (PDF p.110), source `kaletha-prasad-2023-bruhat-tits-new-approach`, SHA-256
  `05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`. This is Steinberg's theorem
  as stated in the target's Markdown. The dimension-at-most-one criterion is in Section 2.3,
  printed pp.78–79 (PDF pp.109–110). Kaletha–Prasad refer to Serre, *Galois Cohomology*, III
  §2.2, Theorem 1, for the proof.
- R. Steinberg, *Regular elements of semi-simple algebraic groups*, Publ. Math. IHÉS 25 (1965),
  source `steinberg-1965-regular-elements-semisimple-groups`, SHA-256
  `bda20c4a4b3cf4a7e9e5b17a4eacd0147d0c9370063ab3a3778114a53c8349b9` (PDF page = printed page
  − 47). Item 2 corresponds to Theorem 1.7 (printed p.51). The class quotient in item 1
  corresponds to 6.5, 6.6, 6.10, 7.9 and 9.2–9.19. The torus reduction in item 3 is the proof of
  Theorem 1.8 in §10 (printed p.78). It takes a rational strongly regular element of the twisted
  group, uses 1.7 to put a rational point in its conjugacy class, and then moves the cocycle into
  that point's centralizer torus. The deduction of Theorem 1.9 and Corollary 10.2 a) (a Borel
  subgroup over `k`) appears on printed pp.78–79. Steinberg assumes `k` perfect. Kaletha–Prasad
  note that the reductive quasi-split assertion does not need this, and the Lean statement makes
  no perfectness assumption.
- A. Borel and T. A. Springer, *Rationality properties of linear algebraic groups II*,
  Tôhoku Math. J. 20 (1968), source `borel-springer-1968-rationality-properties-ii`, SHA-256
  `e465d0622ca9540ff21e0d53d7b2fdb00a14cf70a7caceee352c040a3cb1abef`, 8.6 (printed pp.483–484).
  It extends Steinberg's rationality of regular classes to arbitrary fields.

The implemented route follows the structure of the literature proof:

1. reduce to the quasi-split inner form;
2. reduce cocycles in the simply connected quasi-split group to torus cocycles, using rational
   points of Galois-stable strongly regular classes;
3. show that torus cocycles vanish under the norm criterion.

The Lean order of composition is internal to this Library. This module only composes published
results and adds no mathematics of its own.
