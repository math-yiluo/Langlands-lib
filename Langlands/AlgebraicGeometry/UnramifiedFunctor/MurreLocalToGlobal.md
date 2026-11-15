# Murre's Proposition 2: representability is local on the base

Module `Langlands.AlgebraicGeometry.UnramifiedFunctor.MurreLocalToGlobal`.

## Statement proved

`theorem murreLocalToGlobal : MurreLocalToGlobalStatement.{u, v}` proves the Library
statement `Langlands.AlgebraicGeometry.UnramifiedFunctor.MurreLocalToGlobalStatement`
(module `MurreProofSteps`) for arbitrary universes `u` and `v`, with no extra hypotheses.
This is Proposition 2 of J. P. Murre, *Representation of unramified functors.
Applications (according to unpublished results of A. Grothendieck)*, Séminaire Bourbaki,
exp. 294. Let `S` be a locally noetherian scheme and `F` a presheaf on `Over S` that
satisfies the conditions of Murre's Theorem 1 (`MurreConditions F`). Suppose that for
every point `s` of `S`, the base change of `F` to `Spec 𝒪_{S,s}` is represented by a
scheme that is separated, locally of finite type and formally unramified over
`Spec 𝒪_{S,s}`. Then `F` itself is represented by a scheme that is separated, locally
of finite type and formally unramified over `S`.

## Proof

The proof is a single term that assembles results already in the Library. It follows
Murre's route: Lemma 2 gives the inductive step (the construction of charts), and the
inductive step together with Lemma 3 gives Proposition 2.

1. **Lemma 2 (openness of the étale locus).**
   - `EtaleLocus.genericNoLargerLift : GenericNoLargerLiftStatement` (module
     `MurreGenericNoLargerLiftProof`) is the first half of Murre's case (b). At a point
     `y` of `Spec (R'/𝔍)` lying over the generic point of `Spec R`, condition (F8) gives
     a neighbourhood `V` of `y`. At every point `w` of `V`, `𝔍` is nilpotent in the
     local ring `R'_w`, and the restriction of `ξ` lifts to no strictly larger closed
     subscheme of `Spec R'_w`.
   - `EtaleLocus.closedEtaleLocusOpen_of_generic : ClosedOfGenericStatement` (module
     `EtaleLocusAssembly`) turns this into `ClosedEtaleLocusOpenStatement`. This is the
     case of Lemma 2 where the test scheme is a closed subscheme `Spec (R'/𝔍)` of an
     étale `Spec R`-scheme `Spec R'`. It covers the rest of case (b) and the whole of
     case (a), and finishes with noetherian induction on closed subsets.
   - `EtaleLocus.murreEtaleLocusOpen_of_closed` (module `MurreEtaleLocusClosedProof`)
     reduces the general Lemma 2, `MurreEtaleLocusOpenStatement`, to that closed case.
2. **The inductive step (charts).** `Charts.murreChartsFromEtaleLocus :
   MurreChartsFromEtaleLocusStatement` (module `MurreCharts`) derives
   `MurreNoetherianChartsStatement` from `MurreEtaleLocusOpenStatement`. Over the
   spectrum of a noetherian ring, and under the noetherian induction hypothesis, it gives
   a family of monomorphic, infinitesimally étale charts of `F`, locally of finite type
   and formally unramified, through which every field-valued point of `F` factors.
3. **Lemma 3 (gluing of charts).** `ChartGluing.murreChartGluing :
   MurreChartGluingStatement` (module `ChartGluingRepr`) is Murre's Lemma 3 in the form
   of SGA 3, XI, Proposition 3.5. Such a family of charts glues to a representing scheme.
4. **Proposition 2.** `murreLocalToGlobal_of_steps` (module
   `MurreLocalToGlobalReduction`) proves `MurreLocalToGlobalStatement` from
   `MurreLocalToGlobalStepsStatement`, the conjunction of `MurreChartGluingStatement` and
   `MurreNoetherianChartsStatement`. The anonymous constructor
   `⟨ChartGluing.murreChartGluing, Charts.murreChartsFromEtaleLocus …⟩` supplies this
   conjunction.

The proof uses only the axioms `propext`, `Classical.choice` and `Quot.sound`. It does
not use `MurreCriterionStatement`, `MurreProofStepsStatement`, or any statement that
consumes Proposition 2.
