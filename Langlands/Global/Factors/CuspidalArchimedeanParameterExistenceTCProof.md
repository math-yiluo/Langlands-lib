# Archimedean standard-module parameters of cuspidal realizations over totally complex fields

Authors: Worker 20, with Worker 174 (the global generic-component results used below).
Supporting proof candidate of Task 5720 (`a2cfc970-9e20-4d56-b053-8f91a2e0b5cc`). Worker 0
(Task 0) requested it, following the operator's answer `81ed24709e7050068786116ca6613260`
(Option A). The target of Task 5720, the unrestricted
`CuspidalArchimedeanParameterExistenceStatement`, does not change.

## Statement proved

`Langlands.Global.cuspidalArchimedeanParameterExistenceTC :
CuspidalArchimedeanParameterExistenceTCStatement.{u}` proves the Library statement
`Langlands.Global.CuspidalArchimedeanParameterExistenceTCStatement` (module
`Langlands.Global.Factors.CuspidalPairFunctionalEquationTCStatement`). It keeps the universe
`u` and adds no hypotheses. The statement is:

for every number field `F : Type u` with `[NumberField.IsTotallyComplex F]` and
`[CompactSpace (AdeleQuotient F)]`, every `r : ℕ` and every actual cuspidal realization
`T : Automorphic.CuspidalOperatorRealization F r` of `GL_(r+1)`,

1. at every real place `v` of `F` there is a list `ds` of real blocks with
   `OperatorRealization.HasRealPlaceParameter T.realization v ds`; and
2. at every complex place `v` of `F` there is a list `ds` of complex characters with
   `OperatorRealization.HasComplexPlaceParameter T.realization v ds`.

`HasComplexPlaceParameter` (module `Langlands.Automorphic.ArchimedeanPlaceParameter`) asks
that `ds` has length `r + 1`, and that some injective linear map sends the `U(r+1)`-finite
functions of the principal series `complexStandardModule (r+1) ds` into the space of
`T.realization`. This map must intertwine right translation with the compact action at `v`,
and right derivatives with the Lie action at `v`.

## Proof

The Lean proof is a short tactic proof. Fix `F`, `r` and `T`.

**Real places (clause 1).** This clause is vacuous. A place `v` in the subtype
`{v : InfinitePlace F // v.IsReal}` is complex by Mathlib's `IsTotallyComplex.isComplex`, so
it is not real (`InfinitePlace.not_isReal_iff_isComplex`). This contradicts `v.2`, and
`absurd` closes the goal.

**Complex places (clause 2).** The proof combines four proved Library theorems.

1. `Langlands.Automorphic.cuspidalArchimedeanGenericComponentBridge` (module
   `Langlands.Automorphic.CuspidalArchimedeanGenericComponentReduction`) proves the statement
   `CuspidalArchimedeanIrreducibleAdmissibleComponentStatement →
   CuspidalArchimedeanWhittakerFunctionalStatement →
   CuspidalArchimedeanGenericComponentStatement`. The proof applies it to the proved premises
   - `cuspidalArchimedeanIrreducibleAdmissibleComponent` (module
     `Langlands.Automorphic.PlaceComponentExistence`): at every infinite place, an actual
     cuspidal realization has a subspace that is irreducible for the place actions and
     admissible for the compact group;
   - `cuspidalArchimedeanWhittakerFunctional` (module
     `Langlands.Automorphic.CuspidalWhittaker.PlaceWhittaker`): for a cuspidal realization,
     every nonzero subspace stable under the place actions at an infinite place is generic.
     It carries a linear functional, nonzero on it, that is a Whittaker functional for some
     nondegenerate character. This comes from the Whittaker–Fourier expansion of cusp forms.

   Applied to `F`, `r` and `T`, the result `hG` says the following. At every complex place `v`
   (`hG.2 v`, an `OperatorRealization.HasComplexPlaceGenericComponent T.realization v`) there
   are a complex vector space `V : Type u` and actions `ρ` of `U(r+1)` and `π` of
   `ℂ ⊗[ℝ] 𝔤𝔩_(r+1)(ℂ)` on `V`. There is also an injective linear map `ι : V → T.realization.Space`
   that intertwines `ρ` and `π` with the compact and Lie actions at `v`. Finally, `(ρ, π)` is
   a complex `(𝔤, K)`-module that is irreducible, admissible and generic.
2. `Langlands.Archimedean.complexGenericStandardParameter :
   ComplexGenericStandardParameterStatement` (module
   `Langlands.Representation.Archimedean.ComplexGenericStandardParameterProof`) gives every
   such module a standard-module parameter. Applied to `(r + 1, V, ρ, π)` and the four
   properties, it yields `ds` with `Archimedean.HasComplexStandardParameter (r+1) ρ π ds`.
3. `OperatorRealization.hasComplexPlaceParameter_of_component` (module
   `Langlands.Automorphic.ArchimedeanParameterReduction`) composes the injective intertwining
   map of the standard module into `V` with `ι`. This gives
   `HasComplexPlaceParameter T.realization v ds`.

The complex-place step is the complex branch of the published reduction
`cuspidalArchimedeanParameterReduction`, with the premises replaced by proved theorems. The
proof does not call that reduction, because the reduction also needs the real-place premise
`RealGenericStandardParameterStatement`, which is still open (Task 5975). Over a totally complex
field this premise is not needed.

## Check

A private `lean_check` of this module reported 0 errors and 0 warnings. The theorem depends
only on the axioms `propext`, `Classical.choice` and `Quot.sound`.

## Provenance

Provenance: *derived*. The statement is the totally complex special case of the published
`CuspidalArchimedeanParameterExistenceStatement`. For its sources, see
`CuspidalPairFunctionalEquationTCStatement.md` and
`ArchimedeanParameterReduction.md`. The proof composes only Library theorems. The mathematical
sources of those theorems are documented in their own Markdown: Kostant (1978) and Vogan
(1978) for `complexGenericStandardParameter`, and the Whittaker–Fourier expansion and the
admissibility of the place components for the global generic-component theorems.
