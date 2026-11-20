# Common local components determine an automorphic representation

Author: Worker 3657.

Lean module: `Langlands.Automorphic.LocalComponentDeterminationReverse`. It
imports the draft modules `Langlands.Representation.FreeMonoidGenerators`
(and through it `Langlands.Representation.CommutingFamilyUniqueness`) and
`Langlands.Automorphic.OperatorSubquotientPlaceGeneration`, and the Library
modules `Langlands.Representation.Smooth.Schur.Proof`,
`Langlands.Representation.Unramified.SphericalFixedLineProof` and
`Langlands.Global.FiniteAdelicGL.PadicComparison`. It changes no published
file.

This module proves the reverse implication "⇐" of
`Langlands.Automorphic.LocalComponentDeterminationStatement` (Task 6817) from
`LocalComponentExistenceStatement` (proved by the Library's
`localComponentExistence`, Task 6815).

## Main theorem

```lean
theorem Langlands.Automorphic.localComponentDetermination_reverse
    (hex : LocalComponentExistenceStatement.{u})
    (F : Type u) [Field F] [NumberField F] (r : ℕ) (Q Q' : IrreducibleOperatorSubquotient F r)
    (hQ : Q.subquotient.IsJointlyAdmissible)
    (h : (finite places) ∧ (real places) ∧ (complex places)) :
    Nonempty (Q.Equivalence Q')
```

The hypothesis `h` is the right-hand side of the biconditional in
`LocalComponentDeterminationStatement`, copied verbatim: at every finite place
an irreducible `ρ` on a `W : ModuleCat.{u} ℂ` with `Q` and `Q'` both
`ρ`-isotypic, and at every real or complex place an irreducible
`(𝔤, K)`-module `(V, ρ, π)` with both `(ρ, π)`-isotypic. Only the joint
admissibility of `Q` is used. The local representations in `h` are only
assumed irreducible (not admissible or smooth); everything else is
transported from the admissible local components of `Q` supplied by `hex`.

## Declarations

**Places and generators.**

- `PlaceIndex F := FinitePlace F ⊕ (real places ⊕ complex places)`.
- `PlaceGenerator F n i`: `FiniteLocalGL F n v` at a finite place;
  `RealPlaceGenerator n = ULift (O(n) ⊕ (ℂ ⊗_ℝ 𝔤𝔩_n(ℝ)))` at a real place,
  `ComplexPlaceGenerator n = ULift (U(n) ⊕ (ℂ ⊗_ℝ 𝔤𝔩_n(ℂ)))` at a complex
  place (lifted so that every place has generators in the universe `u`).
- `placeSpherical F n i`: the one-letter words in `GL_n(𝒪_v)` at a finite
  place, `∅` at an infinite place; `of_mem_placeSpherical`.

**Place actions of an operator subquotient** `Q : OperatorSubquotient F n`.

- `placeGeneratorAction Q i`: the local translations `Q.localRepresentation v`
  at a finite place; `gkGenerators ULift.down` of the compact action and the
  complexified Lie action at an infinite place.
- `placeRep Q i := rep (placeGeneratorAction Q i)`, a representation of the
  free monoid on `PlaceGenerator F n i`.
- `placeGeneratorAction_comm_finite`, `_finite_real`, `_finite_complex`,
  `_real`, `_real_complex`, `_complex`, and `placeGeneratorAction_comm`: the
  generators at distinct places commute. The cases use
  `OperatorSubquotient.localRepresentation_comm_of_ne`,
  `realPlaceCompactRepresentation_comm_of_ne`,
  `realPlaceCompactRepresentation_comm_complexPlace`,
  `complexPlaceCompactRepresentation_comm_of_ne` (draft module
  `OperatorSubquotientPlaceGeneration`), the Library's
  `finiteRepresentation_realPlaceCompactRepresentation`,
  `finiteRepresentation_complexPlaceCompactRepresentation`,
  `finiteRepresentation_realPlaceLieAction`,
  `finiteRepresentation_complexPlaceLieAction`, and the Library's
  `realPlaceLieAction_comm_of_ne`, `realPlaceLieAction_comm_complexPlace`,
  `realPlaceCompactRepresentation_realPlaceLieAction_of_ne`,
  `realPlaceCompactRepresentation_complexPlaceLieAction`,
  `complexPlaceLieAction_comm_of_ne`,
  `complexPlaceCompactRepresentation_complexPlaceLieAction_of_ne`,
  `complexPlaceCompactRepresentation_realPlaceLieAction` (Task 6815 modules).
- `placeRep_commuting`: hence `RestrictedTensor.CyclicEvaluation.Commuting`
  (`rep_comm`).
- `placeRep_eventually_fixed`: every vector is fixed by
  `placeSpherical F n i` for all but finitely many `i`: at finite places by
  `FiniteAdelicGL.eventually_fixed_localIntegral` (draft module
  `OpenSubgroupInduction`) applied to the Library's
  `finiteRepresentation_isSmooth`; the infinite places are finitely many.
- `representation_mem_of_placeRep_stable`: a subspace stable under all
  place actions is stable under `Q.representation a` for every operator `a`
  (`representation_mem_of_placeStable`, draft module
  `OperatorSubquotientPlaceGeneration`).
- `isJointlyIrreducible_placeRep`: for `Q` irreducible and nonzero, the
  place actions are jointly irreducible (`CommutingFamily.IsJointlyIrreducible`):
  a stable subspace is a subrepresentation of `Q.representation`, hence `⊥`
  or `⊤`.

**Local data.** `PlaceData F n` bundles a carrier in `ModuleCat.{u} ℂ` and
local actions at every place; `PlaceData.carrier`, `PlaceData.action`
(local translations at finite places, `gkGenerators ULift.down` at infinite
places) and `PlaceData.localRep`.

**Common local components.**

- `automorphicObject_scalar`: Schur's lemma for an irreducible admissible
  `A : AutomorphicObject (padicField v) (r+1)`, read as a representation of
  `FiniteLocalGL F (r + 1) v` (the Library's
  `admissibleSchur_scalarEndomorphism`).
- `automorphicObject_fixed_line`: the vectors of such an `A` fixed by
  `GL_(r+1)(𝒪_v)` lie on a line. The Library's
  `FiniteAdelicGL.localIntegral_eq_sphericalSubgroup` identifies
  `GL_(r+1)(𝒪_v)` with `Correspondence.sphericalSubgroup (padicField v) r`;
  the fixed space is `⊥` or, by the Library's
  `Unramified.sphericalFixedLine`, of dimension one (`finrank_eq_one_iff'`).
- `finitePlace_isCommonType`: let `ρ` be an irreducible local component of
  `Q` and `Q'` at a finite place `v`, and let `A` be the admissible local
  component of `Q` from `hex`. By `isCommonType_monoid`, `rep ⇑ρ` is a common
  type of the place actions of `Q` and `Q'` with scalar self-intertwiners,
  and `ρ ≃ A`; by `exists_fixed_line_of_equiv` the vectors of `ρ` fixed by
  `GL_(r+1)(𝒪_v)` lie on a line.
- `realPlace_isCommonType`, `complexPlace_isCommonType`: the same at
  infinite places with `isCommonType_gk`. The `GKModuleDensity.Hyp` of the
  admissible component `(ρA, πA)` from `hex` is built from its
  `IsRealGKModule` (resp. `IsComplexGKModule`) structure: each vector lies in
  its finite-dimensional orbit span, and matrix coefficients are continuous.

## The implemented proof of the main theorem

1. Choose the common local components `ρ_v` from `h` and the admissible
   components of `Q` from `hex`; bundle the former as `D : PlaceData F (r+1)`.
2. At every place `i`, `D.localRep i` is irreducible with scalar
   self-intertwiners, and the place actions of `Q` and `Q'` are both
   `D.localRep i`-isotypic (`finitePlace_isCommonType`,
   `realPlace_isCommonType`, `complexPlace_isCommonType`).
3. At every finite place the vectors of `D.localRep i` fixed by
   `placeSpherical` lie on a line; the remaining places (infinite) are
   finitely many, so this holds for all but finitely many `i`.
4. The place actions of `Q` and of `Q'` commute (`placeRep_commuting`), are
   jointly irreducible (`isJointlyIrreducible_placeRep` with the
   irreducibility of `Q` and `Q'`) and smooth (`placeRep_eventually_fixed`).
5. `CommutingFamily.exists_linearEquiv_of_isotypic` gives a linear
   isomorphism `Φ : Q.Space ≃ Q'.Space` with `Φ ∘ placeRep Q i g =
   placeRep Q' i g ∘ Φ`; on one-letter words this says that `Φ` commutes with
   the local translations, the compact translations and the complexified Lie
   actions at every place.
6. `OperatorSubquotient.equivalenceOfPlaceComm` (draft module
   `OperatorSubquotientPlaceGeneration`) turns `Φ` into `Q.Equivalence Q'`.

## Provenance

The statement is the uniqueness half of Getz–Hahn, *An introduction to
automorphic representations* (2024), Theorem 6.3.7, p.165 (PDF 179), with
the uniqueness of the factors and the proof on p.166 (PDF 180)
(`getz-hahn-2024-automorphic-representations`, SHA256
`a125cf9c0f445972cbbd3552b4fb9905ca948108a05880f90eaa43558d09a507`), and of
Flath, *Decomposition of representations into tensor products* (1979),
Theorem 3, p.181 (PDF 177) (`flath-1979-tensor-products`, SHA256
`3b9fe0145da81d870ef8967be83635cd440a2581fe043e64e63324e22dec4db5`).

The sources compare the restricted tensor products of the local components.
The one-dimensional `K_v`-fixed spaces at almost every finite place make
the isomorphism class independent of the reference vectors. See Flath,
§2, Example 2, p. 181 (PDF p. 177), and Getz–Hahn, §5.7, pp. 151–152
(PDF pp. 166–167). The Lean proof uses the isotypic restrictions described
at the end of Flath's proof of Theorem 1, p. 180 (PDF p. 176), together with
Schur's lemma for admissible local representations, spherical fixed-line
bounds and smoothness. `nonempty_equiv_of_isotypic` matches the local types
inside `isCommonType_monoid` and `isCommonType_gk`.
`CommutingFamily.exists_linearEquiv_of_isotypic` builds the intertwiner by
cyclic evaluation on the restricted tensor products of the local cyclic
spaces of selected vectors. `OperatorSubquotientPlaceGeneration` uses
smoothness to extend the intertwining to the full operator algebra.

## Check

`lean_check` 65394a97 (module): 0 errors, 0 warnings; lake build dbe84f71 of
the full Task 6817 draft: 0 errors, 0 warnings.
