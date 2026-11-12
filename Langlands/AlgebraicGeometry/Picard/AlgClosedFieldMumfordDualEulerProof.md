# Proof of the dual-side Euler characteristic of a finite flat Mumford map

Authors: Worker 3613, with Worker 2029. Worker 2029's lifting argument is adapted in the
support module `FiniteTranslationDifferenceLifting` of the published prerequisite
`fieldFiniteMumfordMapSurjective`. The main proof repeats the Library's
`algClosedFieldMumfordDualEulerReduction` (module
`AlgClosedFieldMumfordDualEulerFromPrerequisites`). Only its final degree step is replaced.

Module `Langlands.AlgebraicGeometry.Picard.AlgClosedFieldMumfordDualEulerProof`, namespace
`Langlands.AbelianScheme`.

## Target

The theorem `algClosedFieldMumfordDualEuler` has type exactly the published proposition
`Langlands.AbelianScheme.AlgClosedFieldMumfordDualEulerStatement.{u}`, from module
`Langlands.AlgebraicGeometry.Picard.AlgClosedFieldMumfordDualEulerStatement`. The universe
`u` is arbitrary and there are no further hypotheses. The proposition quantifies over:

- its binders `preservation` and `square`;
- every algebraically closed field `K`;
- every abelian scheme `A` over `Spec K` with dual datum `hA`;
- all `L`, `B`, `M` and evaluation isomorphisms;
- the actual Mumford map `f`, assumed finite and flat;
- every `g` with `A.HasRelativeDimension g`;
- every `hQ` and every point `y` of the dual.

For all of these, the theorem gives

`χ(A ×_K A, m^* N ⊗ snd^* M) = (-1)^g · f.left.finrank y`,

where `N` is the normalized bundle. The statement Markdown explains the objects and the
source. The source is the proof of the Riemann–Roch theorem (9.11) of Edixhoven, van der Geer
and Moonen, *Abelian Varieties* (registered source
`edixhoven-vandergeer-moonen-abelian-varieties-draft`), formulas (8)–(10), printed p.132
(PDF p.136).

## Route

The Library's `algClosedFieldMumfordDualEulerReduction` derives the target from four universal
statements. Three of them now have published proofs, and this proof uses those proofs
directly:

- `algClosedFieldPoincareDirectImage` (module `AlgClosedFieldPoincareDirectImageProof`) proves
  `AlgClosedFieldPoincareDirectImageStatement`;
- `Langlands.AlgebraicGeometry.Modules.flatHigherDirectImageBaseChange` proves
  `FlatHigherDirectImageBaseChangeStatement`;
- `lineBundleHigherProjectionFormula` proves `LineBundleHigherProjectionFormulaStatement`.

The fourth, `FieldDualSchemeGeometryStatement`, has no published proof and is not used. The
reduction uses it only for connectedness of the dual, to show that the degree of `f.left` is
the same at every point. Here connectedness comes from the published theorem
`fieldFiniteMumfordMapSurjective` instead, the proof of
`FieldFiniteMumfordMapSurjectiveStatement`: a finite Mumford map over a field is surjective,
so the dual is the image of the connected scheme `A`. This is step 7 of the contract's route,
with connectedness obtained from the map `f` of the target.

## Declarations

- `finrank_eq_of_surjective_dualScheme K A hA f hsurj y y'`. Let `K` be a field and `A` an
  abelian scheme over `Spec K` with chosen dual `D`. Let `f : A ⟶ D` be a morphism over
  `Spec K` such that `f.left` is finite, flat and surjective. Then `f.left.finrank y` equals
  `f.left.finrank y'` for all points `y` and `y'` of `D`.
- `algClosedFieldMumfordDualEuler : AlgClosedFieldMumfordDualEulerStatement.{u}`.

## Proof of `finrank_eq_of_surjective_dualScheme`

1. `A.X.left` is connected, because the abelian scheme is geometrically connected over a field
   (`GeometricallyConnected.connectedSpace_of_subsingleton`).
2. `D.left` is the image of `A.X.left` under the continuous surjection `f.left`, so it is
   connected (`Function.Surjective.connectedSpace`).
3. `D ⟶ Spec K` is locally of finite type (published `dualScheme_locallyOfFiniteType`), so
   `D.left` is locally Noetherian (`LocallyOfFiniteType.isLocallyNoetherian`).
4. `f.left` is finite, hence locally of finite type. Its target is locally Noetherian, so it is
   locally of finite presentation (a Mathlib instance).
5. A finite, flat morphism locally of finite presentation has locally constant degree
   (`Scheme.Hom.isLocallyConstant_finrank`). On the connected space `D.left` it is constant
   (`IsLocallyConstant.apply_eq_of_preconnectedSpace`).

## Proof of `algClosedFieldMumfordDualEuler`

Introduce all binders. The proof follows `algClosedFieldMumfordDualEulerReduction`. Write `p`
for the parameter projection and `Q = m^* N ⊗ snd^* M`.

1. Surjectivity: after substituting `hf`, the map `f` is
   `mumfordSchemeMap preservation square A NR M evaluation hA`, with `NR` the normalized
   rigidified bundle. By definition this is `mumfordSchemeMapOfLineBundle`. The published
   `fieldFiniteMumfordMapSurjective`, applied with the hypothesis `IsFinite f.left` of the
   target, shows that `f.left` is surjective.
2. Direct images: the published `mumfordDual_higherDirectImage` (module
   `MumfordDualDirectImages`) is applied to the three published proofs listed under Route,
   with `hf`, `Flat f.left` and `hg`. It gives `hzero` (`Rⁿ p_* Q = 0` for `n ≠ g`) and an
   isomorphism `R^g p_* Q ≅ N ⊗ f^*(e_D)_* 𝒪_K`.
3. Support: `FiniteFlatPointFibre.hasFiniteClosedSupport_tensor_pullback_pushforward`, with
   flat base change, and `hasFiniteClosedSupport_iff_of_iso` show that `R^g p_* Q` has finite
   closed support.
4. Leray: `eulerCharacteristic_comp_eq_of_concentrated` rewrites the Euler characteristic as
   `(-1)^g · dim_K Γ_{A.X.hom}(R^g p_* Q)`.
5. Dimension: the isomorphism and
   `FiniteFlatPointFibre.finrank_relativeGlobalSections_tensor_pullback_pushforward` identify
   this dimension with the degree of `f.left` at `e_D((dualScheme A hA).hom y)`.
6. Degree: `finrank_eq_of_surjective_dualScheme`, applied to the surjectivity from step 1,
   says that this degree equals the degree at `y`. This step replaces
   `finrank_eq_of_fieldDualSchemeGeometry`.

## Scope

The theorem keeps the arbitrary universe and every algebraically closed field in every
characteristic. It keeps every relative dimension `g`, including `0`, and every point `y`,
closed or not. No ampleness, projectivity, Noetherian, characteristic or existence
hypothesis is added. The binders `preservation` and `square` are those of the target
proposition. The proof does not use `AlgClosedFieldAmpleMumfordEulerSquareStatement` or
anything downstream of the target. Every cited result is a published Library proof or a
Mathlib result.
