# The idele group as a Galois representation and its finite-place coordinates

This module makes the actual idele group `J_E` of a number field `E` into a
representation of `Gal(E/K)`, for Mathlib group cohomology. For a finite place
`w` of `E` over a finite place `v` of `F` it builds the `w`-coordinate
`J_E → E_wˣ` and proves that this coordinate is equivariant along the
published `decompositionHom v w : Gal(E_w/F_v) → Gal(E/F)`. From this come
morphisms of representations between `J_E` and `E_wˣ` and the maps they induce
on group cohomology in every degree. The module also gives the matching
localization `Eˣ → E_wˣ` and its maps on cohomology. All declarations are in
`Langlands.ClassField.Global`.

Here `J_E` is Mathlib's `NumberField.IdeleGroup (𝓞 E) E`: the units of the
full adele ring, with the infinite and finite parts. `Eˣ` and `E_wˣ` carry the
published representations `Langlands.ClassFieldTheory.Local.unitsRepresentation`.
Only finite places are treated; infinite places and the semilocal Shapiro
isomorphism are not part of this module.

## The idele representation

Let `K` and `E` be fields with `E` a number field and `[Algebra K E]`. `K` and
`E` may lie in different universes.

- `relativeIdeleAut K E` is the homomorphism `Gal(E/K) → Aut(J_E)` sending `σ`
  to the published idele isomorphism `ideleEquiv σ.toRingEquiv`. It is a
  homomorphism by the published `ideleEquiv_refl` and `ideleEquiv_trans`.
  `continuous_relativeIdeleAut` records that each `relativeIdeleAut K E σ` is
  continuous.
- `relativeIdeleAction` is the resulting multiplicative action of `Gal(E/K)`
  on `J_E`. It is a local instance in this module, and
  `relativeIdele_smul` gives its value.
- `relativeIdeleRepresentation K E` is the representation of `Gal(E/K)` on
  `Additive J_E`, with scalars `NormalizedTwoCocycle.CoefficientScalars`.
  This is the published `NormalizedTwoCocycle.coefficientRepresentation`
  applied to that action, the same construction as the published idele-class
  representation `relativeIdeleClassRepresentation`.
  `relativeIdeleRepresentation_apply` gives its value.
- `relativeIdeleCohomology K E n` is Mathlib's `groupCohomology` of this
  representation in degree `n`.

## Coordinates at a finite place

Let `E` be a number field and `w` a finite place of `E`.

- `ideleCoordinate w : J_E →* E_wˣ` sends an idele to its `w`-coordinate in
  the finite adeles. `ideleCoordinate_val` gives its value.
- `ideleCoordinate_ofAdicCompletion_self`: the `w`-coordinate of Mathlib's
  idele `IdeleGroup.ofAdicCompletion (𝓞 E) E w x` (coordinate `x` at `w`, `1`
  at every other place) is `x`.
- `ideleCoordinate_ofAdicCompletion_of_ne`: the `w'`-coordinate of that
  idele is `1` for every finite place `w' ≠ w`.
- `ideleCoordinate_unitEmbedding`: the `w`-coordinate of the principal idele
  of `a ∈ Eˣ` is the image of `a` in `E_w`.
- `ideleEquiv_ofAdicCompletion_of_eq` takes a ring isomorphism `e : K ≃+* L`
  of number fields, finite places `p` of `L` and `q` of `K` with
  `finitePlaceEquiv e p = q`, and a continuous ring homomorphism
  `φ : K_q → L_p` that extends `e` on the image of `K`. Then `ideleEquiv e`
  sends the idele with coordinate `x` at `q` to the idele with coordinate
  `φ(x)` at `p`. The proof substitutes the equation of places and identifies
  `φ` with the published `finiteCompletionEquiv e p`, since both are
  continuous and agree on the dense image of `K`. It then applies the
  published `ideleEquiv_ofAdicCompletion`. This is the idele analogue of the
  published `ideleClassEquiv_ofAdicCompletion_of_eq`.

## Equivariance along the decomposition map

Let `E / F` be a normal extension of number fields, `v` a finite place of
`F`, `w` a finite place of `E` over `v`, and `σ` an `F_v`-automorphism of
`E_w`. The published `CohomologyMaps` lemmas say that `decompositionHom v w σ`
fixes `w`, restricts `σ` on `E`, and that `σ` is continuous.

- `ideleCoordinate_relativeIdeleAut_decompositionHom`: the `w`-coordinate of
  `decompositionHom v w σ • x` is `σ` applied to the `w`-coordinate of `x`.
  The proof applies the published `adicCompletion_coordinate_eq` to the
  published `finiteCompletionEquiv` and to `σ`.
- `relativeIdeleAut_decompositionHom_ofAdicCompletion`:
  `decompositionHom v w σ` sends the idele with coordinate `x` at `w` to the
  idele with coordinate `σ x` at `w`. This is the transport lemma with
  `φ = σ`.

## Morphisms of representations and maps on cohomology

In this section `Gal(E_w/F_v)` acts on `J_E` and on `Eˣ` through
`decompositionHom v w`, that is, by Mathlib's `Rep.res`.

- `ideleCoordinateLinear` and `ideleEmbeddingLinear` are the
  `w`-coordinate and the single-coordinate embedding
  `x ↦ IdeleGroup.ofAdicCompletion (𝓞 E) E w x` as linear maps between the
  additive modules. The `_apply` lemmas give their values.
- `ideleLocalProjection v w` is the `w`-coordinate as a morphism of
  representations of `Gal(E_w/F_v)` from `J_E` to `E_wˣ`.
  `ideleLocalEmbedding v w` is the single-coordinate embedding as a morphism
  from `E_wˣ` to `J_E`. They intertwine the actions by the two equivariance
  lemmas above.
- `ideleLocalEmbedding_comp_ideleLocalProjection`: the embedding followed by
  the projection is the identity of `E_wˣ`.
- `ideleLocalMap v w n` is the map
  `Hⁿ(Gal(E/F), J_E) → Hⁿ(Gal(E_w/F_v), E_wˣ)`. It is Mathlib's
  `groupCohomology.map` along `decompositionHom v w` with coefficient
  morphism `ideleLocalProjection v w`: restriction of cochains along the
  decomposition map, followed by the `w`-coordinate. This is the component at
  `w` of the semilocal map of Artin–Tate.
- `ideleLocalInclusion v w n` is the map
  `Hⁿ(Gal(E_w/F_v), E_wˣ) → Hⁿ(Gal(E_w/F_v), J_E)` induced by
  `ideleLocalEmbedding v w`, where `J_E` is restricted along
  `decompositionHom v w`.
- `unitsLocalizationLinear` is the linear map `Eˣ → E_wˣ`,
  `a ↦ algebraMap E E_w a`, between the additive modules;
  `unitsLocalizationLinear_apply` gives its value.
- `unitsLocalization v w` is this map as a morphism of representations of
  `Gal(E_w/F_v)`, from `Eˣ` restricted along `decompositionHom v w` to
  `E_wˣ`. It intertwines the actions by the published
  `algebraMap_decompositionHom`.
- `unitsLocalMap v w n` is the map
  `Hⁿ(Gal(E/F), Eˣ) → Hⁿ(Gal(E_w/F_v), E_wˣ)` given by
  `groupCohomology.map` along `decompositionHom v w` with coefficient
  morphism `unitsLocalization v w`. It is the local component at `w` of a
  global class.

This module does not construct the principal map `Eˣ → J_E` as a morphism of
representations, any exact sequence, or the semilocal Shapiro isomorphism. It
proves no vanishing or injectivity results.

## Sources and provenance

The idele group, the action of the Galois group on it and the semilocal
description of its cohomology through the decomposition group and the
coordinate at a place over `v` follow Artin–Tate, *Class Field Theory*
(AMS Chelsea, 2009), Preliminaries §1, printed pp. 1–2 (PDF pp. 10–11), and
Chapter VII §3, printed pp. 42–43 (PDF pp. 51–52). The Lean construction is
internal. It uses the published idele isomorphisms `ideleEquiv`, the
published decomposition map `decompositionHom`, Mathlib's `Rep.res` and
`groupCohomology.map`, and the density argument of the published
`CohomologyMaps` module.
