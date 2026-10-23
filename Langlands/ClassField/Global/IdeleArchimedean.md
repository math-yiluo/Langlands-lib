# Archimedean components of idele cohomology in degree two

Let `F` and `E` be number fields with `E` an `F`-algebra, `G = Gal(E/F)`
(`E ≃ₐ[F] E`), and `J_E` the idele group of `E` with the published Galois
representation `relativeIdeleRepresentation F E`. This module treats the
infinite places of `E` in the cohomology `H²(G, J_E)`. It provides:

1. the coordinate `J_E → E_wˣ` at an infinite place `w`, and the action of
   the stabilizer `D_w` of `w` on `E_wˣ`;
2. the semilocal projection `J_E ⟶ Coind(E_wˣ)` along `D_w`, with a coset-sum
   section;
3. the archimedean invariant `archimedeanIdeleInvariant F w : H²(G, J_E) →+ ℚ/ℤ`.
   On the image of `H²(G, Eˣ)` it agrees with the published
   `Reciprocity.archimedeanInvariant w`;
4. the vanishing criterion `archimedeanIdeleInvariant_eq_zero_iff`. A class in
   `H²(G, J_E)` has archimedean invariant `0` at every infinite place exactly
   when it is the class of a 2-cocycle whose values all have infinite adele
   part `1`.

No Galois hypothesis on `E / F` is needed. Only the criterion assumes
`[NumberField F]`, which makes `G` finite. Only degree `2` is treated. The
module does not define a local invariant on `H²(D_w, E_wˣ)`, and it does not
prove that the archimedean invariants identify the archimedean part of
`H²(G, J_E)` with a sum of copies of `½ℤ/ℤ`.

## Sources

- Milne, *Class Field Theory* v4.03 (`milne-2020-class-field-theory`),
  Chapter VII §2, printed pp.203–206 (PDF pp.212–215). Lemma 2.1 gives the
  action of `G` on `∏_{w|v} L_w`: if `α` has `a` in the `w`-position, then
  `σα` has `σa` in the `σw`-position. Proposition 2.2 gives the
  `G`-isomorphism `α ↦ f_α`, `f_α(σ) = σ(α(σ⁻¹w₀))`, onto
  `Ind_{G_{w₀}}^G L_{w₀}`, with inverse `f ↦ α_f`. Proposition 2.3 gives
  `Hʳ(G, ∏_{w|v} L_wˣ) ≅ Hʳ(G_{w₀}, L_{w₀}ˣ)` by Shapiro's lemma.
  Proposition 2.5(b) gives `Hʳ_T(G, I_L) = ⊕_v Hʳ_T(G_v, L_vˣ)` for all
  `r ≥ 0`, a sum over all primes `v` of `K`, the infinite ones included.
- The archimedean invariant: Milne Chapter IV §4, "The real numbers", printed
  p.139 (PDF p.148). It says `H²(ℂ/ℝ) ≅ Ĥ⁰(G, ℂˣ) = ℝˣ/Nm ℂˣ = {±}`, and the
  nonzero class is represented by the 2-cocycle with value `-1` at `(σ, σ)`
  and `1` elsewhere. The formula used here is the one in the published
  `ReciprocityStatement` module, which explains it in detail.

## Coordinates at infinite places

Let `E` be a number field.

- `ideleInfiniteCoordinate w : J_E →* E_wˣ`, for an infinite place `w`, is the
  `w`-component of the infinite adele part of an idele.
  `ideleInfiniteCoordinate_val` unfolds it.
- `ideleInfiniteCoordinate_ofCompletion_self` and
  `ideleInfiniteCoordinate_ofCompletion_of_ne`: Mathlib's single-coordinate
  idele `IdeleGroup.ofCompletion w y` has coordinate `y` at `w` and `1` at
  every other infinite place.
- `ideleInfiniteCoordinate_unitEmbedding`: the `w`-coordinate of the principal
  idele of `a ∈ Eˣ` is the image of `a` in `E_w`.
- `ideleInfinite_eq_one_iff`: an idele has infinite adele part `1` iff all its
  infinite coordinates are `1`.
- `ideleOfInfiniteCoordinates a`, for a family `a w ∈ E_wˣ` over all infinite
  places, is the idele with infinite coordinates `a w` and finite adele part
  `1`. `ideleInfiniteCoordinate_ideleOfInfiniteCoordinates` gives its
  coordinates.

## The Galois action on infinite coordinates

Now `E` is an `F`-algebra. The published action `relativeIdeleAut F E g` of
`g ∈ G` on `J_E` uses the published `infinitePlaceEquiv g w` (the place
`w ∘ g`) and `infiniteCompletionEquiv g w`.

- `ideleInfiniteCoordinate_relativeIdeleAut`: the `w`-coordinate of `g • x`
  is `infiniteCompletionEquiv g w` applied to the coordinate of `x` at
  `infinitePlaceEquiv g w`. This holds by definition. It is Milne's Lemma 2.1
  in the form `(σα)(w) = σ(α(σ⁻¹w))`.
- `infinitePlaceEquiv_eq_inv_smul`: `infinitePlaceEquiv g w` is `g⁻¹ • w` for
  Mathlib's action of `G` on infinite places. `infinitePlaceEquiv_mul`:
  `infinitePlaceEquiv (g * h) w = infinitePlaceEquiv h (infinitePlaceEquiv g w)`.
- `infinitePlaceEquiv_eq_self_iff`: `infinitePlaceEquiv g w = w` iff `g` lies
  in Mathlib's stabilizer `MulAction.stabilizer G w`. In this module `D_w`
  denotes that stabilizer.
- `mem_stabilizer_of_isConj`: the complex conjugation `c` of `w` (Mathlib's
  `ComplexEmbedding.IsConj w.embedding c`) lies in `D_w`.
- `extensionEmbedding_algebraMap`: Mathlib's embedding
  `InfinitePlace.Completion.extensionEmbedding w : E_w → ℂ` sends the image of
  `a ∈ E` to `w.embedding a`.
- `extensionEmbedding_infiniteCompletionEquiv_of_isConj` and
  `extensionEmbedding_ideleInfiniteCoordinate_of_isConj`: if `c` is the complex
  conjugation of `w`, then the complex value of the `w`-coordinate of `c • x`
  is the complex conjugate of that of `x`. The first lemma is proved on the
  dense image of `E` in `E_w` (Mathlib's `InfinitePlace.Completion.induction_on`).
- `ideleInfiniteCoordinate_relativeIdeleAut_eq_iff`: `g • x` and `g • y` have
  the same `w`-coordinate iff `x` and `y` have the same coordinate at
  `infinitePlaceEquiv g w`. `ideleInfiniteCoordinate_congr` transports an
  equality of coordinates along an equality of places.
- `ideleInfiniteCoordinate_relativeIdeleAut_congr`: if `g ∈ D_w`, the
  `w`-coordinate of `g • x` depends only on the `w`-coordinate of `x`.
- `ideleInfiniteCoordinate_relativeIdeleAut_eq_one` and
  `ideleInfiniteCoordinate_relativeIdeleAut_ofCompletion_of_ne`: if the
  coordinate of `x` at `infinitePlaceEquiv g w'` is `1`, then the
  `w'`-coordinate of `g • x` is `1`. In particular the single-coordinate idele
  at `w`, moved by `g`, has coordinate `1` at every `w'` with
  `infinitePlaceEquiv g w' ≠ w`.
- `relativeIdeleAut_mul_apply`: `(g * h) • x = g • (h • x)`.
  `relativeIdeleAut_finite_eq_one`: the action preserves ideles with finite
  adele part `1`.
- `idele_eq_ofCompletion`: an idele with finite adele part `1` and coordinate
  `1` at every infinite place other than `w` is the single-coordinate idele of
  its `w`-coordinate.
- `relativeIdeleAut_ofCompletion_of_eq`: if `g ∈ D_w`, then `g` maps the
  single-coordinate idele of `y` at `w` to the single-coordinate idele of the
  `w`-coordinate of the image.

## The local module and the semilocal maps

- `infiniteLocalAction F w` is the action of `D_w` on `E_wˣ` (a
  `MulDistribMulAction`, declared `@[instance_reducible]` but not an
  instance). `d • y` is the `w`-coordinate of `d • ι_w(y)`, where
  `ι_w(y) = IdeleGroup.ofCompletion w y`. This is the action of Milne's
  Lemma 2.1 on the `w`-position for `σ ∈ G_w`. It is defined through `J_E`, so
  no transport along the equality `infinitePlaceEquiv d w = w` is needed.
- `infiniteLocalRepresentation F w` is the representation of `D_w` on
  `Additive E_wˣ`. It is the published
  `NormalizedTwoCocycle.coefficientRepresentation` for this action, so it has
  the same scalars as `relativeIdeleRepresentation F E`.
  `infiniteLocalRepresentation_apply` unfolds the action.
- `infiniteCoordinateLinear F w` is the `w`-coordinate as a linear map of
  coefficient modules, and `infiniteLocalProjection F w` is the morphism of
  `D_w`-representations from the restriction of `J_E` to `E_wˣ` that it
  defines.
- `infiniteEmbeddingLinear F w` and `infiniteLocalEmbedding F w` are the
  single-coordinate embedding `E_wˣ → J_E`, linear and as a morphism of
  `D_w`-representations (by `relativeIdeleAut_ofCompletion_of_eq`).
- `infiniteSemilocalProjection F w : J_E ⟶ Coind(E_wˣ)` is Mathlib's
  `Rep.resCoindToHom` of the local projection, with coinduction along the
  inclusion `D_w → G`. `infiniteSemilocalProjection_apply`: its value at `g`
  is the `w`-coordinate of `g • x`. This is Milne's `f_α(σ) = σ(α(σ⁻¹w₀))` of
  Proposition 2.2.
- `map_infiniteSemilocalProjection_comp_shapiroMapOf`: the map
  `Hⁿ(G, J_E) → Hⁿ(D_w, E_wˣ)` induced by the restriction to `D_w` and the
  local projection is the map induced by the semilocal projection, followed by
  the published Shapiro map `Shapiro.shapiroMapOf`.
- `ideleInfiniteCoordinate_eq_of_infiniteSemilocalProjection_eq`: if `x` and
  `y` have the same semilocal projection at `w`, they have the same
  coordinate at `infinitePlaceEquiv g w` for every `g`, that is, at every
  place of the orbit of `w`.

The remaining definitions of this section assume a `Fintype` instance on
`G ⧸ range(D_w → G)`.

- `infiniteSemilocalSection F w : Coind(E_wˣ) ⟶ J_E` is the published coset
  sum `Shapiro.coindSum` of the local embedding,
  `f ↦ ∑_{gD_w} g • ι_w(f(g⁻¹))`. This is Milne's inverse `f ↦ α_f` of
  Proposition 2.2.
- `infiniteSemilocalSection_comp_infiniteSemilocalProjection`: the section
  followed by the projection is the identity. The hypotheses of the published
  `Shapiro.coindSum_comp_resCoindToHom` come from
  `ideleInfiniteCoordinate_ofCompletion_self` and
  `ideleInfiniteCoordinate_relativeIdeleAut_ofCompletion_of_ne`.
  `infiniteSemilocalProjection_infiniteSemilocalSection` is the same statement
  on elements.
- `ideleInfiniteCoordinate_infiniteSemilocalSection_infiniteSemilocalProjection`:
  projecting and then applying the section does not change the coordinates at
  the places of the orbit of `w`.

## The archimedean invariant

- `rationalClass_half_ne_zero`: the class of `1/2` in `ℚ/ℤ` is nonzero.
- `ideleConjugationValue c f`, for `c ∈ G` and a 2-cochain `f` of `J_E`, is
  the idele `f(c,c) · f(1,1)`: the sum `f(c,c) + f(1,1)` read back
  multiplicatively. `ideleConjugationValue_add` says it is multiplicative in
  `f`.
- `ideleConjugationValue_fixed`: if `c * c = 1` and `f` is a 2-cocycle, `c`
  fixes `f(c,c) · f(1,1)`. As in the published `conjugationValue_fixed`, this
  is the cocycle identity at `(c, c, c)`.
- `extensionEmbedding_ideleConjugationValue_im`: if `c` is the complex
  conjugation of `w` and `f` is a 2-cocycle, then the complex value of the
  `w`-coordinate of `f(c,c) · f(1,1)` is real. It equals its own conjugate by
  the previous lemma and `extensionEmbedding_ideleInfiniteCoordinate_of_isConj`.
- `archimedeanIdeleCocycleHom F w` is an additive map from the 2-cocycles of
  `J_E` to `ℚ/ℤ`, defined with `open Classical`. If some `c ∈ G` with `c ≠ 1`
  lies in `D_w`, it sends `f` to the published
  `signClass (extensionEmbedding w (w-coordinate of f(c,c) · f(1,1)))`, with
  `c` chosen by `Classical.choose`. Otherwise it sends `f` to `0`. The
  condition and the choice are literally those of the published
  `Reciprocity.archimedeanCocycleHom`. Additivity is the published
  `signClass_mul` (both values are real and nonzero). The published
  `isConj_of_mem_stabilizer` says that the chosen `c` is the complex
  conjugation of `w`.
  `archimedeanIdeleCocycleHom_apply_of_exists` and
  `archimedeanIdeleCocycleHom_apply_of_not_exists` give the two cases.
- `archimedeanIdeleCocycleHom_coboundary`: the map vanishes on 2-coboundaries.
  For `f = d b`, the product `f(c,c) · f(1,1)` telescopes to `(c • b(c)) · b(c)`
  because `c * c = 1`. Its complex value at `w` is `z̄ z` with `z` the value of
  the `w`-coordinate of `b(c)`, and the published `signClass_star_mul_self`
  gives `0`.
- `archimedeanIdeleInvariant F w : relativeIdeleCohomology F E 2 →+ ℚ/ℤ` is the
  published `Reciprocity.H2Lift` of `archimedeanIdeleCocycleHom F w`.
  `archimedeanIdeleInvariant_H2π`: on the class of a cocycle `f` it is
  `archimedeanIdeleCocycleHom F w f`.
- `ideleConjugationValue_principalIdeleCocycles₂`: for a 2-cocycle `z` of
  `Eˣ`, the idele `f(c,c) · f(1,1)` of its image under the published
  `principalIdeleCocycles₂ F E` is the principal idele of the published
  `conjugationValue c z`.
- `archimedeanIdeleInvariant_principalIdeleCohomologyMap`: for
  `x ∈ H²(G, Eˣ)`, the archimedean invariant at `w` of its image under the
  published `principalIdeleCohomologyMap F E 2` is the published
  `archimedeanInvariant w x`.

Background, not proved in this module: as explained in
`ReciprocityStatement`, the stabilizer `D_w` is trivial or `{1, c}` with `c`
the complex conjugation of `w`. In the second case `w` is complex, `E_w` is
identified with `ℂ`, and in the sources the sign class of `f(c,c) · f(1,1)`
is the image of the `D_w`-component of the class of `f` in
`Ĥ⁰(D_w, ℂˣ) = ℝˣ/ℝ_{>0} ≅ ½ℤ/ℤ`. Here that component is taken through the
`w`-coordinate of ideles, as in Milne's Proposition 2.5(b) for the infinite
place `v` below `w`. This module proves no such identification. It proves
only the lemmas listed here and the criterion below.

## Primitives

- `exists_d₁₂_eq_infiniteLocalProjection`: if
  `archimedeanIdeleCocycleHom F w f = 0` for a 2-cocycle `f` of `J_E`, then
  there is a 1-cochain `β : D_w → E_wˣ` whose coboundary is the restriction of
  `f` to `D_w × D_w` followed by the `w`-coordinate. If `D_w` is trivial,
  `β` is constant with value the `w`-coordinate of `f(1,1)`. Otherwise
  `D_w = {1, c}`, and `y`, the `w`-coordinate of `f(c,c) · f(1,1)`, has
  positive real complex value: it is real, nonzero, and its sign class is
  `0`. Since `w` is complex (Mathlib's `ComplexEmbedding.isConj_ne_one_iff`
  and `InfinitePlace.isComplex_iff`), Mathlib's
  `InfinitePlace.Completion.surjective_extensionEmbedding_of_isComplex` gives
  `s ∈ E_wˣ` with complex value `√(Re y)`. Then `s` is fixed by `c` and
  `s · s = y`. The cochain with `β(1)` the `w`-coordinate of `f(1,1)` and
  `β(c) = s` works. The four pairs in `D_w × D_w` are checked with the
  cocycle identities `f(1, g) = f(1, 1)` and `f(g, 1) = g • f(1, 1)`.
- `exists_d₁₂_eq_infiniteSemilocalProjection`: under the same hypothesis, the
  semilocal projection of `f` at `w` is the coboundary of a 1-cochain
  `G → Coind(E_wˣ)`. The class of the semilocal projection maps to `0` under
  the Shapiro map, by the previous lemma and
  `map_infiniteSemilocalProjection_comp_shapiroMapOf`. The Shapiro map is an
  isomorphism by the published `Shapiro.isIso_shapiroMapOf`, because the
  inclusion `D_w → G` is injective.
- `ideleInfiniteCoordinate_d₁₂_eq`: let `β` be such a 1-cochain and `b` a
  1-cochain of `J_E` whose coordinates at the places of the orbit of `w` agree
  with those of the semilocal sections of the values of `β`. Then `d b` and
  `f` have the same coordinates at the places of the orbit of `w`.

## The vanishing criterion

Assume in addition `[NumberField F]`.

- `archimedeanIdeleInvariant_eq_zero_iff c`: for
  `c ∈ relativeIdeleCohomology F E 2`, `archimedeanIdeleInvariant F w c = 0`
  for every infinite place `w` of `E` iff there is a 2-cocycle `f` with
  `H2π f = c` all of whose values have infinite adele part `1`.

  Forward direction: let `f` represent `c`. For every infinite place `p`,
  choose a 1-cochain `β p` as in `exists_d₁₂_eq_infiniteSemilocalProjection`.
  Let `r u` be the representative chosen by `Quotient.out` of the `G`-orbit of
  an infinite place `u`. Let `b(k)` be the idele with finite part `1` and, at
  every infinite place `u`, the `u`-coordinate of the semilocal section at
  `r u` of `β (r u) k`. By `ideleInfiniteCoordinate_d₁₂_eq` at `r u`, `d b` has
  the same infinite coordinates as `f`, so `f - d b` represents `c` and has
  infinite adele part `1` everywhere. Converse: if all values of `f` have
  infinite adele part `1`, the `w`-coordinate of `f(c,c) · f(1,1)` is `1`, and
  `signClass 1 = 0`.

## Provenance and scope

The component of a class of `H²(G, J_E)` at an infinite place, and the
vanishing of all of them for the classes with trivial infinite part, are part
of Milne's Proposition VII.2.5(b) (with Propositions 2.2 and 2.3). Combined
with the description of `H²(ℂ/ℝ)` in Chapter IV §4, the component at a real
place `v` with complex `w` is detected by a sign. The definitions here are
derived from those sources. The archimedean invariant follows the convention
of the published `Reciprocity.archimedeanInvariant` (same predicate, same
`Classical.choose`, the sign class of `f(c,c) · f(1,1)`), so that
`archimedeanIdeleInvariant_principalIdeleCohomologyMap` holds. The following
are internal to this formalization: the definition of the local action
through `J_E`, the explicit square root in place of a computation of
`H²(D_w, E_wˣ)`, the use of the published Shapiro machinery along the
inclusion of the stabilizer, the gluing over orbit representatives chosen by
`Quotient.out`, and the form of the criterion, which is stated for the
degree-two classes of `J_E` with an explicit representative.
