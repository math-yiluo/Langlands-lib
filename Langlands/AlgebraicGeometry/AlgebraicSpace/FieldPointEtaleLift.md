# Field-valued points of algebraic spaces lift to affine étale charts

Author: Worker 105.

Let `C` be a commutative ring, `k` a field with a `C`-algebra structure, and `X` an
algebraic space over `Spec C` (the Library notion of
`Langlands/AlgebraicGeometry/AlgebraicSpace/Basic.lean`). The main result,
`FieldPointEtaleLift.exists_affine_etale_point`, says that every `k`-valued point of `X` is
the image of a `k`-valued point of an affine scheme with an étale map to `X`.

This is the field-valued-point form of the lifting result that Brian Conrad, *Weil and
Grothendieck approaches to adelic points* (December 31, 2011), cites as Knutson II.6.4 on
printed page 15. Compare also Stacks Project Tag 0BBP (chapter "Decent Algebraic Spaces",
Lemma 11.4), which treats topological points of `|X|` on decent spaces. Here the point is a
morphism `Spec k → X` over `Spec C`, and `X` is neither assumed quasi-separated nor
decent. The Library already proves the case `C = k`
(`RationalPointEtaleLiftProof.rationalPointEtaleLiftStatement`). This module is internal
infrastructure for the integral-point results of Conrad's Corollary 5.7, where the base is
`Spec O` for a valuation ring `O`. It contains no new definitions of mathematical objects
beyond the auxiliary constructions listed below.

All names are in the namespace `Langlands.AlgebraicGeometry.AlgebraicSpace.FieldPointEtaleLift`
unless qualified otherwise. `ringTest C A` is the scheme `Spec A` over `Spec C`, and
`ringTestMap C φ` is the morphism induced by a `C`-algebra map `φ`.

## Why the field case does not suffice

The Library proof for `C = k` lets the Galois group of a finite Galois extension `K/k` act
diagonally on the product of a fibre power of a chart with `Spec K`. That product is étale
over the chart because `Spec K → Spec k` is étale. Over `Spec C`, `Spec K` is not étale, so
that construction gives no étale chart. Here the fibre power is instead indexed by the
`k`-embeddings `L → K` of a finite separable extension `L/k`, and the Galois group acts by
permuting the index.

## Definitions

- `fieldTestMap : ringTest C K ⟶ ringTest C k`, the morphism `Spec K → Spec k` over
  `Spec C` for a tower `C → k → K`.
- `galoisAction : OverAction (K ≃ₐ[k] K) (ringTest C K)`, the action of `Gal(K/k)` on
  `Spec K` over `Spec C` by `ringTestMap C g`.
- For a scheme `S`, an algebraic space `X` over `S`, `V : Over S` and
  `a : h_V ⟶ X.presheaf`: `selfPullback a`, the represented fibre product `V ×_X V`, with
  projections `selfFst a`, `selfSnd a`, the lift `selfLift a y₁ y₂ h` of two points with
  equal images, and the diagonal `selfDiag a : V ⟶ V ×_X V`.
- For a fibre power `Y : ChartFibrePower a E` (Library module `ChartFibrePower`):
  - `coordPair Y e e' : Y.obj ⟶ selfPullback a`, the pair of coordinates `e, e'`;
  - `distinctLocus Y`, for `V.hom` separated: the open subscheme of `Y.obj.left` where, for
    every pair `e ≠ e'`, the point `coordPair Y e e'` avoids the image of the diagonal. It is
    open because the diagonal is a closed immersion (`isClosedImmersion_selfDiag`) and `E` is
    finite.
- `embAction Y : OverAction (K ≃ₐ[k] K) Y.obj` for `Y : ChartFibrePower a (L →ₐ[k] K)`,
  the action of `Gal(K/k)` by `act γ ≫ Y.pr e = Y.pr (γ ∘ e)`.
- `resAction ρ U hU`, the restriction of an `OverAction` `ρ` to a stable open `U`, as an
  action on `OverAction.resOver U`.

## Statements

Galois descent (section `Galois`):

- `galoisAction_act_left`, `galoisAction_fieldTestMap`: the action is by
  `Spec (g : K → K)` and commutes with `Spec K → Spec k`.
- `spec_hom_ext`: two morphisms `Spec k ⟶ Z` into an affine scheme agree when they agree
  after composing with `Spec K → Spec k`.
- `exists_desc_of_galois_invariant`: for `K/k` finite Galois and `V` over `Spec C` with
  affine underlying scheme, a `K`-point `w` of `V` with `galoisAction.act σ ≫ w = w` for all
  `σ` is `fieldTestMap ≫ u` for a `k`-point `u`. The ring map `Γ(V) → K` lands in the fixed
  field `k` (`IsGalois.mem_range_algebraMap_iff_fixed`).
- `changeRing_injective`: for a finite extension `K/k`, the map
  `RingPoints.changeRing : X(k) → X(K)` is injective for every algebraic space `X` over
  `Spec C`. `Spec K → Spec k` is flat, locally of finite presentation and surjective, so it
  generates an fppf covering sieve, and `X` is separated for it.

Field-theoretic input (section `Embeddings`):

- `exists_separable_point_mono`: a nonempty scheme `T` étale over `Spec k` has a point
  `Spec L → T` over `Spec k` that is a monomorphism of schemes, with `L/k` finite
  separable. An affine open `Spec A` of `T` has `A` étale over `k`, so `A` is a finite
  product of finite separable field extensions (`Algebra.Etale.iff_exists_algEquiv_prod`).
  The projection to one factor gives a closed immersion `Spec L → Spec A`.
- `exists_faithful_galois`: for `L/k` finite separable there is a finite Galois extension
  `K/k` such that the set of `k`-embeddings `L → K` is finite and nonempty, and `Gal(K/k)`
  acts faithfully on it. `K` is the splitting field of the minimal polynomial `f` of a
  primitive element of `L`; an automorphism fixing all embeddings fixes all roots of `f`,
  which generate `K`.

Diagonals of étale charts (section `Diagonal`):

- `isOpenImmersion_of_section`: a section of an étale morphism of schemes is an open
  immersion (Mathlib `pullback_lift_diagonal_isPullback`).
- `selfPullback_isPullback`, `selfDiag_fst`, `selfDiag_snd`, `eq_selfDiag`: the universal
  property of `V ×_X V`; a point with equal coordinates factors through the diagonal.
- `mono_selfPullback_lift`: the comparison `V ×_X V → V ×_S V` is a monomorphism of schemes.
- `isOpenImmersion_selfDiag`: if `a` is étale, the diagonal is an open immersion (it is a
  section of the étale projection `selfFst a`).
- `isClosedImmersion_selfDiag`: if `V.hom` is separated, the diagonal is a closed immersion
  (its composite with `selfFst a` is the identity, and `selfFst a` is separated because it
  factors through the monomorphism above and the separated projection of `V ×_S V`).

The distinct locus (section `Distinct`):

- `coordPair_fst`, `coordPair_snd`, `mem_distinctLocus`.
- `ne_of_mem_distinctLocus`: if a morphism `b : T ⟶ Y.obj` from a scheme with a nonempty
  underlying space lands in the distinct locus, then `b ≫ Y.pr e ≠ b ≫ Y.pr e'` for
  `e ≠ e'`.
- `mem_distinctLocus_of_ne`: conversely, if `a` is étale, `T` has at most one point and
  `b ≫ Y.pr e ≠ b ≫ Y.pr e'` for all `e ≠ e'`, then `b` lands in the distinct locus. Here
  the diagonal is open, so a one-point morphism into its image factors through it.

Actions (section `Actions`): `one_comp_emb`, `mul_comp_emb`, `embAction_pr`,
`resAction_ι`.

Main result (section `Lift`):

- `exists_affine_etale_point (X : AlgebraicSpace (Spec (CommRingCat.of C)))
  (x : RingPoints C X k)`: there are `U : Over (Spec (CommRingCat.of C))` with `U.left`
  affine, a morphism of algebraic spaces `f : (schemeToSpace _).obj U ⟶ X` whose
  underlying transformation `hom f` is étale (`AlgebraicSpace.IsEtale`), and a point
  `u : RingPoint C U k` with
  `RingPoints.map f ((schemeRingPointsEquiv C U k).symm u) = x`.

## Proof of `exists_affine_etale_point`

Let `x̂ = uliftYonedaEquiv.symm x : h_{Spec k} ⟶ X.presheaf`.

1. Take an atlas `a₀ : h_{U₀} ⟶ X.presheaf` (`X.exists_atlas`), étale and surjective. Its
   represented pullback `P` along `x̂` has étale surjective projection `p : P ⟶ Spec k`.
   So `P`, viewed over `Spec k`, is a nonempty étale `k`-scheme.
2. `exists_separable_point_mono` gives `L/k` finite separable and a monomorphism
   `w₀ : Spec L → P` over `Spec k`. `exists_faithful_galois` gives `K/k` finite Galois
   with `E = (L →ₐ[k] K)` finite, nonempty, and acted on faithfully by `Gal(K/k)`. All
   fields get the `C`-algebra structures induced from `k`.
3. Let `v₁ : Spec L → U₀` be the image of `w₀` in the atlas. Choose an affine open `O` of
   `U₀` containing its point and factor `v₁` through `O` as `ℓ`. The chart
   `a = h(O ↪ U₀) ≫ a₀ : h_O ⟶ X.presheaf` is étale, and `O` is affine, hence separated
   over `Spec C`.
4. For `e ∈ E`, `vE e = ringTestMap C e ≫ ℓ : Spec K → O`. All have image
   `h(fieldTestMap) ≫ x̂` in `X` (`hvE`). The map `e ↦ vE e` is injective (`hvinj`):
   equal points give equal points of `P` by the pullback property, then `e = e'` because
   `w₀` is a monomorphism and `Spec` is faithful.
5. `ChartFibrePower.exists_of_finite` gives the `E`-fold fibre power `Y` of `a`, separated
   over `Spec C` with étale projections. `embAction` makes `Gal(K/k)` act on it. The family
   `vE` defines `y : Spec K → Y` with `y ≫ Y.pr e = vE e`, and `y` is equivariant:
   `y ≫ ρ.act γ = galoisAction.act γ ≫ y` (`hyeq`).
6. `W = ρ.orbitInf (distinctLocus Y)` is the largest stable open inside the distinct locus
   (Library `OverAction.orbitInf`). The action restricts to `τ` on `W`
   (`resAction`). It is free (`hfree`): if `b ≫ τ.act g = b ≫ τ.act h` for a morphism `b`
   from a nonempty scheme, then by `ne_of_mem_distinctLocus` the embeddings `g ∘ e` and
   `h ∘ e` agree for every `e`, so `g⁻¹ h` fixes every embedding and equals `1` by
   faithfulness. `W` is separated over `Spec C`, hence separated as a scheme.
7. The map `t = h(W ↪ Y) ≫ h(Y.pr e₀) ≫ a` is étale and `τ`-invariant (`ht`, `hinv`;
   invariance uses `Y.w`, which says all projections have the same image in `X`).
8. `y` lands in `W` (`hyW`): for every `g`, `y ≫ ρ.act g` has pairwise distinct coordinates
   `g ∘ vE e` by step 4, so it lies in the distinct locus by `mem_distinctLocus_of_ne`.
   Hence `y` factors through `W` as an equivariant `z : Spec K → W` (`hz`, `hzeq`).
9. `OverAction.exists_affine_chart_of_point` (Library module `OverActionQuotientChart`),
   applied to the free action `τ`, the free one-point action `galoisAction`, the invariant
   étale `t` and the equivariant `z`, gives `M` over `Spec C` with `M.left` affine, an étale
   `tM : h_M ⟶ X.presheaf`, and a Galois-invariant `w : Spec K → M` with
   `h(w) ≫ tM = h(z) ≫ t`. The right side equals `h(fieldTestMap) ≫ x̂` (`hfinal`).
10. `exists_desc_of_galois_invariant` descends `w` to `u : Spec k → M`. Take `U = M`,
    `f = AlgebraicSpace.homMk tM` and the point `u`. By `changeRing_injective` it is
    enough to compare the images in `X(K)`. Through `uliftYonedaEquiv` and
    `uliftYonedaEquiv_naturality` these are `h(w) ≫ tM` and `h(fieldTestMap) ≫ x̂`, which
    agree by step 9.

The proof uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`.

## Sources

- Conrad, registered source `conrad-2011-weil-grothendieck-adelic-points`, printed page 15,
  proof of Proposition 5.4: the citation of Knutson II.6.4 for lifting `k`-points of `X` to
  `k`-points of étale scheme charts.
- Stacks Project, chapter "Decent Algebraic Spaces", Lemma 11.4 (Tag 0BBP), in the
  registered copy `Stacks Project - Decent Algebraic Spaces, full chapter PDF (version
  ed88ff78)`, for comparison only.

The route of the Lean proof (embeddings-indexed fibre power, distinct locus, quotient
chart) is the author's own. It adapts the Library proof of the case `C = k`.
