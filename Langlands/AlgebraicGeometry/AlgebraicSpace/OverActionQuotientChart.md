# Affine étale charts from finite group actions with a fixed point

Internal infrastructure for the proof of `RationalPointEtaleLiftStatement` (Knutson,
*Algebraic Spaces*, II.6.4; Stacks Project, Tag 0BBP). This module carries out the
quotient step of the Galois-descent argument. A finite group `G` acts on a separated scheme
`Z` over `S` with an invariant étale map `t` to an algebraic space, and a one-point scheme
`Λ` maps equivariantly to `Z`. Then a `G`-stable affine neighbourhood of the image point
has an affine quotient. The quotient carries an étale map to the space and an invariant
point. The module also supplies the diagonal action on a fibre product and the Galois action
on `Spec K`. These are standard constructions, not a specific statement from the
literature.

Throughout, `S` is a scheme, and names are in the namespace
`Langlands.AlgebraicGeometry.AlgebraicSpace` (mostly in `OverAction`).

## Definitions

- `OverAction G Y`, for a group `G` and `Y : Over S`, is an action by morphisms over `S`:
  `act : G → (Y ⟶ Y)` with `act 1 = 𝟙 Y` and `act g ≫ act h = act (g * h)`. Since
  composition is written in diagrammatic order, this is a right action in the usual
  notation. Each `(act g).left` is an isomorphism (instance), with inverse
  `(act g⁻¹).left`.
- `OverAction.IsFree ρ`: for every nonempty scheme `T` and every `a : T ⟶ Y.left`, the map
  `g ↦ a ≫ (ρ.act g).left` is injective.
- `prodOver Y Λ` is the fibre product over `S`; its underlying scheme is
  `pullback Y.hom Λ.hom`. It comes with `prodFst`, `prodSnd`, `prodLift` and
  `prod_hom_ext`. `prodFst` is étale when `Λ.hom` is (instance).
- `ρ.prod σ` is the diagonal action on `prodOver Y Λ`, with `prod_act_fst` and
  `prod_act_snd`.
- For finite `G` and `τ : OverAction G Z`, `τ.orbitInf U = ⨅ g, (τ.act g).left ⁻¹ᵁ U` is
  the intersection of the translates of an open `U` of `Z.left`.
- `resOver U : Over S` is an open `U` of `Z.left` over `S`, and `resOverι U` is its
  inclusion. For a stable open (`hU : ∀ g, (τ.act g).left ⁻¹ᵁ U = U`), `τ.resAct U hU g` is
  the restricted action. If `τ` is free, `τ.restrict U hU hfree` is this action packaged as
  a Library `FiniteFreeSchemeAction G (resOver U).left`.
- `galoisAction : OverAction (K ≃ₐ[k] K) (specOver k K)` is the Galois group of a field
  extension `K/k` acting on `Spec K` over `Spec k` by `g ↦ specOverMap g.toAlgHom`.

## Statements

- `prod_isFree`: if `σ` is free, so is `ρ.prod σ`.
- `mem_orbitInf`, `preimage_orbitInf`: `x ∈ τ.orbitInf U` iff every translate of `x` lies in
  `U`, and `τ.orbitInf U` is stable under every `(τ.act h).left`.
- `isAffineOpen_orbitInf`: if `Z.left` is separated and `U` is an affine open, then
  `τ.orbitInf U` is an affine open.
- `resAct_ι`, `resAct_one`, `resAct_mul`, `restrict_act_hom`, `restrict_over`,
  `actOver_resOverι`: compatibility of the restricted action with the inclusion and with the
  structure morphism to `S`.
- `exists_quotient_chart`: let `G` be finite, `X` an algebraic space over `S`, `τ` a free
  action on `Z`, and `U` a stable open with `(resOver U).left` affine. Let
  `t : h_Z ⟶ X.presheaf` be étale with `h(τ.act g) ≫ t = t` for all `g`. Then there are
  `M : Over S` with `M.left` affine, a morphism `q : resOver U ⟶ M` invariant under the
  restricted action, and an étale `tM : h_M ⟶ X.presheaf` with
  `h(q) ≫ tM = h(resOverι U) ≫ t`.
- `exists_affine_chart_of_point`: let `G` be finite, `X` an algebraic space over `S`, `τ` a
  free action on `Z` with `Z.left` separated, and `σ` an action on `Λ` with `Λ.left`
  nonempty and with at most one point. Let `t : h_Z ⟶ X.presheaf` be étale and invariant
  under `τ`, and let `z : Λ ⟶ Z` satisfy `z ≫ τ.act g = σ.act g ≫ z`. Then there are
  `M : Over S` with `M.left` affine, an étale `tM : h_M ⟶ X.presheaf`, and `w : Λ ⟶ M`
  with `σ.act g ≫ w = w` for all `g` and `h(w) ≫ tM = h(z) ≫ t`.
- `galoisAction_act`: `galoisAction.act g = specOverMap g.toAlgHom`.
- `galoisAction_isFree`: the Galois action on `Spec K` is free.
- Instances: `(specOver k K).left` is nonempty and has at most one point, and
  `(specOver k K).hom` is étale when `K/k` is finite and separable.

## Proofs

- `prod_isFree`: compose with the second projection, which intertwines the diagonal action
  with `σ`, and use freeness of `σ`.
- `isAffineOpen_orbitInf`: each translate `(τ.act g).left ⁻¹ᵁ U` is affine because
  `(τ.act g).left` is an isomorphism. A finite intersection of affine opens in a separated
  scheme is affine (Mathlib's `IsAffineOpen.iInf`).
- `restrict`: `resAct` is `Scheme.Hom.resLE`. The group laws and freeness follow by
  cancelling the monomorphism `U.ι`.
- `exists_quotient_chart`: the restricted action has the Library affine quotient
  `(τ.restrict U hU hfree).quotient`. The map `h(resOverι U) ≫ t` is invariant, so it
  descends to `tM` on the quotient (`FiniteActionChart.exists_desc`). `tM` is étale by
  `isEtale_of_finiteEtale_comp`, because the quotient map is finite étale surjective and
  `h(resOverι U) ≫ t` is étale (`isEtale_map` and `IsEtale.comp`). The quotient map is
  invariant (`AffineQuotient.invariant`).
- `exists_affine_chart_of_point`: let `y` be the point of `Λ.left`. Since `Λ.left` has at
  most one point, the image `z(y)` is fixed by `G`. Choose an affine open `U₀` containing
  it. Then `U = τ.orbitInf U₀` is a stable affine open containing `z(y)`. Apply
  `exists_quotient_chart` to `U`. The map `z` factors through `U`
  (`IsOpenImmersion.lift`), and composing with `q` gives `w`. Invariance of `w` comes from
  equivariance of `z` and invariance of `q`. The equation for `tM` comes from the
  factorization of `t`.
- `galoisAction`: `one` is `specMap_id`, and `mul` is `specMap_comp`.
- `galoisAction_isFree`: if `a ≫ Spec g = a ≫ Spec h` for some `a : T ⟶ Spec K` with `T`
  nonempty, compose with the residue-field point of some `x ∈ T`. The two resulting ring
  maps `K → κ(x)` agree. Since `K → κ(x)` is an injective ring map of fields, `g = h`.
- The étale instance: a finite separable extension is formally étale and of finite
  presentation, hence étale, and `Spec` of an étale algebra map is étale.
