# The stalk tower of the closed-fibre representing schemes

Module `Langlands.AlgebraicGeometry.UnramifiedFunctor.MurreCompleteFibre`, namespace
`Langlands.AlgebraicGeometry.UnramifiedFunctor.CompleteLocal`. A supporting module of the proof
of Step 2a of Murre's induction (`MurreCompleteLocalStepStatement`, Bourbaki exp. 294, Case I,
Step 2a). In that step `F` is represented over each `Spec (R/m^(k+1))` by a scheme `Y k`. This
module builds, for a point `y` of `Y 0`, the tower of local rings `B_k = 𝒪_{Y k, y_k}`, its
elements of `F` and its surjective transition maps. `MurreCompleteChart` takes the inverse limit
`B_y` of this tower.

## Level: stalks of a representing scheme (section `Level`)

Let `π : T₀ ⟶ Spec R` be a monomorphism, `q : Y ⟶ T₀`, and
`e : (baseChange π F).RepresentableBy (Over.mk q)`. For `y : Y`:

* `LevelRing π q y` is the stalk `𝒪_{Y,y}`, a local ring. Its `R`-algebra structure comes from
  `levelHom`, a ring map `R → 𝒪_{Y,y}` with spectrum
  `Spec 𝒪_{Y,y} ⟶ Y ⟶ T₀ ⟶ Spec R` (`spec_levelHom`). `levelJ` is
  `Spec 𝒪_{Y,y} ⟶ Y`.
* `levelElem π q y e ∈ F(Spec 𝒪_{Y,y})` is the element classified by `levelJ`.
* `map_levelElem`: restricting `levelElem` along `ψ : 𝒪_{Y,y} →ₐ[R] A` gives the element
  classified by `Spec ψ ≫ levelJ`.
* `exists_levelElem`: take a local `R`-algebra `A` lying over `T₀` and `η ∈ F(Spec A)` whose
  classifying morphism sends the closed point to a generization of `y`. Then `η` is a restriction
  of `levelElem`. The proof factors the classifying morphism through `Spec 𝒪_{Y,y}`
  (`Charts.exists_comp_fromSpecStalk`).
* `levelElem_injective`: two `R`-algebra maps out of `𝒪_{Y,y}` that restrict `levelElem` to the
  same element are equal. The proof uses `elemEquiv`, the fact that `levelJ` is a monomorphism,
  and faithfulness of `Spec`.
* `levelHom_eq`, `formallyUnramified_level`, `essFiniteType_level`: if `q` and `π` are formally
  unramified (resp. locally of finite type), then `𝒪_{Y,y}` is formally unramified (resp.
  essentially of finite type) over `R`.

## Classifying morphisms (sections `Change`, `Cls`)

`elemEquiv_naturality'` is the Library's `elemEquiv_naturality`, with compatibility of the
factorizations assumed in place of `Mono g`. For `T` lying over `S'` through `t`:

* `cls` is the classifying morphism `T.left ⟶ Y` of an element of `F(T)`, and `mkElem` is the
  inverse construction. The two are mutually inverse (`cls_mkElem`, `mkElem_cls`,
  `eq_of_cls_eq`) and compatible with restriction (`map_mkElem`, `cls_map`).
* `univ`, `univHom` and `eq_map_univ`: every element is a restriction of the universal element.
* `changeMap`: given two monomorphisms `T₁ ⟶ Spec R` and `T₂ ⟶ Spec R` with `T₁` over `T₂`, this
  is the morphism `Y₁ ⟶ Y₂` of representing schemes. `cls_changeMap` says it composes
  classifying morphisms.

These lemmas are typed by `T.left ⟶ Y`. That avoids comparing objects `Over.mk t` at different
levels, which made the kernel time out.

## The tower (section `Tower`)

Let `R` be local and `Y k` represent `F` over `Spec (R/m^(k+1))` through `q k` and `e k`.

* `levelMap hkl` is the closed immersion `Spec (R/m^(k+1)) ⟶ Spec (R/m^(l+1))` for `k ≤ l`.
  `towerMap e hkl : Y k ⟶ Y l` is the corresponding `changeMap`. It is a monomorphism, and
  composition and identities are respected (`towerMap_comp`, `towerMap_refl`).
* `pt e y k` is the image of `y` in `Y k`, `Bk e y k = 𝒪_{Y k, pt e y k}`, and `ξk e y k` is its
  element of `F`.
* `transition e y k : Bk e y (k+1) →ₐ[R] Bk e y k` is obtained from `exists_levelElem`
  (`exists_transition`). It restricts `ξk (k+1)` to `ξk k` (`map_transition`).
* `transition_surjective` and `transition_ker`: the transition is surjective with kernel
  `transIdeal = m^(k+1) · Bk (k+1)`. The proof first restricts `ξk (k+1)` to the quotient
  `TransQ = Bk (k+1) / m^(k+1)`, giving `ηQ`. Its classifying morphism sends the closed point to
  `pt k`, by injectivity of `towerMap` (`cls_ηQ_closedPoint`). So `exists_levelElem` gives
  `σ : Bk k → TransQ` (`exists_transInv`). Then `σ` and the map `transBar : TransQ → Bk k`
  induced by `transition` are mutually inverse; both identities come from `levelElem_injective`
  (`transBar_comp_transInv`, `transInv_comp_transBar`). `transition_ker_linear` restates the
  kernel as the `R`-submodule `m^(k+1) • ⊤`.
* The instances say that `maximalIdealPowQuotientMap R k` is formally unramified and locally of
  finite type, being a closed immersion.

## Level zero (section `Zero`)

Assume every `q k` is formally unramified and locally of finite type.

* `Bk_formallyUnramified`, `Bk_essFiniteType`: from the `Level` section.
* `Bk_isLocalHom`: `R → Bk k` is local, because `m^(k+1)` maps to zero
  (`algebraMap_Bk_eq_zero`).
* `B0_isField`: `Bk 0` is a field. Its maximal ideal is the image of `m`
  (`Algebra.FormallyUnramified.map_maximalIdeal`), and `m` maps to zero.
* `B0_finite`: `Bk 0` is finite over `R`. It is isomorphic to its residue field, which is finite
  over the residue field of `R` (Mathlib's instance for formally unramified local algebras
  essentially of finite type).

The Spec identity `ArtinianBase.homR_id` is imported from `ArtinianBaseTools` and reused for the transition maps.
