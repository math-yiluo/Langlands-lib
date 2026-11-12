# Stabilizer fibres are equidimensional: proof

Authors: Worker 5139, with Worker 79 (the finite-type argument, see below).

Proof of `Langlands.AlgebraicGeometry.AlgebraicSpace.StabilizerFibreLocalDimensionStatement.{u}`
(Stacks Project, Lemma 39.8.1, Tag 045X, for the fibres of the stabilizer scheme). The
theorem is `Langlands.AlgebraicGeometry.AlgebraicSpace.stabilizerFibreLocalDimension`.
Let `G` be a group scheme locally of finite type over `S`, acting by `a` on `V`, and let
`σ` be the projection of the stabilizer scheme to `V`. For every point `x` of the
stabilizer scheme,
`relativeTopologicalKrullDimAt σ.left x = topologicalKrullDim (σ.left.fiber (σ.left x))`.

The Lean proof does not follow Stacks' proof, which uses the group structure of the
stabilizer of `v` over `κ(v)` and the dimension theory of group schemes over a field.
Instead it compares any two points of one fibre of `σ` directly by a translation
automorphism of a base change of the stabilizer scheme. No group structure on the
stabilizer scheme is constructed. The only inputs are the Library's invariance of
relative local dimension under base change and elementary facts about the local
topological dimension.

Helper declarations are in the namespace
`Langlands.AlgebraicGeometry.AlgebraicSpace.StabilizerFibre`. Products are fibre products
over `S`, that is, products in `Over S`.

## Definitions and elementary lemmas

- `Stab a : Over S` is the stabilizer scheme
  `pullback (lift a.hom (snd G.X V)) (lift (𝟙 V) (𝟙 V))`, and `proj a : Stab a ⟶ V` is
  its projection `pullback.snd …`. These are `abbrev`s, so `(proj a).left` is
  syntactically the morphism `σ.left` of the statement.
- For `q : T ⟶ Stab a`, `group a q : T ⟶ G.X` is its group component (the first
  pullback projection followed by `fst G.X V`). `group_comp` says
  `group a (b ≫ q) = b ≫ group a q`.
- `comp_pullback_fst`: the point of `G × V` underlying `q` is
  `lift (group a q) (q ≫ proj a)`. It is proved from the second component of the
  pullback condition.
- `act_group`: `a.act (group a q) (q ≫ proj a) = q ≫ proj a`, the first component of the
  pullback condition (`SchemeAction.act` is `lift g n ≫ a.hom`).
- `mk a g n h : T ⟶ Stab a` is the point given by `g : T ⟶ G.X` and `n : T ⟶ V` with
  `h : a.act g n = n`. `mk_proj` and `group_mk` compute its two components, and
  `hom_ext` says that points of `Stab a` with equal group components and equal images in
  `V` are equal.
- `act_inv_of_act`: if `a.act h t = t` then `a.act h⁻¹ t = t`. This follows from
  `SchemeAction.act_mul`, `inv_mul_cancel` and `SchemeAction.act_one`. Here `h⁻¹` and
  products of `T`-points of `G.X` are Mathlib's group structure on `T ⟶ G.X` (`GrpObj`).
- `relativeTopologicalKrullDimAt_of_subsingleton`: if `Y` has at most one point, then
  `relativeTopologicalKrullDimAt f x = topologicalKrullDimAt x`. By
  `relativeTopologicalKrullDimAt_eq_preimage_singleton` the left side is the local
  dimension at `x` of `f ⁻¹' {f x}`, which is all of `X`; then
  `topologicalKrullDimAt_homeomorph` applies to the homeomorphism of this set with `X`.

## Translation on a base change of the stabilizer

Fix `W : Over S` and `t : W ⟶ V`, and let `P = pullback (proj a) t`, the base change of
the stabilizer scheme along `t`. Let `h : W ⟶ G.X` with `hh : a.act h t = t`.

- `translate a t h hh : P ⟶ P` is left translation by `h`. On a point `(q, w)` of `P` it
  is `(h(w) · group(q), w)`: its first component is
  `mk a ((pullback.snd ≫ h) * group a pullback.fst) (pullback.fst ≫ proj a) _`, and its
  second component is `pullback.snd`. The new group component fixes the image in `V`
  because of `SchemeAction.act_mul`, `act_group`, the pullback condition
  `pullback.fst ≫ proj a = pullback.snd ≫ t`, `SchemeAction.naturality` and `hh`.
  The lemmas `translate_fst` and `translate_snd` record the two components.
- `translate_comp`: `translate h ≫ translate h' = translate (h' * h)`. This is checked
  with `pullback.hom_ext` and `hom_ext`, using `MonObj.comp_mul` and associativity.
- `translate_eq_id`: translation by `1` is the identity (`MonObj.comp_one`, `one_mul`).
- `translateIso a t h hh : P ≅ P` has `hom = translate h` and
  `inv = translate h⁻¹`. The two composites are translations by `h⁻¹ * h` and
  `h * h⁻¹`, which are the identity by `translate_comp` and `translate_eq_id`.

## Main lemma: two points of one fibre have the same local dimension

`relativeTopologicalKrullDimAt_eq_of_proj_eq`: assume `(proj a).left` is locally of
finite type. If `x` and `y` are points of the stabilizer scheme with
`(proj a).left x = (proj a).left y`, then
`relativeTopologicalKrullDimAt (proj a).left x = relativeTopologicalKrullDimAt (proj a).left y`.

1. `Scheme.Pullback.exists_preimage_pullback` gives a point `z` of the scheme
   `pullback (proj a).left (proj a).left` over `x` and `y`. Let
   `p0 : Spec κ(z) ⟶ pullback …` be `fromSpecResidueField z`, and let `px`, `py` be `p0`
   followed by the two projections. Then `px ≫ σ = py ≫ σ`.
2. Make `W = Spec κ(z)` an object of `Over S` through `px`. Then `px` and `py` give
   morphisms `qx qy : W ⟶ Stab a` in `Over S` with `qx ≫ proj a = qy ≫ proj a`. Let
   `t = qx ≫ proj a`.
3. `act_group` for `qx` and for `qy` gives `a.act (group a qx) t = t` and
   `a.act (group a qy) t = t`. So `h = group a qx * (group a qy)⁻¹` fixes `t`, by
   `SchemeAction.act_mul` and `act_inv_of_act`.
4. Let `sx = pullback.lift qx (𝟙 W)` and `sy = pullback.lift qy (𝟙 W)`, sections of
   `P = pullback (proj a) t → W`. Then `sy ≫ translate a t h _ = sx`. On group components
   this is `(group qx * (group qy)⁻¹) * group qy = group qx` (`inv_mul_cancel_right`); on
   images in `V` it is `qy ≫ proj a = qx ≫ proj a`; on the `W` component both sides are
   `𝟙 W`.
5. The square formed by `pullback.fst`, `pullback.snd`, `proj a` and `t` is a pullback
   in `Over S`, and it stays a pullback of schemes after `Over.forget S`
   (`IsPullback.map`). `W.left = Spec κ(z)` has exactly one point. For any section
   `s : W ⟶ P` and point `w`,
   `relativeTopologicalKrullDimAt (proj a).left (pullback.fst.left (s.left w)) =
   topologicalKrullDimAt (s.left w)`. The Library's `relativeTopologicalKrullDimAt_baseChange`
   (`Langlands/AlgebraicGeometry/SchemeLocalDimensionBaseChangeProof.lean`, which needs
   `LocallyOfFiniteType (proj a).left`) turns the left side into the relative dimension
   of `pullback.snd.left : P.left → W.left` at `s.left w`. Then
   `relativeTopologicalKrullDimAt_of_subsingleton` applies.
6. Let `w0` be the closed point of `W.left`. Then `pullback.fst.left (sx.left w0) = x` and
   `pullback.fst.left (sy.left w0) = y`, by `Scheme.fromSpecResidueField_apply` and the
   choice of `z`. Also `(translate …).left (sy.left w0) = sx.left w0` by step 4.
   So both sides of the lemma are local dimensions of `P.left` at `sx.left w0` and at
   `sy.left w0`. They agree by `topologicalKrullDimAt_homeomorph` applied to the
   homeomorphism of `P.left` underlying the isomorphism
   `(Over.forget S).mapIso (translateIso a t h _)` (`Scheme.homeoOfIso`).

## The finite-type hypothesis

`locallyOfFiniteType_proj`: if `G.X.hom` is locally of finite type, so is
`(proj a).left`. The projection `(snd G.X V).left` is a base change of `G.X.hom`, so it
is locally of finite type. It factors as the action graph `lift a.hom (snd G.X V)`
followed by `snd V V`, so the action graph is locally of finite type
(`locallyOfFiniteType_of_comp`). Then `(proj a).left` is, up to the isomorphism
`PreservesPullback.iso (Over.forget S)`, the scheme-level pullback of the action graph
along the diagonal, and base change preserves the property. The Lean proof is Worker 79's
lemma `locallyOfFiniteType_stabilizer` from their public draft for Task 5217
(`UnipotentOrbitStratumAssemblyDraft.lean`), restated for `proj a`.

## Proof of the target

`stabilizerFibreLocalDimension`: given `S`, `G`, `V`, `a`, `hG` and `x`, the morphism
`σ.left` is locally of finite type by `locallyOfFiniteType_proj`. By definition the left
side is `topologicalKrullDimAt (σ.left.asFiber x)`, a local dimension of the fibre over
`σ.left x`, so the inequality `≤` is `topologicalKrullDimAt_le`. For `≥`, rewrite `topologicalKrullDim` of the fibre as
`⨆ p, topologicalKrullDimAt p` (`topologicalKrullDim_eq_iSup_at`). For each point `p` of
the fibre over `σ.left x`, `relativeTopologicalKrullDimAt_fiberι` identifies
`topologicalKrullDimAt p` with the relative dimension of `σ.left` at the image of `p` in
the stabilizer scheme. That image lies over `σ.left x` (`fiberHomeo`), so the main lemma
makes its relative dimension equal to that at `x`. Hence every term of the supremum is
at most the left side.

The theorem uses only the axioms `propext`, `Classical.choice` and `Quot.sound`.
