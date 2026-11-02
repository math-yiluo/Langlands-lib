# fppf descent of loci cut out by immersions

Authors: Worker 766 and Worker 266. Worker 766 wrote the Lean proof and the
first version of this Markdown. Worker 266 checked both against the required
theorem type, the Lean code and the source, and revised the Markdown.

This module proves the theorem
`Langlands.AlgebraicGeometry.fppfImmersionLocusDescent`. It is the analogue of
`Langlands.AlgebraicGeometry.FppfClosedLocusDescentStatement` (see
`FppfClosedLocusDescentStatement.md`) with immersions in place of closed
immersions. It is not the proof of a separate Library statement. It is a
corollary of `fppfClosedLocusDescent`, which is proved in
`FppfClosedLocusDescentProof.lean`.

## Statement

```lean
theorem fppfImmersionLocusDescent (Y : Scheme.{u}) (E : Sieve Y)
    (hE : Scheme.fppfTopology.IsClosed E) (R : Sieve Y) (hR : R ∈ Scheme.fppfTopology Y)
    (h : ∀ ⦃Y' : Scheme.{u}⦄ (f : Y' ⟶ Y), R f →
      ∃ (Z : Scheme.{u}) (ι : Z ⟶ Y'), IsImmersion ι ∧
        ∀ ⦃T : Scheme.{u}⦄ (g : T ⟶ Y'), (∃ k : T ⟶ Z, k ≫ ι = g) ↔ E (g ≫ f)) :
    ∃ (Z : Scheme.{u}) (ι : Z ⟶ Y), IsImmersion ι ∧
      ∀ ⦃T : Scheme.{u}⦄ (g : T ⟶ Y), (∃ k : T ⟶ Z, k ≫ ι = g) ↔ E g
```

In words: let `E` be a sieve on a scheme `Y` that is closed for the fppf
topology, and let `R` be an fppf covering sieve of `Y`. Suppose that on every
member `f : Y' ⟶ Y` of `R`, an immersion `ι : Z ⟶ Y'` cuts out the pullback of
`E`. That is, a morphism `g : T ⟶ Y'` factors through `ι` exactly when
`E (g ≫ f)`. Then a single immersion `ι : Z ⟶ Y` cuts out `E`: a morphism
`g : T ⟶ Y` factors through `ι` exactly when `E g`. All schemes lie in the same
universe `u`. `IsImmersion` is Mathlib's `AlgebraicGeometry.IsImmersion`. The
binders are those of `FppfClosedLocusDescentStatement`, with `IsImmersion` in
place of `IsClosedImmersion` in the hypothesis and in the conclusion. The
meaning of fppf-closedness and of the covering sieve is explained in
`FppfClosedLocusDescentStatement.md`.

## Provenance

The result is the subfunctor form of Stacks Project, *Descent*, Lemma 35.24.1
(Tag 02YM), PDF pp.60-61 (source `stacks-descent-ed88ff78-2026`): the property
"`f` is an immersion" is fppf local on the base. As in
`FppfClosedLocusDescentStatement.md`, no descent datum is supplied, because the
sieve `E` determines the local pieces. The Lean proof follows the idea of the
proof of Tag 02YM (PDF p.61). In that proof $f : X \to S$ is a morphism and
$\pi : S' \to S$ is a surjective flat morphism of affine schemes, locally of
finite presentation, such that the base change $f' : X' \to S'$ is an
immersion. Then $\pi$ is open, and $f'(X') = \pi^{-1}(f(X))$ is locally closed,
so $f(X)$ is locally closed (Topology, Lemma 6.4, as cited there). Let
$Z = \overline{f(X)} \setminus f(X)$. Then $f'(X')$ is closed in $S' \setminus Z'$,
and Lemma 35.23.21 (Tag 02L6) applied to $\{S' \setminus Z' \to S \setminus Z\}$
shows that $f$ is a closed immersion into $S \setminus Z$. The Lean proof makes
the same argument with these differences. It does not reduce to a single
morphism of affine schemes. It works with all members of a cover `𝒰` of `Y` by
flat morphisms locally of finite presentation whose arrows lie in `R`, and shows
directly that the set `S ⊆ Y` of points under the local immersions has open
coborder, the complement of `closure S \ S`. The descent step over this open set
is `fppfClosedLocusDescent`, the subfunctor form of Tag 03I0, in place of
Lemma 35.23.21. No code is copied from another project.

The module imports `Langlands.AlgebraicGeometry.Descent.FppfClosedLocusDescentProof`
and the Mathlib module `AlgebraicGeometry.Morphisms.Immersion`.

## Proof outline

### 1. Points under the local pieces (`mem_range_of_mem_range`)

This lemma lives in the namespace
`Langlands.AlgebraicGeometry.FppfClosedLocusDescent`. Let `fₖ : Yₖ ⟶ Y` and
`ιₖ : Zₖ ⟶ Yₖ` for `k = 1, 2` be morphisms such that `g : T ⟶ Yₖ` factors through
`ιₖ` exactly when `E (g ≫ fₖ)`. No immersion hypothesis is needed. If
`f₁ y₁ = f₂ y₂` and `y₁` lies in the image of `ι₁`, then `y₂` lies in the image
of `ι₂`.

*Proof.* `Scheme.Pullback.exists_preimage_pullback` gives a point `w` of
`Y₁ ×_Y Y₂` over `y₁` and `y₂`. By `Scheme.Pullback.range_snd`, `w` comes from
a point `v` of `P = Z₁ ×_{Y₁} (Y₁ ×_Y Y₂)`. Let `q : P ⟶ Y₂` be the projection
to `Y₁ ×_Y Y₂` followed by the second projection. By the two pullback squares,
`q ≫ f₂` equals the projection `P ⟶ Z₁` followed by `ι₁ ≫ f₁`, which lies in
`E` because the projection followed by `ι₁` factors through `ι₁`. So `q`
factors through `ι₂` by some `k`, and `ι₂ (k v) = q v = y₂`.

### 2. The theorem (`fppfImmersionLocusDescent`)

Choose for every member `f` of `R` the immersion `ι f : Z f ⟶ Y'` of the
hypothesis.

1. *The set `S`.* Let `S ⊆ Y` be the set of points `f (ι f z)` for all members
   `f` of `R` and all points `z`. By step 1, `f ⁻¹' S` is the image of `ι f` for
   every member `f`.
2. *A cover.* `Scheme.mem_grothendieckTopology_iff`, for the morphism property
   `@Flat ⊓ @LocallyOfFinitePresentation`, gives a cover `𝒰` of `Y` by flat
   morphisms locally of finite presentation whose arrows lie in `R`. As in
   `FppfClosedLocusDescentProof.lean`, the proof supplies the instance
   `IsMultiplicative` for this property by hand. Each `𝒰.f i` is an open map
   (`Scheme.Hom.isOpenMap`, using the instance `UniversallyOpen` of flat
   morphisms locally of finite presentation).
3. *`S` is locally closed.* The coborder of `S` (Mathlib `coborder`, the
   complement of `closure S \ S`) is the union of the images of its preimages
   under the `𝒰.f i`, since `𝒰` is jointly surjective. For an open continuous
   map, the preimage of the coborder is the coborder of the preimage
   (`coborder_preimage`). The preimage of `S` under `𝒰.f i` is the image of an
   immersion, which is locally closed (`Scheme.Hom.isLocallyClosed_range`), so its
   coborder is open (`IsLocallyClosed.isOpen_coborder`). Images of open sets
   under the open maps `𝒰.f i` are open. Hence `W = coborder S` is an open
   subscheme of `Y`.
4. *`S` is closed in `W`.* A point of `W` in the closure of `S` lies in `S`
   (`mem_coborder_iff_imp`). So the preimage of `S` in `W` is the preimage of
   `closure S`, which is closed.
5. *Closed pieces over `W`.* Apply `fppfClosedLocusDescent` to `W`, the sieve
   `E.pullback W.ι` (closed by `GrothendieckTopology.isClosed_pullback`) and the
   covering sieve `R.pullback W.ι` (by `pullback_stable`). For a member `f` of
   `R.pullback W.ι`, the composite `f ≫ W.ι` lies in `R`. The immersion
   `ι (f ≫ W.ι)` has image `(f ≫ W.ι) ⁻¹' S = f ⁻¹' (W.ι ⁻¹' S)`, which is closed
   by step 4. An immersion with closed image is a closed immersion
   (`IsClosedImmersion.of_isPreimmersion`). It cuts out the pullback of
   `E.pullback W.ι` along `f`. This gives a closed immersion `ι₀ : Z₀ ⟶ W` that
   cuts out `E.pullback W.ι`.
6. *Conclusion.* The required immersion is `ι₀ ≫ W.ι`. If `g` factors through it,
   then `g` factors through `W.ι` by a morphism in `E.pullback W.ι`, so `E g`.
   Conversely let `E g` with `g : T ⟶ Y`. Every point `t` of `T` maps into `W`:
   choose `i` and `y` with `𝒰.f i y = g t`, and a point `w` of `T ×_Y 𝒰.X i` over
   `t` and `y`. The second projection lies in the pullback of `E` along `𝒰.f i`,
   since `E` is a sieve, so it factors through `ι (𝒰.f i)` by some `k`. Then
   `g t = 𝒰.f i (ι (𝒰.f i) (k w))` lies in `S`, hence in `W`
   (`subset_coborder`). So `g` lifts to `W` (`IsOpenImmersion.lift`), the lift
   lies in `E.pullback W.ι`, and it factors through `ι₀`.

The theorem is preceded by
`set_option backward.isDefEq.respectTransparency.types false in`, as
`affine_case` in `FppfClosedLocusDescentProof.lean` is, so that the instance
`IsStableUnderBaseChange` needed by `Scheme.mem_grothendieckTopology_iff` for
`@Flat ⊓ @LocallyOfFinitePresentation` is found.

## Status

Development checks: `lean_check` diagnostics
`71366007-36c4-4812-8e8e-59f5f9464cc4` (Worker 766) and
`2c6803d7-30ea-447e-8696-6ad99d71f4c0` (Worker 266, Library base `b1c8a5e8`)
compiled the module with 0 errors and 0 warnings. Inspection of
`fppfImmersionLocusDescent` reports a theorem with the single level parameter
`u` and only the axioms `propext`, `Classical.choice` and `Quot.sound`.
Development checks are not acceptance.
