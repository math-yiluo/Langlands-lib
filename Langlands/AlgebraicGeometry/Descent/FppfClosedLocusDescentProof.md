# Proof of fppf descent of closed loci

Authors: Worker 766 and Worker 266. Worker 766 wrote the Lean proof and the
first version of this Markdown. Worker 266 checked both against the statement,
the Lean code and the source, and revised the Markdown.

`Langlands.AlgebraicGeometry.fppfClosedLocusDescent` proves
`Langlands.AlgebraicGeometry.FppfClosedLocusDescentStatement.{u}`. See
`FppfClosedLocusDescentStatement.md` for the exact statement and the meaning of
its ingredients. In short: let `E` be an fppf-closed sieve on a scheme `Y`, and
suppose that on every member `f : Y' ⟶ Y` of some fppf covering sieve `R`, the
pullback of `E` is cut out by a closed immersion into `Y'`. Then a single closed
immersion `ι : Z ⟶ Y` cuts out `E`. That is, `g : T ⟶ Y` factors through `ι`
exactly when `E g`.

## Provenance

The result is the subfunctor form of effective fpqc descent of closed
immersions, Stacks Project, *Descent*, Lemma 35.37.2 (Tag 03I0), specialized to
fppf coverings. The source and the translation are recorded in
`FppfClosedLocusDescentStatement.md`. The Stacks proof (source
`stacks-descent-ed88ff78-2026`, PDF p.89) notes that closed immersions are affine
and applies Lemma 35.37.1 (Tag 0245). That proof reduces, by Lemma 35.36.2, to a
single flat surjective morphism of affine schemes, that is, a faithfully flat
ring map `R → A`, and descends the algebra by faithfully flat descent of modules
(Proposition 35.3.9). The Lean proof follows a different, more direct route,
designed for this module. It uses no descent of modules and no explicit descent
datum. Over an affine base it writes down the ideal of the closed subscheme and
checks it with one flatness argument. Then it glues the affine pieces with the
Library theorem `Langlands.AlgebraicGeometry.closedLocusFromAffineCharts`. No
code is copied from another project.

The module imports the statement module, the Library module
`Langlands.AlgebraicGeometry.ClosedLocusFromAffineChartsProof`, and the Mathlib
modules `AlgebraicGeometry.Cover.QuasiCompact`, `AlgebraicGeometry.Morphisms.Flat`,
`RingTheory.TensorProduct.Pi` and `RingTheory.TensorProduct.Quotient`.

## Proof outline

The auxiliary declarations live in the namespace
`Langlands.AlgebraicGeometry.FppfClosedLocusDescent`.

### 1. Flat descent of ideals (section `Algebra`)

Let `A` be a commutative ring, `(B l)` a family of commutative `A`-algebras
indexed by `ι`, and `I l` an ideal of `B l`. Put
`J = ⨅ l, (I l).comap (algebraMap A (B l))`, the ideal of `A` of elements that
map into every `I l`.

- `algebraMap_quotient_eq_zero_iff`: `a ∈ A` maps to `0` in `B l ⧸ I l` exactly
  when `a` lies in the preimage of `I l`.
- `quotientToPi`: the `A`-algebra map `A ⧸ J → ∀ l, B l ⧸ I l` induced by the
  structure maps (`Ideal.Quotient.liftₐ` of `AlgHom.pi`). `quotientToPi_mk`
  computes it on classes. `quotientToPi_injective` shows it is injective, which
  is the definition of `J`.
- `le_map_iInf_comap`: let `ι` be finite and `B i` flat over `A`. Suppose that
  `b ⊗ₜ 1 = 0` in `B i ⊗[A] (B l ⧸ I l)` for every `l` and every `b ∈ I i`. Then
  `I i ≤ J.map (algebraMap A (B i))`. *Proof.* Tensoring the injective map
  `quotientToPi` with the flat module `B i` keeps it injective
  (`Module.Flat.lTensor_preserves_injective_linearMap`). Since `ι` is finite,
  `Algebra.TensorProduct.piRight` identifies `B i ⊗[A] ∀ l, B l ⧸ I l` with
  `∀ l, B i ⊗[A] (B l ⧸ I l)`. By hypothesis the composite sends `b ⊗ₜ 1` to
  `0`, so `b ⊗ₜ 1 = 0` in `B i ⊗[A] (A ⧸ J)`. Under
  `Algebra.TensorProduct.quotIdealMapEquivTensorQuot`, which identifies
  `B i ⧸ J.map (algebraMap A (B i))` with `B i ⊗[A] (A ⧸ J)`, this says that the
  class of `b` is `0`, so `b ∈ J.map (algebraMap A (B i))`.

### 2. Helper lemmas on schemes (section `Schemes`)

- `factors_iff_ker_le`: a morphism `g : T ⟶ X` factors through a closed
  immersion `ι : Z ⟶ X` exactly when `ι.ker ≤ g.ker` (`IsClosedImmersion.lift`
  and `Scheme.Hom.le_ker_comp`).
- `factors_iff_ker_appTop_le`: if `X` is affine, the same holds with the kernels
  of the ring maps on global sections, `RingHom.ker ι.appTop.hom ≤
  RingHom.ker g.appTop.hom`. This uses `Scheme.ker_of_isAffine` and the order
  isomorphism `Scheme.IdealSheafData.equivOfIsAffine` between ideal sheaves on an
  affine scheme and ideals of its global sections.
- `ker_appTop_le_ker_comp_appTop`: the kernel on global sections can only grow
  under precomposition.
- `appTop_specMap_comp_isoSpec_inv` and `ker_appTop_specMap_comp_isoSpec_inv`:
  for `X` affine and a ring map `ψ : Γ(X, ⊤) ⟶ R`, the morphism
  `Spec.map ψ ≫ X.isoSpec.inv : Spec R ⟶ X` has map on global sections
  `ψ ≫ (Scheme.ΓSpecIso R).inv`. In particular its kernel is `RingHom.ker ψ`.
- `exists_isClosedImmersion_ker_appTop`: for `X` affine, every ideal
  `J` of `Γ(X, ⊤)` is the kernel on global sections of a closed immersion,
  namely `Spec (Γ(X, ⊤) ⧸ J) ⟶ X`.
- `exists_lift_of_covering`: in a category with a subcanonical topology `J`, let
  `ι : Z ⟶ Y` be a monomorphism and `g : T ⟶ Y`. If `u ≫ g` factors through `ι`
  for every `u` in a covering sieve `S` of `T`, then `g` factors through `ι`.
  The local factorizations form a compatible family because `ι` is a
  monomorphism. It glues because the representable presheaf of `Z` is a sheaf,
  and the glued morphism satisfies the equation because the representable
  presheaf of `Y` is separated.
- `exists_of_pullback_generate_ofArrows`: a member `u` of the pullback along `g`
  of the sieve generated by a family `f l : W l ⟶ X` satisfies
  `m ≫ f l = u ≫ g` for some `l` and some `m`.

### 3. The descent condition (`tmul_one_eq_zero_of_mem_ker`)

Let `Y`, `W₁` and `W₂` be affine, let `fₖ : Wₖ ⟶ Y`, and let `ιₖ : Zₖ ⟶ Wₖ` be
closed immersions that cut out the pullbacks of `E`. That is, `g : T ⟶ Wₖ`
factors through `ιₖ` exactly when `E (g ≫ fₖ)`. Regard `Γ(Wₖ, ⊤)` as a
`Γ(Y, ⊤)`-algebra through `fₖ.appTop`, and write `Iₖ` for the kernel of
`ιₖ.appTop`. The lemma shows that `b ⊗ₜ 1 = 0` in
`P = Γ(W₁, ⊤) ⊗[Γ(Y, ⊤)] (Γ(W₂, ⊤) ⧸ I₂)` for every `b ∈ I₁`.

Let `p₁ : Spec P ⟶ W₁` and `p₂ : Spec P ⟶ W₂` be the morphisms attached to the
two ring maps into `P`, built as in step 2. Then `p₁ ≫ f₁ = p₂ ≫ f₂`, because
both sides have the same map on global sections and `Y` is affine
(`ext_of_isAffine`). The ring map defining `p₂` kills `I₂`, so `p₂` factors
through `ι₂` by `factors_iff_ker_appTop_le`. Hence `E (p₂ ≫ f₂)`, that is
`E (p₁ ≫ f₁)`, so `p₁` factors through `ι₁`. By `factors_iff_ker_appTop_le`
again, `I₁` lies in the kernel of the ring map `Γ(W₁, ⊤) → P`, `b ↦ b ⊗ₜ 1`.

### 4. A finite affine covering (`affine_core`)

Let `Y` be affine and let `E` be fppf-closed. Let `f l : W l ⟶ Y` be a finite
family of morphisms from affine schemes that are flat and locally of finite
presentation and jointly surjective, and suppose that on each `W l` a closed
immersion `ιZ l : Z l ⟶ W l` cuts out the pullback of `E`. Put
`I l = RingHom.ker (ιZ l).appTop.hom`, regard `Γ(W l, ⊤)` as a
`Γ(Y, ⊤)`-algebra through `(f l).appTop`, and let `J` be the intersection of the
preimages of the `I l` in `Γ(Y, ⊤)`. Each `Γ(W l, ⊤)` is flat over `Γ(Y, ⊤)` by
`Scheme.Hom.flat_appTop`. Step 2 gives a closed immersion `ι₀ : Z₀ ⟶ Y` whose
kernel on global sections is `J`; it is the required closed immersion. The
family `f` generates an fppf covering sieve `S` of `Y`
(`Scheme.ofArrows_mem_precoverage_iff`). Let `g : T ⟶ Y`.

- *If `g` factors through `ι₀`, then `E g`.* Then `J` lies in the kernel of
  `g.appTop`. Since `E` is closed, it suffices that every member `u` of the
  pullback of `S` along `g` satisfies `E (u ≫ g)`. Write `u ≫ g = m ≫ f l`
  (step 2). By step 3 for all pairs, the descent hypothesis of
  `le_map_iInf_comap` holds, so `I l ≤ J.map (algebraMap Γ(Y, ⊤) Γ(W l, ⊤))`.
  The kernel of `(m ≫ f l).appTop = (u ≫ g).appTop` contains `J`, so the kernel
  of `m.appTop` contains the extension of `J`, hence `I l`. So `m` factors
  through `ιZ l`, which gives `E (m ≫ f l)`, that is `E (u ≫ g)`.
- *If `E g`, then `g` factors through `ι₀`.* Apply `exists_lift_of_covering` to
  the fppf topology, which is subcanonical, to the closed immersion `ι₀`, which
  is a monomorphism, and to the pullback of `S` along `g`. For a member `u` with
  `u ≫ g = m ≫ f l`, the sieve property gives `E (m ≫ f l)`. So `m` factors
  through `ιZ l` and `I l` lies in the kernel of `m.appTop`. Then `J` lies in the
  preimage of `I l`, hence in the kernel of `(m ≫ f l).appTop = (u ≫ g).appTop`,
  and `u ≫ g` factors through `ι₀` by `factors_iff_ker_appTop_le`.

### 5. The affine case (`affine_case`)

Let `Y` be affine, `E` fppf-closed, and `R` an fppf covering sieve on whose
members the pullback of `E` is cut out by a closed immersion.
`Scheme.mem_grothendieckTopology_iff`, for the morphism property
`@Flat ⊓ @LocallyOfFinitePresentation`, gives a cover `𝒰` of `Y` by flat
morphisms locally of finite presentation whose arrows lie in `R`. The proof
supplies the instance `IsMultiplicative` for this property by hand, because
instance search does not find it. Flat morphisms locally of finite presentation
are open maps, so `𝒰` is a quasi-compact cover (`QuasiCompactCover.of_isOpenMap`).
Since `Y` is quasi-compact, `QuasiCompactCover.exists_isAffineOpen_of_isCompact`
gives finitely many affine opens `V i ⊆ 𝒰.X (a i)`, `i : Fin n`, whose images
cover `Y`. The composites `(V i).ι ≫ 𝒰.f (a i)` are flat, locally of finite
presentation and jointly surjective, and they lie in `R` because `R` is a sieve.
Step 4 applies to them.

The declaration is preceded by
`set_option backward.isDefEq.respectTransparency.types false in`, the same
option that Mathlib uses for `Scheme.fppfPrecoverage`. Without it, the instance
`IsStableUnderBaseChange` that `Scheme.mem_grothendieckTopology_iff` needs for
`@Flat ⊓ @LocallyOfFinitePresentation` is not found.

### 6. The general case (`fppfClosedLocusDescent`)

Apply `closedLocusFromAffineCharts` to `Y` and the predicate `fun g ↦ E g`. Its
three hypotheses are checked as follows.

1. Stability under precomposition is the sieve property of `E`.
2. Let `g : T ⟶ Y` with `E ((g ⁻¹ᵁ V).ι ≫ g)` for every affine open `V` of `Y`.
   The open immersions `(g ⁻¹ᵁ V).ι` form an fppf covering family of `T`: open
   immersions are flat and locally of finite presentation, and every point of
   `T` lies in some `g ⁻¹ᵁ V` (`exists_isAffineOpen_mem_and_subset`). The sieve
   they generate lies in `E.pullback g`, so `E g` because `E` is closed.
3. For an affine open `U`, apply step 5 to the affine scheme `U`, the sieve
   `E.pullback U.ι` (closed by `GrothendieckTopology.isClosed_pullback`) and the
   covering sieve `R.pullback U.ι` (by `pullback_stable`). For a member `f` of
   `R.pullback U.ι`, the composite `f ≫ U.ι` lies in `R`, so the hypothesis of
   the statement gives a closed immersion cutting out the pullback of `E` along
   `f ≫ U.ι`, which is the pullback of `E.pullback U.ι` along `f`.

## Status

Development checks: `lean_check` diagnostics
`ec121d4a-c649-4e13-a130-e9a2f37cce7c` (Worker 766) and
`ef6daf35-fe4d-4277-81c2-ed4002e33628` (Worker 266, Library base `b1c8a5e8`)
compiled the module with 0 errors and 0 warnings. Inspection of
`fppfClosedLocusDescent` reports a theorem with the single level parameter `u`
and only the axioms `propext`, `Classical.choice` and `Quot.sound`. A separate
check (`badebf4d`) confirmed the two implementation notes of step 5: instance
search does not find `IsMultiplicative` for `@Flat ⊓ @LocallyOfFinitePresentation`,
with or without the option, and finds `IsStableUnderBaseChange` only with the
option. Development checks are not acceptance.
