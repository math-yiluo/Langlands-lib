# Ring-map lifting for the effective Picard tower bundle

This internal module proves condition (2) of Stacks Lemma 90.13.2 for the
published effective line bundle of the Picard source tower: maps into the
limit ring lift along elementary surjections with one-dimensional kernel. Only
small extensions with one-dimensional kernel are treated, which is the form
required by `ArtinianPrincipalLifting.isFormallyVersalAt_of_ringLifting`. All
declarations are in the namespace
`Langlands.AlgebraicGeometry.Picard.PicardGroupoid.ArtinianPicardTowerRingLifting`.

Throughout, `k` is a commutative ring, `K` a field with a `k`-algebra
structure, and tests are objects of the published `ArtinianTest k K`. For a test
arrow `q : A ⟶ B`, `Kernel q` is the published kernel ideal and
`Pullback.test q g` the published fibre product test with projections
`Pullback.fst` and `Pullback.snd`.

## Algebra: one-dimensional kernels

`liftAlgHom_surjective`. Let `q : A ⟶ B` be a test arrow with an additive
isomorphism `c : Kernel q ≃+ K` satisfying `c (a • x) = ε_A(a) * c x`. Let
`g : T ⟶ B` be a test arrow, `R` a `k`-algebra with a surjective map
`ε : R → K`, and `σ : R → A`, `π : R → T` algebra maps with `q ∘ σ = g ∘ π`,
`ε_A ∘ σ = ε` and `π` surjective. If `σ` does not kill the kernel of `π`, then
the induced map `R → A ×_B T` (published `Pullback.liftAlgHom`) is surjective.
Proof: pick `r₀` with `π r₀ = 0` and `σ r₀ ≠ 0`, so `σ r₀` is a nonzero element
of `Kernel q`. Given `(a, t)` in the fibre product, choose `r₁` with
`π r₁ = t`. Then `a - σ r₁` lies in `Kernel q`, so it equals `σ(r₂) σ(r₀)` for
any `r₂` with `ε(r₂) = c(a - σ r₁) / c(σ r₀)`. The element `r₁ + r₂ r₀` maps to
`(a, t)`.

## Extension of a stage family over a flat base

`exists_extension`. Let `f : X ⟶ Spec k` be flat and `M` an actual line bundle
on the base change of `X` to the residue point. Let `q : A ⟶ B` be an elementary
surjection, `g : T ⟶ B` a test arrow, `ξ` an actual pointed deformation of `M`
over `T`, and `N` an actual line bundle on the base change to `A`. Given an
isomorphism of line bundles between the pullbacks of `ξ` along `baseMap g` and
of `N` along `baseMap q`, there is an actual pointed deformation `Z` over
`Pullback.test q g` whose restriction along `Pullback.snd` is isomorphic to
`ξ` as a pointed deformation.

Proof: `Pullback.test q g` is a ring fibre product `A ×_B T` with `q`
surjective with square-zero kernel. The published
`FlatPicardSquareGluing.affine_isSquareEffective`, applied to the flipped
published ring pullback square `Pullback.ring_isPullback q g`, glues the
underlying bundle of `ξ` and `N` to a bundle `Z` on the total corner. Its
restriction to `T` is identified with the underlying bundle of `ξ`.
`PseudofunctorPointedTransport.transport` then carries the pointing of `ξ` to
`Z`, and `transportIso` gives the isomorphism of pointed deformations.

## Ring-map lifting

Let `R` be a complete Noetherian local `k`-algebra with surjective
augmentation `ε : R → K`. Let `f` be flat and proper, and let `s₀` be a
published `ArtinianPicardSourceStep.Stage ε f M`. Write `H` for the published
limit ring `ArtinianPicardSourceTower.limitRing`, `L` for the published
effective bundle `ArtinianPicardTowerAlgebraization.effectiveBundle` on the
base change to `H`, and `p` for the published closed point `residuePoint`.

`exists_ringLift` assumes `hlift`: for every test arrow `q` with surjective
algebra map, every augmentation-compatible map `R → B` lifts to `A`
(surjectivity of the published `AugmentedAdicCompletion.postcomp ε q`). Let
`q : A ⟶ B` be an elementary surjection with `c` as above, `N` an actual line
bundle on the base change to `A`, and `y` an actual point of `L` with values
in `N` over `baseMap q` (published `ArtinianChartVersality.FiberPoints`), with
closed point `p`. Then there is `u : base A ⟶ affineBase k H` with
`baseMap q ≫ u = y.1`.

Proof, following the proof of Stacks Lemma 90.13.4:

1. `y.1` is the spectrum of an algebra map `α : H → B` compatible with the
   augmentations. This uses the published `OpennessOfVersality`
   lemmas `exists_affineBaseMap_eq`, `affineBaseMap_injective` and
   `reduction_comp_affineBaseMap`.
2. By the published `ArtinianAdicEvaluation.exists_bound`, `α` has a finite
   adic bound `a`. With `n = index a`, the published
   `ArtinianPicardTowerEvaluation.stageMap` gives a test arrow
   `g : test n ⟶ B` with `g ∘ projection n = α`. Let `s` be stage `n`.
3. By `hlift`, the map `g ∘ s.cover : R → B` lifts to `σ : R → A` with
   `q ∘ σ = g ∘ s.cover`.
4. If `σ` kills the kernel of `s.cover`, then `σ` descends to `H`, because the
   limiting equations lie in that kernel. The descended map gives `u`.
5. Otherwise `liftAlgHom_surjective` makes `R → A ×_B test n` surjective. The
   published `ElementarySourceExtension.factor` factors this map as a surjective
   test arrow `τ : s.sourceTest ⟶ Pullback.test q g` with
   `τ ≫ Pullback.snd = s.sourceReduction`. The published
   `effectiveEvaluationIso` identifies the pullback of `L` along `α` with the
   pullback of the stage bundle along `g`. Composed with the isomorphism of
   `y`, this is the input of `exists_extension`, which gives a pointed family
   over `Pullback.test q g` restricting to `s.family`. The minimality theorem
   `ArtinianPicardSourceMinimality.exists_next_factor_of_extension` gives
   `ψ : test (n + 1) ⟶ Pullback.test q g` with `ψ ≫ Pullback.snd = s.reduction`.
   Then `u` is the spectrum of `fst ∘ ψ ∘ projection (n + 1)`. It extends `y.1`
   by `Pullback.condition`, the published `projection_step` and `stageMap_projection`.

## Provenance

Internal. Step 5 and the dichotomy in step 4 are the argument in the proof of
Stacks Project Lemma 90.13.4 (Tag 06IW, Chapter 90 Formal Deformation Theory)
that the hull satisfies condition (2) of Lemma 90.13.2 (Tag 06IU). In Stacks
the dichotomy is between `S/J_n ×_A B → S/J_n` having a section and being an
essential surjection. Here it is the explicit computation of
`liftAlgHom_surjective` for one-dimensional kernels. Condition (S1) for line
bundles is the published flat-base gluing theorem.
