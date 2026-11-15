# Artinian lifting of Picard-zero families, assuming the underlying line bundle lifts

Author: Worker 225.

This module reduces the target proposition
`Langlands.AbelianScheme.PicardZeroArtinianLiftingStatement` to lifting a plain line
bundle. The rigidification and the Picard-zero condition of the lift are not part of
that hypothesis. The main results are two explicitly conditional theorems:

- `picardZeroArtinianLifting_of_familyLineBundle_lift (hlift) :
  PicardZeroArtinianLiftingStatement`, where `hlift` says the following. Take all the
  data of the target: an abelian scheme `A` over `S`, a surjection `φ : B' → B` of local
  Artinian rings with `maximalIdeal B' * ker φ = ⊥`, a morphism `β : Spec B' ⟶ S`, and a
  rigidified family `M` over `Over.mk (Spec φ ≫ β)` with `IsPicardZeroFamily A M`. Then
  there is a line bundle `L'` on `((baseChange β).obj A).X.left = A ×_S Spec B'` such
  that `(LineBundle.pullback (totalSpaceMap A φ β)).obj L'` is isomorphic to
  `familyLineBundle A M`.
- `picardZeroArtinianLifting_of_lineBundle_lift (hlift) :
  PicardZeroArtinianLiftingStatement`. This is the same reduction with the hypothesis
  stated on the relative total space `(relativeSpace A.X.hom).obj (Over.mk β)`. The lift
  `N` must satisfy
  `(LineBundle.pullback ((relativeSpace A.X.hom).map (Over.homMk (Spec φ) rfl))).obj N ≅
  (RigidifiedLineBundle.forget _).obj M`.

Neither hypothesis is proved or assumed anywhere else in the module. The obstruction
theory that should discharge them is not used here. The other inputs are proved Library
results:

- `Langlands.Scheme.Modules.pullbackTensorComparisonIsIso`;
- `Langlands.SchemeModule.RigidifiedModule.pullbackCoherence`;
- `RigidifiedLineBundle.nonempty_iso_of_forget_iso` (module `RigidifiedCarrierIso`);
- `LineBundle.nonempty_iso_trivial_of_unique`, `pullbackCompEqIso`, `pullbackEqIso`
  and `isoOfPullbackIso` (module `LineBundleIsoLemmas`);
- `picardZeroGeometricDetection` (module `PicardZeroGeometricDetectionProof`);
- `RigidifiedLineBundle.classifyingMap_comp`.

All declarations are in the namespace
`Langlands.AbelianScheme.PicardZeroArtinianLiftingReduction`.

## Provenance

The target is a derived formulation of the Artinian case of Faltings–Chai, *Degeneration
of Abelian Varieties*, Chapter I, Remark 1.5(c); see the Markdown of
`PicardZeroArtinianLiftingStatement`. This module formalizes step 1 of the mathematical
outline in the context of task `d1735ac9-6af5-4460-8c3a-b09a43c01ffa`. Once the
underlying line bundle lifts, the rigidification and the Picard-zero condition of the
lift come for free. The hypotheses `hlift` are internal interfaces chosen for the split
of that task between its two executors. They are not source theorems.

## Declarations and proofs

### Ring-theoretic lemmas

- `mul_self_eq_zero_of_mem_ker`: if `maximalIdeal B' * ker φ = ⊥`, then every `x ∈ ker φ`
  has `x * x = 0`. If `x` were a unit, `φ x = 0` would be a unit. So `x` lies in the
  maximal ideal, and `x * x ∈ maximalIdeal B' * ker φ = ⊥`.
- `exists_comp_spec_eq`: for surjective `φ` with the same kernel condition, every
  morphism `s : Spec K ⟶ Spec B'` from the spectrum of a field factors as
  `s₀ ≫ Spec φ`. Write `s = Spec ψ`. Each `x ∈ ker φ` has `ψ x * ψ x = ψ (x * x) = 0` in
  the field `K`, so `ψ x = 0`. Hence `ψ` factors through `φ` by
  `RingHom.liftOfSurjective`.

### Pullback bookkeeping for the Picard-zero predicate

- `isPicardZeroFamily_relativePullback_comp`: the predicate on a family pulled back
  first along `h` and then along `g` agrees with the predicate on its pullback along
  `g ≫ h`. This is `RigidifiedLineBundle.classifyingMap_comp` with
  `RigidifiedModule.pullbackCoherence`, applied through `IsPicardZeroClass`.
- `isPicardZeroFamily_overHomMk_iff`: a pullback along `Over.homMk s hs` depends only on
  `s`. After substituting `hs`, this holds by `rfl`.

### The canonical total-space map

- `totalSpaceMap A φ β` (an `abbrev`) is
  `Limits.pullback.map A.X.hom (Spec φ ≫ β) A.X.hom β (𝟙 _) (Spec φ) (𝟙 S)`. This is the
  canonical map `A ×_S Spec B ⟶ A ×_S Spec B'`, the identity on the `A` factor.
- `relativeSpaceSymmetry_inv_comp_map`: under the inverse symmetry isomorphisms
  `relativeSpaceSymmetry`, `totalSpaceMap` agrees with the relative total-space map
  `(relativeSpace A.X.hom).map (Over.homMk (Spec φ) rfl)`. Both projections are
  checked with `pullback.hom_ext`. `simp` unfolds the maps, and `erw` with
  `pullback.lift_fst` and `pullback.lift_snd` handles the two definitionally equal
  presentations of the pullback objects.
- `nonempty_lineBundle_lift_of_familyLineBundle_lift`: write `σ` and `τ` for the
  symmetry isomorphisms over `Spec B` and `Spec B'`, and take
  `N = (LineBundle.pullback τ.hom).obj L'`. By `isoOfPullbackIso σ.inv`, it is enough to
  identify the pullbacks along `σ.inv`. The left side becomes the pullback along
  `σ.inv ≫ relativeSpace.map _ = totalSpaceMap ≫ τ.inv`. Composing pullbacks, `τ.inv ≫
  τ.hom = 𝟙` gives `(LineBundle.pullback totalSpaceMap).obj L'`. This is
  `familyLineBundle A M = (LineBundle.pullback σ.inv).obj (forget M)` by the given
  isomorphism.

### The reduction

- `exists_picardZero_lift_of_lineBundle_lift`: given `N` on the relative total space over
  `Spec B'` and an isomorphism `e` from its pullback to `forget M`, there is a
  Picard-zero rigidified family `M'` over `Spec B'` whose rigidified pullback along
  `Spec φ` is isomorphic to `M`. The proof has three steps.
  1. *Rigidify.* `Spec B'` has one point (`PrimeSpectrum` of a local Artinian ring is
     `Unique`). So the restriction of `N` along the unit section `ε'` is trivial by
     `LineBundle.nonempty_iso_trivial_of_unique`. This trivialization makes `N` into a
     rigidified family `M'` through `RigidifiedLineBundle.ofLineBundle`.
  2. *Compare with `M`.* `RigidifiedLineBundle.nonempty_iso_of_forget_iso` says that
     rigidified line bundles with isomorphic underlying line bundles are isomorphic
     when the rigidification section has a retraction. Here the retraction is the
     projection `(relativeProjection A.X.hom).app _`, by `relativeSection_projection`,
     and the tensor input is `pullbackTensorComparisonIsIso`. Applied to `e`, it gives
     an isomorphism between the rigidified pullback of `M'` and `M`. This works because
     the underlying line bundle of the rigidified pullback is, by definition, the
     line-bundle pullback of `N`.
  3. *Picard-zero.* By `picardZeroGeometricDetection`, it suffices to check pullbacks to
     all algebraically closed geometric points `s : Spec K ⟶ Spec B'`. Each such `s` is
     `s₀ ≫ Spec φ` by `exists_comp_spec_eq`. The detection criterion for `M` at `s₀`
     gives the condition for the pullback of `M` along `s₀`, which is isomorphic to the
     pullback of `M'` along `s₀ ≫ Spec φ` (by the rigidified isomorphism, then
     `isPicardZeroFamily_relativePullback_comp`). The `Over` morphisms are matched by
     `ext; rfl` and `isPicardZeroFamily_overHomMk_iff`.
- `picardZeroArtinianLifting_of_lineBundle_lift`: introduce the data of the target,
  obtain `N` and `e` from `hlift`, and apply the previous theorem.
- `picardZeroArtinianLifting_of_familyLineBundle_lift`: introduce the data of the
  target, obtain `L'` from `hlift`, convert it with
  `nonempty_lineBundle_lift_of_familyLineBundle_lift`, and apply
  `exists_picardZero_lift_of_lineBundle_lift`.
