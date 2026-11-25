# Projective frames of torsion evaluations over an algebraically closed field

This internal helper module proves the field case of the frame-locus covering
step. Let `a` be a datum of the published moduli problem over `Spec K`, where
`K` is an algebraically closed field. It has abelian scheme `π : A → Spec K`,
cubic bundle `L³` and rigidification module `V = π_* L³`. Its frame locus is
`Datum.frameLocus` from the Library module
`Langlands.AbelianScheme.PolarizedFiniteLevel.FrameLocus`. The main theorem
says the following. Assume the Library statement `CubicFieldEmbeddingStatement`
(Lefschetz's embedding theorem over a field). Assume also that `n` is positive
and invertible in `K` and that `n^(2g)` exceeds a fixed multiple of
`n^(2g-2)`. Then some choice of `m + 2` torsion indices has frame locus equal
to the whole base, where `m = cubicProjectiveDimension g d`.

## Declarations

- `Datum.pullbackEvaluation_app_top`: let `y : T → A` be any morphism and `σ`
  a global section of `V`. Pull back the adjoint evaluation `π^* V → L³`
  along `y` and precompose with the comparison `(y ≫ π)^* V ≅ y^* π^* V`.
  This composite sends the pulled-back section of `σ` to
  `pullbackSection y L³ σ`.
- `Datum.exists_pullbackSection_ne_zero`: let the base be affine, `V`
  quasi-coherent and the adjoint evaluation an epimorphism. Then for every
  field-valued point `y : Spec κ → A` some global section `σ` of `V` has
  nonzero pullback `pullbackSection y L³ σ`.
- `Datum.basis_generates`: over `Spec K`, with `V` quasi-coherent and the
  adjoint evaluation an epimorphism, every `K`-basis `basis` of the global
  cubic sections is base-point free. That is, every point of `A` lies in the
  nonvanishing locus of some `basis i`.
- `moduleSpecΓPiIso`, `moduleSpecΓPiIso_hom_apply`: global sections over an
  affine spectrum of a product of module sheaves are the product of the
  global sections. The `j`-th component of the comparison is the global
  sections of the projection `Pi.π N j`.
- `finrank_moduleSpecΓ_lineBundle`: a line bundle on `Spec K` has
  one-dimensional global sections.
- `Datum.finrank_cubicSections`: if `0 < d`, the global cubic sections have
  dimension `cubicProjectiveDimension g d + 1` (which equals `6^g d`).
- `Datum.isClosedImmersion_cubicSectionMap`: under
  `CubicFieldEmbeddingStatement` and `0 < d`, the cubic section map
  `a.cubicSectionMap basis hs` of every generating basis is a closed
  immersion into projective space over `K`.
- `Datum.fibreCoordinates_left`: the geometric fibre point with coordinates
  `r` of the level structure, taken along the identity of `Spec K`, has
  underlying morphism `a.torsionPoint r`.
- `Datum.isIso_frameEvaluation_of_bijective`: with `V` quasi-coherent, the
  frame evaluation `a.frameEvaluation ρ k` is an isomorphism if the map
  `s ↦ (j ↦ (a.torsionEvaluation (ρ j)).app ⊤ s)` is bijective. Here `s`
  runs over global sections of `V` and `j` over indices different from `k`.
- `Datum.frameLocus_eq_top_of_isIso`: over any base, if every frame
  evaluation of `ρ` is an isomorphism, the frame locus of `ρ` is `⊤`.
- `Datum.exists_frameLocus_eq_top` (main theorem): assume
  `CubicFieldEmbeddingStatement`, `0 < g`, `0 < d`, `0 < n`, `(n : K) ≠ 0`
  and

  `(cubicProjectiveDimension g d + 1) * (6^g * d * g! * n^(2g-2)) < n^(2g)`.

  Then there is `ρ : Fin (cubicProjectiveDimension g d + 2) → (Fin (2g) → ZMod n)`
  with `a.frameLocus ρ = ⊤`.

## Proofs

`Datum.pullbackEvaluation_app_top` follows the composite on sections. The
right-hand side is written with `pullbackSection_eq_sectionPullback`. The
Library lemma `pullbackComp_inv_sectionPullbackLE` splits the pullback along
`y ≫ π`. `pullback_map_app_sectionPullbackLE` (from
`TorsionEvaluationSections`) moves the evaluation map inside. Finally
`Datum.cubicEvaluationAdjoint_eq_evaluationAdjoint` and
`evaluationAdjoint_sectionPullback` evaluate the adjoint evaluation on the
pulled-back section `σ`, which gives `σ`.

`Datum.exists_pullbackSection_ne_zero` argues by contradiction. Write `θ` for
the composite from the previous lemma, with `T = Spec κ`. Every global
section of `(y ≫ π)^* V` is a sum of tensors `c ⊗ σ`
(`pullbackTensorMap_bijective`, using that the base and `Spec κ` are affine).
If all `pullbackSection y L³ σ` vanish, `θ` is zero on global sections. On
the other hand `θ` is an epimorphism (a pullback of an epimorphism composed
with an isomorphism), hence surjective on sections over the affine `⊤`
(`QuasicoherentLocal.surjective_app_of_epi`). The target `y^* L³` is
isomorphic to the structure sheaf of `Spec κ` (`fieldLineBundleTriviality`),
whose global section `1` is nonzero. This is a contradiction.

`Datum.basis_generates` takes a point `x` where every `basis i` vanishes. The
previous lemma, applied to `Spec κ(x) → A`, gives a section `σ` with nonzero
pullback at `x`. Expand `σ` in the basis. The Library equivalence
`basisHyperplaneSectionEquiv` and `basisHyperplaneSectionEquiv_eq_linComb`
write `σ` as a linear combination `linComb` of the `basis i`. The pullback is
additive and `K`-linear (`pullbackSection_sum`, `pullbackSection_smul`), so
the pullback of `σ` vanishes, a contradiction.

`moduleSpecΓPiIso` composes the product-preservation isomorphism of
`moduleSpecΓFunctor` with Mathlib's `ModuleCat.piIsoPi`. The component
formula follows from `ModuleCat.piIsoPi_hom_ker_subtype` and
`piComparison_comp_π`.

`finrank_moduleSpecΓ_lineBundle` applies the Library dimension formula
`FiniteFlatPointFibre.finrank_relativeGlobalSections_lineBundle` to the
identity of `Spec K`. The structure sheaf has one-dimensional sections
(`finrank_relativeGlobalSections_structureSheaf` and
`Scheme.Hom.finrank_eq_one_of_isIso`), and pushforward along the identity is
isomorphic to the identity.

`Datum.finrank_cubicSections` combines `cubicProjectiveDimension_add_one`,
the Library computation `cubicFibreCohomology` of the degree-zero cohomology
of `L³` over an algebraically closed field, and the identification
`relativeCohomologyZeroIso` of degree-zero relative cohomology with relative
global sections.

`Datum.isClosedImmersion_cubicSectionMap` uses the second part of
`CubicFieldEmbeddingStatement`: the relative linear-system map is a closed
immersion. By `relativeLinearSystemMap_toPolynomial`, composing it with
`RelativeProjectiveSpace.toPolynomial m (𝟙)` gives the absolute linear-system
map `linearSystemMap π hs`, which is `a.cubicSectionMap basis hs`. Over the
identity base, `toPolynomial` is `map (𝟙)` followed by an isomorphism, so it
is an isomorphism. A closed immersion composed with an isomorphism is a
closed immersion.

`Datum.fibreCoordinates_left` rewrites with the Library lemma
`enumerateTuple_fibre`. The geometric fibre point is then the composite of
`Over.homMk (𝟙)` with the enumerated torsion section, whose underlying
morphism is `a.torsionPoint r`.

`Datum.isIso_frameEvaluation_of_bijective` applies the Library criterion
`ModuleDescentCore.isIso_of_bijective_app_top` over the affine base: a map of
quasi-coherent modules is an isomorphism if it is bijective on global
sections. The target of the frame evaluation is a finite product of line
bundles, so it has a finite local basis (`hasFiniteLocalBasis_frameTarget`,
from `FrameLocusIsoLocus`) and is finitely presented. Its global sections are
identified with the product by `moduleSpecΓPiIso`. Under this identification
the frame evaluation becomes the map in the hypothesis (`Pi.lift_comp_π`).

`Datum.frameLocus_eq_top_of_isIso`: the frame locus is the supremum of the
opens on which all frame evaluations restrict to isomorphisms. The open `⊤`
is one of them, because restriction to `⊤` preserves isomorphisms.

`Datum.exists_frameLocus_eq_top` proceeds as follows.

1. Set `m = cubicProjectiveDimension g d`. The Library theorem
   `cubicDirectImage` makes `V` locally free, hence finitely presented and
   quasi-coherent. `CubicFieldEmbeddingStatement` makes the adjoint
   evaluation an epimorphism. Let `V₀` be the global cubic sections. By
   `Datum.finrank_cubicSections`, `dim V₀ = m + 1`. Choose a basis `β`. By
   `Datum.basis_generates` it is base-point free. By
   `Datum.isClosedImmersion_cubicSectionMap` its section map is a closed
   immersion.
2. For each torsion index `r`, let `W_r` be the global sections of
   `P_r^* L³`, where `P_r = a.torsionPoint r`. It is one-dimensional, so
   choose a linear isomorphism `e_r : W_r ≅ K`. Let `ℓ_r : V₀ → W_r` be the
   torsion evaluation on global sections. By `Datum.torsionEvaluation_app_top`
   (from `TorsionEvaluationSections`), `ℓ_r s = 0` exactly when `s` vanishes
   along `P_r`. The configuration is `v_r = e_r ∘ ℓ_r` in the dual space of
   `V₀`.
3. Hyperplane bound. Let `Λ` be a nonzero functional on the dual space. Then
   `Λ` is evaluation at a nonzero section `s` (`Module.evalEquiv`). Let `F`
   be the linear form corresponding to `s` under
   `basisHyperplaneSectionEquiv`. The Library lemma `vanishesAlong_linComb_iff`
   (from `FieldPointHyperplane`), together with `degreeOneBasis_expansion` and
   `Datum.fibreCoordinates_left`, shows: `Λ (v_r) = 0` if and only if `F` lies
   in the homogeneous ideal of the image under the cubic section map of the
   geometric fibre point with coordinates `r`. The Library equivalence
   `hyperplaneCoordinateEquiv` identifies such indices with
   `TorsionHyperplaneSections (a.cubicSectionMap β hs) F`. The Library bound
   `Datum.cubicSectionMap_torsionHyperplane_bound`, with the proved
   `cubicTorsionHyperplaneBound`, bounds their number by
   `q = 6^g d g! n^(2g-2)`. This needs the closed immersion from step 1 and
   `(n : K) ≠ 0`. Hence `HyperplaneBound v q` holds.
4. There are `n^(2g)` torsion indices and the dual space has dimension
   `m + 1`. By the size hypothesis, `HyperplaneBound.exists_frame` (from
   `ProjectiveFrameSelection`) gives `ρ : Fin (m + 2) → (Fin (2g) → ZMod n)`
   such that for each `k` the `m + 1` functionals `v (ρ j)` with `j ≠ k` are
   linearly independent.
5. Fix `k` and let `Ψ : V₀ → ∏_{j ≠ k} W (ρ j)` be the product of the
   `ℓ (ρ j)`. The `m + 1` functionals `v (ρ j)` with `j ≠ k` are linearly
   independent in a space of dimension `m + 1`, so they span the dual space
   (`LinearIndependent.span_eq_top_of_card_eq_finrank'`). If `Ψ s = 0`, every
   such functional vanishes at `s`. Hence every functional vanishes at `s`,
   and `s = 0` by `Module.forall_dual_apply_eq_zero_iff`. Thus `Ψ` is
   injective. Its source and target both have dimension `m + 1`, so it is
   bijective (`LinearMap.injective_iff_surjective_of_finrank_eq_finrank`).
   `Datum.isIso_frameEvaluation_of_bijective` makes the frame evaluation an
   isomorphism. Finally `Datum.frameLocus_eq_top_of_isIso` gives
   `a.frameLocus ρ = ⊤`.

## Provenance

This is an internal step of the reduction from Lefschetz's embedding theorem
to the covering statement `FrameLocusCoverStatement`. It follows the proof that
torsion configurations are stable in Mumford, Fogarty and Kirwan, *Geometric
Invariant Theory*, third edition (1994). Proposition 7.7 (printed p.138 /
one-based PDF p.151) bounds the number of torsion points on a hyperplane
section of the Lefschetz embedding by a multiple of `n^(2g-2)`. This bound is
the Library's `cubicTorsionHyperplaneBound`. When `n` is large, Mumford uses
it to choose torsion points in general position. Lefschetz's theorem (the
third power of an ample bundle is very ample) is Mumford, *Abelian
Varieties*, §17, Theorem on p.163. Here it enters only through the hypothesis
`CubicFieldEmbeddingStatement`. Mumford's statements concern configurations
of points in projective space. This module's frame condition is the linear
dual: the torsion evaluations form a projective frame in the dual of the
space of global sections. In Lean the frame condition is that frame
evaluations of module sheaves are isomorphisms. The translation through
global sections and the frame selection are internal.
