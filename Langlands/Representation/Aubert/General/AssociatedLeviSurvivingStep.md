# The surviving support step and the associated-Levi comparison

Author: Worker 757 (task `f7d95940-33d0-49d3-93d6-8d5ff8d89373`).

This module assembles the associated-Levi Jacquet comparison (**) of Aubert's
1996 erratum (printed p.4690, Remark (1)) from its separate ingredients. It is
a conditional (helper) result. It proves that one coordinate step of the
corrected support filtration maps isomorphically and naturally onto the actual
Jacquet cokernel `r_I(E#)`. With the graded maps of `CorrectedGradedReduction`
it then derives a natural isomorphism

`C.ι ⋙ StandardComplex.sharpFunctor I ⋙ r_I ≅ C.ι ⋙ r_K ⋙ LeviComplex.sharpFunctor K univ ⋙ Ad(m)`

on any full subcategory `C` of smooth representations. The geometric and
homological inputs (Bruhat cover, graded exactness, vanishing of steps, the
surviving-support hypotheses and the orbit Jacquet data) are explicit
hypotheses. The module does not prove the target
`RationalPointFamily.RationalAssociatedLeviComparisonStatement`. It proves no
Bruhat decomposition, no graded exactness and no Coxeter-combinatorial
vanishing of modified supports.

Provenance: derived and internal. The route is the one of the erratum: the
retained cokernel is filtered by the corrected support filtration, every
graded piece except one cell dies in the cokernel, and the surviving cell is
the Jacquet module of the associated Levi conjugated by `n`. All proofs here
are categorical or linear assembly over published definitions: the corrected
filtration (`CorrectedFiltration`, `CorrectedFiltrationNatural`), Worker 691's
homogeneous Jacquet diagram and degree filtration (`JacquetCutDiagram`,
`CorrectedDegreeFiltration`), Worker 1300's natural cokernels
(`NaturalCokernel`, `AssociatedCokernelTransport`), the graded maps of Worker
969 (`CorrectedGradedReduction`, `CorrectedGradedNatural`), the filtered
cokernel lemmas of `FiniteFilteredCokernel`, and
`LeviComplex.sharpFunctorUnivIso` of `RationalFixedLeviComparisonProof`.

## Conventions

The standard data `P M U h hclosed hδ hP hU`, the subgroup `T`, the finite
relative Weyl group and the Coxeter system `cs` are those of
`CorrectedFiltration`. The complex is indexed by removed roots: the coordinate
`s` of degree `d` (`s.card = d`) is the term `E_J = i_J r_J E` with
`J = S \ s` (`Finset.univ \ s`). `r_I` is the normalized Jacquet functor
`jacquetFunctor (h I) (hclosed I)`. `jacquetDegreeEquiv A I d` is Worker 691's
linear identification of `r_I` of the degree-`d` object with the product
`∏_{s.card = d} r_I(E_{S \ s})`, which is `(jacquetDiagram A I).Degree d`.
`degreeFiltration A I d i` is the coordinatewise step `i` of the corrected
support filtration in that product. `N` denotes the filtration length
`(Support.rankOrderedList cs.length).length`. The graded piece `i` of a
filtration is step `i + 1` modulo step `i`. `gradedDifferential A I i k` is
the map induced by the homogeneous differential of degree `k` on graded
pieces `i`.

The linear lemmas take `A : SmoothRep.{0, uG, max uG uV} ℂ G`. The functorial
part works on `SmoothRep.{0, uG, max uI uG uV} ℂ G`, the universe of the
published targets, and instantiates the linear lemmas at `max uI uV`.

## Coordinate steps and the actual cokernel (per object)

* `step_eq_bot_of_modifiedSupport_eq_empty`: if
  `modifiedSupport cs (S \ s) I i = ∅` then step `i` of `r_I(E_{S \ s})` is
  `⊥`. The support set of the step is then empty.
* `coordinateLinear A I d s`: the inclusion of the coordinate `s` into
  `r_I` of the degree-`d` object, the inverse of `jacquetDegreeEquiv` composed
  with `Pi.single s`. `jacquetDegreeEquiv_coordinateLinear` is the defining
  equation, `coordinateLinear_intertwining` says it is `M_I`-equivariant, and
  `coordinateLinear_natural` says it commutes with the maps induced by a
  morphism `φ : A ⟶ B` (`r_I` of the degree functor on one side, `r_I` of
  `termMap φ s` on the other).
* `jacquetDegreeEquiv_natural`: naturality of `jacquetDegreeEquiv` in the
  ambient representation, coordinate by coordinate. The proof reduces to
  classes `[v]` by `Jacquet.Localization.mk_surjective` and uses
  `jacquetDegreeEquiv_mk`.
* `single_eq_of_mem_degreeFiltration`: if every coordinate `s ≠ s0` of degree
  `d` has empty modified support at `i` (`hconc`), an element of
  `degreeFiltration A I d i` equals `Pi.single s0` of its `s0` coordinate.
* `degreeFiltration_eq_bot`: if every coordinate of degree `k` has empty
  modified support at `i`, then `degreeFiltration A I k i = ⊥`.
* `single_mem_degreeFiltration`: `Pi.single s0 y` lies in step `i` when `y`
  lies in step `i` of the coordinate `s0`.
* `incomingJacquet A I d`: the linear map underlying `r_I` of the actual
  incoming differential `(StandardComplex.incomingDifferentialNat d).app A`.
  `incomingJacquet_zero_apply`: it is zero in degree `0`.
  `jacquetDegreeEquiv_incoming`: in degree `k + 1` it corresponds to the
  homogeneous differential `degreeDifferential k` (Worker 691's
  `jacquetDegreeEquiv_differential`).
* `cokernelCoordinate A I d s0 i`: step `i` of the coordinate `s0`, followed
  by `coordinateLinear` and the quotient by the range of `incomingJacquet`.
* `cokernelCoordinate_injective` (at step `i0 + 1`). Hypotheses:
  `hcover : IsBruhatCover T (P ∅) (P I)`; `hlow`: every `s` of degree `d - 1`
  (`s.card + 1 = d`) has empty modified support at `i0 + 1`; `hinj`: if
  `d = 1`, the graded maps `gradedDifferential A I i 0` are injective for
  `i0 < i < N`; `hex`: if `d = k + 2`, the graded sequences at `k` and `k + 1`
  are exact (`range = ker`) for `i0 < i < N`. Proof: in degree `0` the
  incoming map is zero. In degree `k + 1` a class `[coord y]` that is zero
  gives `Pi.single s0 y = degreeDifferential k b`. Step `i0 + 1` of degree `k`
  is `⊥` by `hlow`, and `b` lies in the top step by `hcover`
  (`degreeFiltration_length`). `FiniteFiltered.map_eq_zero_of_graded_exact`
  then shows that the image is zero. For `k = 0` the previous map is `0`, and
  graded exactness is graded injectivity.
* `cokernelCoordinate_surjective` (at step `i0 + 1`). Hypotheses: `hcover`;
  `hconc`: every coordinate `s ≠ s0` of degree `d` has empty modified support
  at `i0 + 1`; `htop`: if `d = 0` then `N ≤ i0 + 1`; `hsurj`: if `d = k + 1`,
  the graded maps `gradedDifferential A I i k` are surjective for
  `i0 < i < N`. Proof: every element lies in the top step (`hcover`). In
  degree `k + 1`, `FiniteFiltered.exists_sub_mem_of_graded_surjective` moves it
  into step `i0 + 1` modulo the image of the differential. In degree `0` it is
  already there by `htop`. By `hconc` the result is concentrated in `s0`.

## The canonical natural map

* `isIso_of_bijective`: a smooth intertwiner with bijective underlying map is
  an isomorphism (via `mono_iff_injective` and `epi_iff_surjective`). It is a
  local version of `Derivative.LevelCalculus.isIso_of_bijective` with a single
  bijectivity premise, avoiding an additional direct import of `LevelCalculus`.
  Existing natural-cokernel dependencies already include derivative modules.
* `stepFunctor I s i`: the functor from smooth `G`-representations to smooth
  `M_I`-representations sending `A` to the smooth subrepresentation step `i`
  of `r_I(E_{S \ s})` and `φ` to `CorrectedFiltration.stepMap φ I s i`. The
  functor laws come from `termMap_id`, `termMap_comp` and the functor laws of
  `r_I`.
* `incomingJacquetNat I d` (abbrev): `incomingDifferentialNat d` whiskered
  by `r_I`. `jacquetCokernel I d` (abbrev): its natural cokernel
  `SmoothNatCokernel.functor`. For `d = Complex.terminalDegree I` this is the
  target of `StandardComplex.jacquetSharpCokernelIsoOn`.
* `coordinateMorphism I d s0 i A`: `coordinateLinear` on step `i`, as a
  morphism of smooth `M_I`-representations; `coordinateMorphism_apply` and
  `coordinateMorphism_natural`.
* `canonicalMap I d s0 i : stepFunctor I s0 i ⟶ jacquetCokernel I d`: the
  coordinate morphism followed by the natural cokernel projection.
  `canonicalMap_app_apply`: its component at `A` is `cokernelCoordinate`
  (definitional).
* `jacquetCokernel_nonempty_iso`: for a functor `F : D ⥤ SmoothRep ℂ G`, a
  functor `Q : D ⥤ SmoothRep ℂ (M I)` and a natural transformation
  `β : F ⋙ stepFunctor I s0 i ⟶ Q`, if every component of `β` and every
  `cokernelCoordinate (F.obj X) I d s0 i` is bijective, then
  `F ⋙ jacquetCokernel I d ≅ Q`. The isomorphism is the inverse of the
  whiskered canonical map composed with `β`. Both are isomorphisms by
  `NatIso.isIso_of_isIso_app`.

## The graded maps and the assembly

This part assumes `[SigmaCompactSpace G] [T2Space G]`, compactness of every
`G / P_J`, and `hPc`, closedness of every `P J`, as `stepGradedMap` does.

* `gradedNat F H hNc hK DE hnat hKs hs`: the components
  `CorrectedFiltration.stepGradedMap … (F.obj X) … (DE X) hKs hs` from step
  `i + 1` of the coordinate `s` to `Ad(m)(r_K(F.obj X))`, as a natural
  transformation `F ⋙ stepFunctor I s (i + 1) ⟶ F ⋙ r_K ⋙ conjugationFunctor m hK`.
  The inputs are `H : SurvivingSupportHypotheses P T cs I s i m`, the
  compact-limit premise `hNc` for `U_I ∩ P_I`, `hK : x ∈ M I ↔ m⁻¹ x m ∈ M K`,
  a family `DE` of orbit Jacquet data for the objects `F.obj X`, `hnat`
  (`(DE X).IsNatural (DE Y) (F.map f)` for every `f : X ⟶ Y`),
  `hKs : K ⊆ S \ s` and `hs : IsMinimal cs (S \ s) I w`. Naturality is Worker
  969's `stepGradedMap_natural`.
* `gradedNat_app_bijective`: if moreover
  `modifiedSupport cs (S \ s) I i = ∅`, every component is bijective. It is
  surjective by `stepGradedMap_surjective`. Its kernel lies in step `i` by
  `stepGradedMap_eq_zero_iff`, and that step is `⊥`.
* `associatedLeviComparison_of_survivingStep`: let `C` be an object property
  of smooth `G`-representations, `I` a subset with `hUc` (compact-limit
  premise for `U I`), `d = Complex.terminalDegree I`, `s0` a coordinate of
  degree `d`, `i0 : ℕ`, `m : G` and `K` with `hK`. Let `hMK`, `hLeviK` and
  `hLeviδK` be the closedness, Levi decompositions and unimodularity in `M K`
  used by `LeviComplex.sharpFunctor K`. Assume `hcover`, `hlow`, `hconc` and
  `htop` as above, and `hsurj`, `hinj` and `hex` for every `E` with `C E`.
  Assume `H`, `hNc`, a family `DE` of orbit Jacquet data on the objects of `C`
  with `hnat`, `hKs : K ⊆ S \ s0`, `hs : IsMinimal cs (S \ s0) I w` and
  `hθ : modifiedSupport cs (S \ s0) I i0 = ∅`. Then
  `Nonempty (C.ι ⋙ StandardComplex.sharpFunctor I ⋙ r_I ≅ C.ι ⋙ r_K ⋙ LeviComplex.sharpFunctor K univ ⋙ conjugationFunctor m hK)`.
  Proof: `StandardComplex.jacquetSharpCokernelIsoOn` identifies the left side
  with `C.ι ⋙ jacquetCokernel I d`. `jacquetCokernel_nonempty_iso` with
  `β = gradedNat` at `i0` (the step `i0 + 1`) identifies it with
  `C.ι ⋙ r_K ⋙ Ad(m)`; bijectivity of the canonical map is
  `cokernelCoordinate_injective` and `_surjective`, and bijectivity of `β` is
  `gradedNat_app_bijective`. Finally `LeviComplex.sharpFunctorUnivIso` for
  `K`, whiskered by `Ad(m)` and composed with the left unitor, identifies the
  right side with `C.ι ⋙ r_K ⋙ Ad(m)`.

The intended instantiation for (**) is not carried out here. It takes
`C = TerminalJacquet.supportObjects I`, `K = I'` the associated subset,
`m = n` a lift of the longest representative, `w = (longestRep I)⁻¹` and
`s0 = S \ I'`. It must then supply `hcover`, the graded exactness hypotheses,
`H`, the orbit Jacquet data and the Coxeter facts `hlow`, `hconc`, `htop`,
`hθ`, `hs` and `s0.card = d`.

## Natural orbit Jacquet data

This module proves no naturality of orbit Jacquet data. For the family `DE`
and its hypothesis `hnat`, one can use Worker 1255's published
`CorrectedFiltration.naturalOrbitJacquetData` and
`naturalOrbitJacquetData_isNatural` (module `CorrectedOrbitJacquetNatural`),
whose measures do not depend on the representation.
