# Unipotent special-fibre kernels from a common closed split torus

Module `Langlands.GroupScheme.IntegralModel.SpecialFibreKernelTorus`.

## Purpose and provenance

In the proof of Kaletha–Prasad, *Bruhat–Tits theory: a new approach* (2023),
Proposition 8.4.15 (printed pp. 306–307, PDF pp. 337–338), unipotence of the
kernel of the special-fibre map `ρ : 𝒢'_k → 𝒢_k` comes from one observation.
The maximal split torus `S` of `G` has a closure in both models. Its special
fibre is a maximal torus of `𝒢'_k`, and `ρ` maps it isomorphically onto the
corresponding torus of `𝒢_k`. So `ρ` is injective on a maximal torus, and the
kernel is unipotent.

This module proves that argument for integral models over a general base. It
does not mention buildings or parahoric subgroups. The statements and their
arrangement are internal design by Worker 4783 for Task 6203, which Worker 282
and Worker 4783 share. No statement here comes from the literature.

Throughout, `R` is a domain with fraction field `K`, and `G` is a group scheme
over `K`. An `IntegralModel R K G` is a group scheme `M.group` over `R` with an
identification `M.genericIso` of its generic fibre with `G`. A model morphism
`ψ : M.Hom N (𝟙 G)` has identity generic fibre, and `ψ.specialFibreMap` is its
base change along `residueBaseMap R : Spec(R/𝔪) → Spec R`. For a homomorphism
`j : 𝒮.toGrp ⟶ M.group`, the map `M.genericTorusMap 𝒮 j` is its generic fibre
followed by `M.genericIso`.

## The split torus of a model, for a fixed splitting

* `SplitTorusClosure.exists_isClosedSubgroup_torus_genericTorusMap_eq_of_bounded`:
  let `R` be a noetherian valuation ring with infinite residue field, and `v` a
  valuation of `K` with `v(a) = 1` for all units `a` of `R`. Let
  `iT : T.toGrp ⟶ G` be a closed subgroup and `e : T.toGrp ≅ 𝔾_m^I` a splitting.
  Suppose the image under `iT` of the character valuation kernel
  `characterValuationKernel v T.toGrp` lies in `M.integralPoints`. Then there is
  a closed subgroup `j : (torus R I).toGrp ⟶ M.group` with
  `M.genericTorusMap (torus R I) j = (genericSplitIso R K I).hom ≫ e.inv ≫ iT`.

  The published
  `SplitTorusClosure.exists_isSplitTorus_genericTorusMap_eq_of_bounded` proves
  the same with an existentially chosen torus and splitting. Here the split
  torus `torus R I` and the comparison with `e` are fixed. Then two models `M`
  and `N` receive closed subgroups from the same torus with the same generic
  fibre.

  *Proof.* Apply the published
  `SplitTorusClosure.exists_isClosedSubgroup_genericTorusMap_eq` with `A = R`
  and `L = K`. Every family `t : I → Rˣ` gives a `K`-point of `T` through `e`.
  This point lies in the character valuation kernel because `v` is one on
  units (`rationalCoeffEquiv_symm_mem_characterValuationKernel`). By hypothesis
  its image lies in `M.integralPoints`. The integrality hypothesis for `K`
  inside `K` is trivial.

## Rigidity and the residue torus

* `Hom.comp_eq_of_genericTorusMap_eq`: let `ψ : M.Hom N (𝟙 G)` and let `𝒮` be a
  commutative group scheme over `R` that is flat. If `j' : 𝒮.toGrp ⟶ M.group`
  and `j : 𝒮.toGrp ⟶ N.group` satisfy
  `M.genericTorusMap 𝒮 j' = N.genericTorusMap 𝒮 j`, then `j' ≫ ψ.hom = j`.

  *Proof.* The generic fibres of `j' ≫ ψ.hom` and `j` agree after composing
  with the isomorphism `N.genericIso.hom`, by `ψ.generic_comm`. The published
  `AbelianScheme.genericFibre_map_injective` says that a morphism from a flat
  scheme over a domain into a separated scheme is determined by its generic
  fibre.

Now let `R` be Henselian local with algebraically closed residue field.

* `isMaximalTorus_specialFibre_of_generic`: let `G` be connected reductive and
  `M` smooth. Let `𝒮` be a split torus and `j : 𝒮.toGrp ⟶ M.group` a closed
  subgroup whose generic torus map is a maximal split torus of `G`. Then the
  special fibre of `j` is a maximal torus of the special fibre of `M`.

  *Proof.* The published `isMaximalSplitTorus_residue_of_generic` (module
  `Langlands.GroupScheme.Torus.HenselianSplitRank`) gives a maximal split torus
  of the special fibre. Over an algebraically closed field every torus is
  split, by the published `IsTorus.isSplitTorus_of_finiteGaloisSplitting` with
  `torusFiniteGaloisSplitting`. The published
  `IsMaximalSplitTorus.isMaximalTorus` then makes it a maximal torus.

## Unipotent kernels

Keep `R` Henselian local with algebraically closed residue field. Let `G` be
connected reductive, `ψ : M.Hom N (𝟙 G)` with `M` smooth, and assume (as
instances) that `kernel ψ.specialFibreMap` is smooth and connected. These two
properties are hypotheses here, not conclusions.

* `isUnipotent_kernel_specialFibreMap_of_splitTorus`: let `𝒮` be a flat split
  torus over `R`, and let `j' : 𝒮.toGrp ⟶ M.group` and
  `j : 𝒮.toGrp ⟶ N.group` be closed subgroups with the same generic torus map,
  a maximal split torus of `G`. Then `IsUnipotent (kernel ψ.specialFibreMap)`.

  *Proof.* By rigidity, `j' ≫ ψ.hom = j`. Base change to the residue field
  shows that the special fibre of `j'` followed by `ψ.specialFibreMap` is the
  special fibre of `j`, a closed immersion and hence a monomorphism. So no
  nonzero cocharacter of the torus is killed
  (`cocharacter_injective_of_mono`). The special fibre of `j'` is a maximal
  torus by `isMaximalTorus_specialFibre_of_generic`. The special fibre of `M` is
  smooth and affine but possibly disconnected, so
  `isUnipotent_kernel_of_isMaximalTorus_of_smooth` (module
  `Langlands.GroupScheme.Absolute.KernelMaximalTorusIdentityComponent`) applies.
* `isUnipotent_kernel_specialFibreMap_of_bounded`: let `R` be in addition a
  noetherian valuation ring, `v` a valuation of `K` that is one on the units of
  `R`, and `iT : T.toGrp ⟶ G` a maximal split torus. Suppose the image of
  `characterValuationKernel v T.toGrp` under `iT` lies in the integral points
  of both `M` and `N`. Then `IsUnipotent (kernel ψ.specialFibreMap)`.

  *Proof.* Choose a splitting `e` of `T`. The first result gives closed
  subgroups `j'` of `M` and `j` of `N` from the same torus `torus R I`, both
  with generic torus map `(genericSplitIso R K I).hom ≫ e.inv ≫ iT`. This
  composite of an isomorphism with `iT` is a maximal split torus. The torus
  `torus R I` is flat and split (`SplitTorusClosure.flat_torus`,
  `SplitTorusClosure.isSplitTorus_torus`). Apply the previous result. The
  infinite residue field needed by the first result follows from algebraic
  closedness.
