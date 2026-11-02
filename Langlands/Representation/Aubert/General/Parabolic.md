# Normalized parabolic induction and Jacquet functors for actual subgroups

Implementation and documentation: Worker 23 (task
`593ef603-6672-4424-976c-14e11e920d9c`, the initial adapter unit of the general
Aubert program `46df6a68-5db4-4428-8044-05151d6ce1f6`).

This module defines normalized parabolic induction `i` and normalized Jacquet
restriction `r` on the full categories of smooth complex representations, for an
actual semidirect decomposition `P = M ⋉ U` of subgroups of a group `G`. It also
gives their action on equivariant maps, the normalizing characters, Levi-in-Levi
versions, conjugation transports, and an identification of `i ∘ r` with Worker
194's unnormalized term `Aubert.SubgroupTransition.term` when `U` is
unimodular. It constructs no reductive structure. The subgroups, the
decomposition, closedness of `U` and unimodularity are inputs. For a connected
reductive group they are supposed to come from the owners of the shared Chapter V
objects (see "Scope" below).

## Ambient group and universes

The functor sections assume `G : Type uG` with `[Group G] [TopologicalSpace G]
[LocallyCompactSpace G] [NonarchimedeanGroup G]`. `NonarchimedeanGroup` already
includes `IsTopologicalGroup`, and no Hausdorff hypothesis is used. The
coefficients are `ℂ`, so every category is `SmoothRep.{0, uG, _} ℂ _`, the
published full subcategory of smooth objects of Mathlib's `Rep`. Jacquet
restriction keeps the carrier universe `uV`. Induction raises it to `max uG uV`,
so `inductionJacquetFunctor.{uG, uV}` is an endofunctor of
`SmoothRep.{0, uG, max uG uV} ℂ G`.

## Semidirect decompositions and the projection

`IsSemidirectDecomposition P M U : Prop` is the conjunction of four conditions:
`M ≤ P`, `U ≤ P`, `P ≤ Subgroup.normalizer (U : Set G)`, and Mathlib's
`(M.subgroupOf P).IsComplement' (U.subgroupOf P)`. The last condition says that
multiplication `M × U → P` is bijective, so every `p ∈ P` is uniquely `m * u`.
`of_isComplement'_symm` builds the same predicate from the complement in the
order `U * M`, using Mathlib's `IsComplement'.symm`. The accessors are
`levi_le`, `unipotent_le`, `le_normalizer`, `levi_le_normalizer` and
`isComplement'`, and `normal` gives normality of `U.subgroupOf P`
(`Subgroup.normal_subgroupOf_iff_le_normalizer`).

`IsSemidirectDecomposition.projection h : P →* M` is the composite of three
maps: the quotient map `P → P ⧸ U`, Mathlib's
`IsComplement'.QuotientMulEquiv : P ⧸ U ≃* M.subgroupOf P`, and
`Subgroup.subgroupOfEquivOfLe`. The proved laws are:

* `projection_levi`: `m ↦ m` on `M`;
* `projection_unipotent`: `U` maps to `1`;
* `projection_eq_one_iff`: the kernel is exactly `U`;
* `projection_inv_mul_mem`: `(proj p)⁻¹ * p ∈ U`;
* `projection_eq_iff`: `proj p = m ↔ m⁻¹ * p ∈ U`;
* `projection_mul`: `proj (m * u) = m`.

Continuity of the projection is neither assumed nor needed.

## Normalizations

Write `δ(x)` for the published Haar modulus
`HaarModulus.closedNormalizerCharacter U hU x` of conjugation `u ↦ x u x⁻¹` on
the closed subgroup `U`, for `x` in the normalizer. Its scaling convention is
`c • μ.map α = μ`, that is `μ(x S x⁻¹) = δ(x) μ(S)`. This is the
Bernstein–Zelevinsky 1977 §1.7 convention (see `Group/HaarModulus.md`). For
`B ⊂ GL_2` it gives `δ(diag(a,b)) = |a/b|`. The half characters are the
published `closedHalfCharacter` (positive real square root, embedded in `ℂ`) and
`closedInverseHalfCharacter` (its inverse). Their kernels are open
(`isOpen_ker_closed...`), so twisting preserves smoothness.

* `normalizedJacquetFunctor U M hU hMU`, written `r`, is the published
  coinvariant functor `Jacquet.Localization.smoothFunctor U 1 M hMU
  (isInvariant_one ..)` followed by `SmoothRep.twistFunctor` with
  `closedInverseHalfCharacter U hU M hMU`. The carrier is the actual quotient
  `V ⧸ span {ρ(u)v - v}`. `normalizedJacquetFunctor_obj_representation` and
  `normalizedJacquetFunctor_obj_apply` record the action,
  `m · [v] = δ(m)^{-1/2} [ρ(m) v]`. `normalizedJacquetFunctor_map_mk` records
  the action on maps, `[v] ↦ [f v]`. All three hold by `rfl`.
  `jacquetFunctor h hU` is this functor with `hMU := h.levi_le_normalizer`.
* `inductionCharacter U P hU hPU` is the smooth character
  `closedHalfCharacter U hU P hPU` of `P`: `δ^{1/2}` taken directly on `P`.
* `inflationFunctor h` is `SmoothRep.toRep ⋙ Rep.resFunctor h.projection`
  (Mathlib's restriction along `P →* M`).
* `normalizedInductionFunctor h hU`, written `i`, is `inflationFunctor h`
  followed by the published `Induction.normalizedSmoothInductionFunctor P
  (inductionCharacter ..)`. That functor twists by the character and takes
  smooth vectors of the covariant functions with right translation.
  `inducingRepresentation h hU A` is the twisted inflated representation
  `p ↦ δ(p)^{1/2} σ(proj p)`.
  `normalizedInductionFunctor_obj_representation` identifies the object with
  `Induction.smoothInduced P (inducingRepresentation ..)`.
  `normalizedInductionFunctor_covariant` gives
  `f (p g) = δ(p)^{1/2} σ(proj p) (f g)`,
  `normalizedInductionFunctor_obj_apply` gives right translation, and
  `normalizedInductionFunctor_map_eval` gives postcomposition on maps.
* `inductionJacquetFunctor h hU := jacquetFunctor h hU ⋙
  normalizedInductionFunctor h hU`.

### Source identification

For every decomposition, `r` is the localization `r_{U,1}` (`θ = 1`) of
Bernstein–Zelevinsky 1977 §1.8(b) (printed p. 444), with `M`-action
`m · [v] = mod_U(m)^{-1/2} [ρ(m) v]`. Renard VI.1.2 (printed p. 135, PDF p. 141)
writes `r^G_P(π) = π_N ⊗ δ_P^{1/2}`. The Remarque on printed p. 136 says his
`δ_P` is the inverse of the usual one, because of his modular-function choice in
II.3.7, so this is the same twist.

For induction, the identification with the sources holds only when `U` is
unimodular. BZ77 §1.8(a)(1) requires `f(u m g) = θ(u) mod_U(m)^{1/2} ρ(m) f(g)`.
With `θ = 1` this factor is trivial on `U`: it is the Levi half modulus inflated
along the projection. The generic `i` here uses `δ(p)^{1/2}` on all of `P`, the
half modulus of conjugation by `p` on `U`. At `u ∈ U` it equals `δ(u)^{1/2}`,
which need not be `1` for an arbitrary closed `U`.

Under the named hypothesis `IsUnimodularModulus U hU`, the two characters
agree by `closedHalfCharacter_eq_comp_projection` (next subsection). In that
case `i` is BZ's normalized induction on the full space of smooth functions,
`I_{U,1}` in BZ's notation. `IsUnimodularModulus U hU` follows from
`IsLimitOfCompactSubgroups U` by
`isUnimodularModulus_of_isLimitOfCompactSubgroups`. This covers the actual
parabolic application, where `U` is a unipotent radical (Renard V.5.2(iii)).

In the same unimodular case, Renard's `i^G_P(τ) = Ind^G_P(τ ⊗ δ_P^{-1/2})`
(VI.1.2, printed p. 135, with his inverted `δ_P`) agrees with `i`, and his
covariance (VI.1.2.3) on p. 136 is `normalizedInductionFunctor_covariant`.
Aubert's Définition 1.5 (p. 2180, citing [BZ, 2.3]) uses these normalized
functors for parabolic subgroups. There `P \ G` is compact, and BZ77 1.9(e)
identifies `I_{U,1}` with the compactly supported `i_{U,1}`.

Outside the unimodular case, `i` is a generic construction with no counterpart
in these sources. This module keeps the character on `P` distinct from the
inflated Levi character there.

### δ on `P` versus the inflated Levi modulus

The induction character is the modulus of conjugation by `P` on `U`, taken on
`P` itself. `closedHalfCharacter_levi` proves by `rfl` that it restricts on `M`
to the Levi half modulus `closedHalfCharacter U hU M ..`.
`IsUnimodularModulus U hU : Prop` is the named hypothesis that every inner
automorphism of `U` has modulus `1`. Under it, `closedHalfCharacter_unipotent`
shows the induction character is trivial on `U`, and
`closedHalfCharacter_eq_comp_projection` shows it equals the Levi half modulus
composed with the projection.

`isUnimodularModulus_of_isLimitOfCompactSubgroups` derives `IsUnimodularModulus
U hU` from the published `Jacquet.Localization.IsLimitOfCompactSubgroups U`
(every compact subset of `U` lies in a compact subgroup). This is the argument
of Renard VI.1.2, Remarques (p. 136): `δ_P` is trivial on compact subgroups.
Given `u ∈ U`, take a compact subgroup `K ∋ u` of `U`. The modulus restricted to
`K` has open kernel (`isOpen_ker_closedNormalizerCharacter`), so the kernel has
finite index `n` in the compact group `K` (`Subgroup.quotient_finite_of_isOpen`).
Hence `δ(u)^n = 1` in the positive reals, and `δ(u) = 1`
(`pow_eq_one_iff_of_nonneg`). For the actual unipotent radical,
`IsLimitOfCompactSubgroups` is the statement that the radical is the union of
its compact open subgroups (Renard V.5.2(iii), printed p. 123); it is not proved
here.

### Comparison with the unnormalized term

`inducingRepresentation_jacquet_eq` proves, under `IsUnimodularModulus`, that
the inducing representation of `i (r A)` equals
`SubgroupTransition.inducing P U h.le_normalizer A.representation`, the
unnormalized quotient action of `P` on the `U`-coinvariants. The proof writes
`p = m u` with `m = proj p`. It shows `[ρ(mu)v] = [ρ(m)v]`, using the published
`relations_stable` and `sub_mem_relations`, and it cancels
`δ(p)^{1/2} δ(m)^{-1/2} = 1`. `intertwiningOfEq` is the identity intertwiner
between equal representations. `inductionJacquetTermIso h hU hδ A` is the
resulting isomorphism in `SmoothRep` from `(inductionJacquetFunctor h hU).obj A`
to `SmoothRep.of (SubgroupTransition.term P U ..)`.
`inductionJacquetTermIso_hom_eval` and `inductionJacquetTermIso_inv_eval` say
that it and its inverse keep every induced function. `inductionJacquetTermIso_natural`
proves naturality in the ambient representation: for `φ : A ⟶ B` it intertwines
`i (r φ)` with `SubgroupTransition.termMap P U h.le_normalizer (hom φ)`. Both
sides send an induced function `f` to `x ↦ [φ (v)]` where `f x = [v]`.

## Levi-in-Levi functors

`subgroupOfContinuousEquiv hLM : L.subgroupOf M ≃ₜ* L` is the continuous form of
`Subgroup.subgroupOfEquivOfLe`. Take a closed `M`, subgroups `Q`, `L ≤ M`, `N`
of `G`, and a decomposition
`IsSemidirectDecomposition (Q.subgroupOf M) (L.subgroupOf M) (N.subgroupOf M)`
inside `M`. This is Renard VI.1.4 (printed p. 136): for standard `P ⊂ Q`,
`L ∩ P = M (L ∩ N)` is a parabolic of the Levi `L`. Then:

* `leviNormalizedInductionFunctor hM hLM h hN : SmoothRep ℂ L ⥤ SmoothRep ℂ M`
  is the pullback along `subgroupOfContinuousEquiv hLM` (the published
  `SmoothRep.pullbackFunctor`), followed by `normalizedInductionFunctor` inside
  the group `M`. It uses `letI := hM.locallyCompactSpace` and the closed set
  `N.subgroupOf M` (the preimage of `N`).
* `leviNormalizedJacquetFunctor` is `jacquetFunctor` inside `M`, followed by the
  pullback along the inverse equivalence.

The transitivity isomorphisms `i^G_Q ∘ i^Q_P ≅ i^G_P` and the matching ones for
`r` (Renard VI.1.4) are not proved here. They are representation-theoretic
proof obligations of this task, to be stated as Prop targets in a separate
submission and listed in the task's separate source-to-declaration and
dependency note. Neither is part of this unit.

## Conjugation transports

`conjugationEquiv g hMN : N ≃ₜ* M` is `x ↦ g⁻¹ x g`, for subgroups with
`x ∈ N ↔ g⁻¹ x g ∈ M` (that is, `N = g M g⁻¹`). `conjugationFunctor g hMN` is
the published `SmoothRep.pullbackFunctor` along it, so
`(ᵍσ)(x) = σ(g⁻¹ x g)` (`conjugationFunctor_obj_apply`). This section assumes
only `[IsTopologicalGroup G]`.

## Smooth contragredient

The smooth contragredient on the actual smooth categories is reused unchanged:
`SmoothRep.contragredientFunctor : (SmoothRep.{uR,uG,uV} R G)ᵒᵖ ⥤
SmoothRep.{uR,uG,max uR uV} R G` (module `Category.Contragredient`), whose
action on maps is precomposition (`hom_contragredientFunctor_map`). Its K0
adapter is in `Aubert.General.AlternatingOperator`.

## Scope and status of the inputs

This module implements the generic construction layer. It does not assert that
the inputs come from a connected reductive group. For the actual group the
inputs have three different statuses. The task's separate dependency note, not
part of this unit, will itemize them:

* Actual objects and their intrinsic laws. The standard parabolics
  `P_I = M_I N_I` (Renard V.3.8, V.4.2) and the Levi decompositions on rational
  points (V.3.1) are to be supplied as actual subgroups and theorems by the
  algebraic-groups program `2b5e4a00` (child `8ace819d`, not public at Library
  `0ebc0efd`). They are not assumptions of this unit. For the published dynamic
  parabolics, `Aubert.General.DynamicParabolic` proves the decomposition
  outright.
* External structural inputs imported without proof in Renard Chapter V. These
  are the topology of `G(F)` and its properties (V.2.1; Conrad task
  `886bf565`), and the compact-subgroup facts of V.5.2 (citing [24], §2.1),
  including that unipotent radicals are limits of compact subgroups.
* Retained in-book proof obligations. These are unimodularity of `N_I` and the
  modulus formulas (V.5.4), and the transitivity and Levi-in-Levi comparisons
  (V.3.10–V.3.11, VI.1.4). `IsUnimodularModulus` is a temporary named hypothesis
  of the comparison lemmas. It is not an allowed external input: it is derived
  here from `IsLimitOfCompactSubgroups` by
  `isUnimodularModulus_of_isLimitOfCompactSubgroups`.

Their owners (tasks `2b5e4a00`, `6edfb074`, `425af515`, `f33d727f`, and Conrad
`886bf565` for the topology) received requests from Workers 1180, 76, 194, 165,
1186, 6 and 8. Nothing here discharges an external input.

## Sources

* I. N. Bernstein and A. V. Zelevinsky, *Induced representations of reductive
  p-adic groups I*, Ann. Sci. ENS 10 (1977), registered as
  `bernstein-zelevinsky-1977-induced-i`: §1.7 (modulus), §1.8 (normalized
  induction and localization), printed pp. 443–445.
* D. Renard, *Représentations des groupes réductifs p-adiques* (2026 version),
  registered as `renard-2026-representations-groupes-reductifs-padiques`:
  VI.1.1–VI.1.4, printed pp. 134–136 (PDF pp. 140–142; printed = PDF − 6).
* A.-M. Aubert, *Dualité dans le groupe de Grothendieck de la catégorie des
  représentations lisses de longueur finie d'un groupe réductif p-adique*,
  Trans. AMS 347 (1995), registered as `aubert-1995-duality`: p. 2180
  (normalized BZ functors).
