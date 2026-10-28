# The complex of compatible families of graded morphisms

Author: Worker 61. Built on `Langlands.Cohomology.DivisibleSystem.HomSystem`
(`cochainTransition`, `cochainTransition_refl`, `cochainTransition_trans`,
`δ_cochainTransition`, `cochainTransitionLinear`,
`cochainTransitionLinear_apply`, `homComplexSystem`, `homComplexLimit`,
`smoothHomComplexSystem`), on `Langlands.Cohomology.LinearHomComplex`
(`LinearHomComplex.complex`, the Hom complex of two cochain complexes as a
complex of `R`-modules) and on `Langlands.Cohomology.DivisibleSystem`
(`DivisibleSystem`, `SmoothRepComplexDivisibleSystem`). From Mathlib it uses
the cochain lemmas `δ_add`, `δ_smul`, `δ_shape` and `δ_δ`, `LinearMap.proj`,
`Submodule.subtype`, `HomologicalComplex.congr_hom` and
`IsLimit.conePointUniqueUpToIso` with its lemmas
`conePointUniqueUpToIso_hom_comp` and `conePointUniqueUpToIso_inv_comp`.

Everything is in the namespace `Langlands.Cohomology.DivisibleSystem`, except
`smoothCompatibleHomComplex`, which is in `Langlands.Cohomology`.

`R` is a ring, `C` an `R`-linear abelian category with Hom-universe `v`, and
`T`, `W` are `ℓ`-divisible systems in `CochainComplex C ℤ`, with levels
`T m = T.obj m`. Recall from HomSystem: a cochain of degree `n` from `T m` to
`W m` (`CochainComplex.HomComplex.Cochain`) is a family of morphisms
`T m ^ p ⟶ W m ^ q` for `p + n = q`; for `m' ≤ m`,
`cochainTransition T W h z` is the cochain from `T m'` to `W m'` obtained
from `z` by reduction along the projections, and `homComplexSystem R T W` is
the inverse system `m ↦ Hom^•(T m, W m)` of Hom complexes
(`LinearHomComplex.complex R (T m) (W m)`) with these transitions.
`homComplexLimit R T W` is its limit `limit (homComplexSystem R T W)`, an
object of `CochainComplex (ModuleCat R) ℤ` chosen by Mathlib's `limit`, about
which HomSystem proves nothing.

This module gives an explicit complex of compatible families, proves it is a
limit of `homComplexSystem R T W`, and hence identifies it with
`homComplexLimit R T W`.

## Compatible families

- `compatibleCochains R T W n`: the `R`-submodule of the product
  `∀ m : ℕ, Cochain (T m) (W m) n` (with the product module structure)
  consisting of the families `z` with `cochainTransition T W h (z m) = z m'`
  for all `m' ≤ m` and `h : m' ≤ m`. It is closed under addition, zero and
  scalar multiplication because `cochainTransitionLinear R T W h n` is
  `R`-linear and agrees with `cochainTransition T W h`
  (`cochainTransitionLinear_apply`).
- `mem_compatibleCochains_iff`: membership unfolds to this condition.
- `mem_compatibleCochains_iff_succ`: a family is compatible if and only if
  `cochainTransition T W (Nat.le_succ m) (z (m + 1)) = z m` for every `m`,
  i.e. compatibility along consecutive levels. One direction is a special
  case. For the other, write `m = m' + k` and induct on `k`: for `k = 0` use
  `cochainTransition_refl`; for `k + 1`, split the transition along
  `m' ≤ m' + k ≤ m' + k + 1` with `cochainTransition_trans`, apply the
  consecutive condition at `m' + k`, and then the induction hypothesis.
- `δ_mem_compatibleCochains R T W n n' hz`: applying the differential
  `δ n n'` of the Hom complexes levelwise to a compatible family gives a
  compatible family, because `δ_cochainTransition` says that the transitions
  commute with `δ`.
- `compatibleδ R T W n n'`: this levelwise differential, as an `R`-linear map
  `compatibleCochains R T W n →ₗ[R] compatibleCochains R T W n'`
  (additivity and linearity levelwise from `δ_add` and `δ_smul`);
  `compatibleδ_apply_coe` states that the level-`m` entry of
  `compatibleδ R T W n n' z` is `δ n n' (z m)` (by definition).

## The complex and its evaluations

- `compatibleHomComplex R T W : CochainComplex (ModuleCat.{v} R) ℤ`: the
  complex with degree-`n` term `compatibleCochains R T W n` and differentials
  `compatibleδ`. The shape condition and `d ≫ d = 0` hold levelwise by
  `δ_shape` and `δ_δ`.
- `compatibleEvalLinear R T W m n`: evaluation `z ↦ z m` of a compatible
  family of degree `n` at level `m`, the restriction of the projection
  `LinearMap.proj m` to the submodule.
- `compatibleEval R T W m`: the chain map
  `compatibleHomComplex R T W ⟶ LinearHomComplex.complex R (T m) (W m)` with
  components `compatibleEvalLinear`; it commutes with the differentials by
  definition of `compatibleδ`. `compatibleEval_f_apply` states
  `(compatibleEval R T W m).f n z = z m`.

## The limit

- `compatibleHomComplexCone R T W`: the cone over `homComplexSystem R T W`
  with apex `compatibleHomComplex R T W` and projections
  `compatibleEval R T W m`. The cone condition for `m' ≤ m` says
  `cochainTransition T W h (z m) = z m'`, which is the compatibility of `z`.
- `compatibleHomComplexLift R T W s n`: for a cone `s` over
  `homComplexSystem R T W` with apex `s.pt`, the `R`-linear map
  `s.pt.X n →ₗ[R] compatibleCochains R T W n` sending `x` to the family of
  its images `(s.π.app (op m)).f n x`. This family is compatible by the cone
  condition `s.w` in degree `n`.
- `compatibleHomComplexIsLimit R T W`: `compatibleHomComplexCone R T W` is a
  limit cone. The lift of a cone `s` has components
  `compatibleHomComplexLift R T W s n`; it is a chain map because each
  projection of `s` is one, it factors `s` through the evaluations by
  definition, and it is unique because a morphism into
  `compatibleHomComplex R T W` is determined by its composites with the
  evaluations.
- `compatibleHomComplexIsoLimit R T W`:
  `compatibleHomComplex R T W ≅ homComplexLimit R T W`, the comparison
  isomorphism `IsLimit.conePointUniqueUpToIso` between the cone of the
  previous item and Mathlib's chosen limit cone.
- `compatibleHomComplexIsoLimit_hom_π R T W m`: the forward isomorphism
  followed by the limit projection at `m` is `compatibleEval R T W m`.
- `compatibleHomComplexIsoLimit_inv_eval R T W m`: the inverse isomorphism
  followed by `compatibleEval R T W m` is the limit projection at `m`.
  Both are `simp` and `reassoc` lemmas.

So the inverse limit of the Hom complexes `homComplexLimit R T W` is, up to
this canonical isomorphism, the complex whose degree-`n` term is the module
of compatible families of degree-`n` cochains and whose differential is
applied level by level.

## Smooth representations

`R : Type u` is a commutative ring, `G : Type v` a topological group, and
`T`, `W` are `ℓ`-divisible systems of `ℤ`-graded cochain complexes of smooth
representations (`SmoothRepComplexDivisibleSystem.{v, u, w} R G ℓ`).

- `smoothCompatibleHomComplex R G T W`: `compatibleHomComplex R T W`, a
  complex in `CochainComplex (ModuleCat.{w} R) ℤ` (an abbreviation). Its
  degree-`n` terms are compatible families of graded `G`-equivariant
  `R`-linear maps, and the results above apply to it, with
  `smoothHomComplexSystem R G T W`, which is `homComplexSystem R T W` by
  definition, as the inverse system.

## Provenance and interpretation

Harris, *Galois properties of cohomological automorphic forms on GL(n)*,
J. Math. Kyoto Univ. 39-2 (1999), proof of Proposition 4.10, printed
pp.311-312 (one-based PDF pages 13-14). The passages are quoted in
`Langlands/Cohomology/DivisibleSystem/HomSystem.md`: Harris writes "We need
to check that the complexes used to obtain the spectral sequences (4.9)
satisfy a Mittag-Leffler condition as m varies", identifies these complexes
as (4.10.2), and studies the maps (4.10.3) `T_{m+1}(j, ẽ) → T_m(j, ẽ)`.
The inverse system of Hom complexes and its relation to Harris's complexes
are discussed there; this module adds nothing to that identification.

Harris does not describe the inverse limit of the complexes (4.10.2) in the
cited passages. The description of the limit of `homComplexSystem` by
compatible families, the reduction to consecutive levels and the proofs are
ours. This is the standard description of limits of complexes of modules
degreewise; it is proved here directly as `compatibleHomComplexIsLimit`
rather than derived from Mathlib's limit API. The consecutive-level
criterion `mem_compatibleCochains_iff_succ` corresponds to Harris's use of
the maps (4.10.3) for consecutive `m`.

## Scope

The module proves no surjectivity of the transitions (Harris's surjectivity
of (4.10.3) uses freeness, which is not assumed), no Mittag-Leffler
condition, and nothing about the cohomology of `compatibleHomComplex` or of
`homComplexLimit`. It does not relate compatible families to morphisms of
`ℓ`-divisible systems (compatibility with the inclusions), to Hom complexes
of inverse limits of the systems, or to Ext groups, and it does not identify
Harris's complexes (4.10.2) with Hom complexes of `ℓ`-divisible systems.

Source registration: Harris 1999,
`harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`, SHA-256
`525a222c4489ee9d3fe86a52c6c17ffb30fcc7c31f24c16a64669e9615085b26`.

Dependencies are the modules named above, pinned to Lean 4.34.0 and Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`.
