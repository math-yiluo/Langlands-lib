# Stage rings of the end ring

Module `Langlands.Correspondence.Laumon.EndRingStages`. As before, `ι : k[x] → endRing k` is the
chart coordinate `x ↦ t`, and `p(b)` denotes the evaluation of `p ∈ k[x][Y]` at `b ∈ endRing k`
through `ι`.

## Definitions

These are internal definitions, the local rings of plane curves at points over `x = 0`, realized
inside `endRing k`.

- `stageResidue k b : k[x][Y] → k` is `p ↦ (p(b) mod t)`, and `stagePrime k b` its kernel, a
  prime ideal (`stagePrime_isPrime`).
- `StageLocalization k b` is the localization of `k[x][Y]` at `stagePrime k b`, and
  `stageMap k b` the map `p / q ↦ p(b) q(b)⁻¹` to `endRing k`; it is defined because `q ∉
  stagePrime k b` means that `q(b)` is a unit (`isUnit_eval₂_of_mem_primeCompl`).
- `stage k b`, the *stage ring* of `b`, is the range of `stageMap k b`: the subring of the
  fractions `p(b) / q(b)` with `q(b)` a unit (`mem_stage_iff`). `stageProj k b` is
  `stageMap k b` with codomain `stage k b`, which is surjective (`stageProj_surjective`).

## Elementary properties

- `stageMap_algebraMap`, `stageProj_algebraMap`, `eval₂_mem_stage`,
  `endChartCoordinate_mem_stage`, `self_mem_stage`: `stage k b` contains every `p(b)`, in
  particular `ι a` and `b`.
- `isUnit_of_isUnit_stageMap`, `mem_stage_of_mul_mem`: a fraction whose image is a unit of
  `endRing k` is a unit of the localization, so if `s ∈ stage k b` is a unit of `endRing k` and
  `x s ∈ stage k b`, then `x ∈ stage k b`.
- `eval₂_mem_of_mem`, `stage_le_stage`: a subring containing `ι(k[x])` and `c` contains all
  `p(c)`; hence `b ∈ stage k b'` implies `stage k b ≤ stage k b'`.
- `endResidue_sub_endChartCoordinate_C`, `exists_eval₂_eq`: with `c` the residue of `b`,
  division by `Y - c` writes `p(b) = a + (b - c) q(b)` with `a = p(c) ∈ k[x]`, `a(0)` the residue
  of `p(b)`, and `p'(b) = q(b) + (b - c) q'(b)`.

## Simple points

Let `b` be a simple point (`IsSimplePoint k b`, module
`Langlands.Correspondence.Laumon.EndRingSimplePoints`), a root of `G` with `G'(b)` a unit.

- `exists_sub_eq_endUniformizer_mul`: `b - c = t u` with `u ∈ stage k b`. Writing
  `0 = G(b) = a + (b - c) q(b)`, the unit `G'(b) ≡ q(b) (mod t)` makes `q(b)` a unit, and
  `a(0) = 0`, so `a = x a'` and `u = -ι a' / q(b)`.
- `mem_stage_of_endUniformizer_mul_mem`, `mem_stage_of_endUniformizer_pow_mul_mem`: if
  `t y ∈ stage k b` with `y ∈ endRing k`, then `y ∈ stage k b`. If `t y q(b) = p(b)`, then
  `p(b) = a + t u p₂(b)` with `a(0) = 0`, so `p(b) = t (ι a' + u p₂(b))` and
  `y q(b) = ι a' + u p₂(b)`.
- `mem_stage_of_mem_adjoin`: every `x ∈ endRing k` lying in `k(t)(b)` lies in `stage k b`. As `b`
  is algebraic over `k(t)`, `x = P(b)` with `P ∈ k(t)[Y]`; clearing denominators,
  `d x = N(b)` with `d ∈ k[x]` nonzero and `N ∈ k[x][Y]`. Writing `d = x ^ j d'` with `d'(0) ≠ 0`,
  `t ^ j (ι d' x) ∈ stage k b`, so `ι d' x ∈ stage k b` by division by `t`, and `x ∈ stage k b`
  as `ι d'` is a unit.

Since the fractions `p(b) / q(b)` lie in `k(t)(b)`, the stage ring of a simple point `b` is in
fact `endRing k ∩ k(t)(b)`; the module states and uses only the inclusion
`endRing k ∩ k(t)(b) ⊆ stage k b`.

## Common stage rings

`exists_isSimplePoint_mem_stage`: any two elements `x₁, x₂` of `endRing k` lie in the stage ring
of a common simple point. The field `k(t)` is infinite (`infinite_ratFunc`) and `endField k` is
separable over it (`isSeparable_endField`), so `k(t)(x₁, x₂) = k(t)(γ)` for some `γ` (Mathlib's
`Field.primitive_element_inf_aux`). Some `t ^ M γ` lies in `endRing k`
(`exists_pow_mul_mem_endRing`); it is separable over `k(t)`, so it lies in `k(t)(b)` for a
simple point `b` (`exists_isSimplePoint`). Then `x₁, x₂ ∈ k(t)(γ) ⊆ k(t)(b)`, and
`mem_stage_of_mem_adjoin` applies.

Provenance: internal; standard commutative algebra (localizations of `k[x][Y]`, primitive
elements of finite separable extensions).
