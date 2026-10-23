# Compact coefficients on `G°` imply product-Levi quasicuspidality

Authors: Worker 252 and Worker 324. Worker 252 supplied the complete Lean proof
and its proof description; Worker 324 checked the source correspondence,
complete declaration type and allowed axioms, and prepared this proof pair
for independent review. The Lean proof is unchanged from Worker 252's draft.

The closing theorem `Langlands.CuspidalSupport.leviHarishChandraConverseTheorem`
proves exactly `Langlands.CuspidalSupport.LeviHarishChandraConverseTheorem.{uF,uV}`
from the published `Langlands.Representation.CuspidalSupport.HarishChandraConverseStatement`.
This is the (4) ⇒ (1) direction of Bernstein–Zelevinsky (1976), Theorem 3.21.
The named theorem
`Langlands.CuspidalSupport.HarishChandra.isLeviQuasicuspidal_of_hasCompactSmoothDualCoefficients`
states the implication for an arbitrary smooth representation `ρ` of
`B.Levi F.Carrier` on a complex module, without bundling.

## Scope and conventions

The closing theorem keeps every quantifier of the target: every prime `p`,
actual `F : PadicField.{uF} p`, compatible `T : F.TopologicalData`, every rank
`n` (including zero), every `B : BlockShape n`, and every
`A : SmoothRep.{0,uF,uV} ℂ (B.Levi F.Carrier)`. The universes `uF` and `uV`
remain independent. It installs `T.topology` and applies the named theorem to
`A.representation` and `A.isSmooth`. No admissibility, finite-length,
finite-dimension, irreducibility, semisimplicity, central-character or
positive-rank hypothesis is used. No arbitrary theorem-valued input is assumed.

Write `G = B.Levi F.Carrier`, `G° = determinantUnitSubgroup T B`, and
`ρ°` for `determinantUnitRestriction T B ρ`. The hypothesis
`HasCompactSmoothDualCoefficients ρ°` is used only as stated. For a vector `v`
and a functional `ℓ'` that is smooth for the restricted dual `ρ°.dual`, the
coefficient `g ↦ ℓ' (ρ° g v)` on `G°` has compact support.

## Implemented proof

Let `S : BlockRefinement B` satisfy `refinedParabolic F.Carrier B S ≠ ⊤`.
We must show that the coinvariant quotient by `refinedUnipotent F.Carrier B S`
is a subsingleton. That is, every vector `v` lies in `Jacquet.relations`.

1. **One long block.** `exists_two_le_length_of_refinedParabolic_ne_top`:
   if every refined block `S i` had length at most one, every block-upper
   condition would be vacuous and the refined parabolic would be `⊤`. So some
   block `i₀` has `2 ≤ (S i₀).length`.
2. **Reduction to one factor.** Let `ρ₀ = ρ ∘ Pi.mulSingle i₀` be the restriction
   of `ρ` to the `i₀`-th factor `GL(B.size i₀, F)`. It is smooth by
   `isSmooth_comp` and `continuous_mulSingle`. `relations_mulSingle_le` shows
   that the relations of `ρ₀` for `(S i₀).unipotentSubgroup` lie inside the
   relations of `ρ` for `refinedUnipotent`. Each generator `ρ₀ u w - w` is a
   generator for `Pi.mulSingle i₀ u`, which lies in the refined radical
   (`Subgroup.mulSingle_mem_pi`). So it suffices to prove that every `v`
   becomes zero in the Jacquet module of `ρ₀` for `(S i₀).unipotentSubgroup`.
3. **A product subgroup fixing `v`.** Smoothness gives an open subgroup `H`
   fixing `v`. By `nhds_pi` and `Filter.mem_pi'`, `H` contains a box of
   neighbourhoods `O j` of `1`. The published `BlockShape.blockIwahoriBasis`
   gives, for each `j`, a compact open `K j ⊆ O j` with a block Iwahori
   factorization for `S j`. Then `N = Subgroup.pi univ K` is a compact open
   subgroup of `G` (`isOpen_set_pi`, `isCompact_univ_pi`) that fixes `v`. In
   particular `v` is `K i₀`-fixed for `ρ₀`.
4. **A contracting element of `G°`.** `exists_strictlyContracting_determinantNorm_eq_one`
   takes `b` from `BlockShape.deepChamberNonempty`, which is strictly contracting
   by `IsDeeplyContracting.strict`. Put `m = B.size i₀`,
   `d = det (blockScalar b)`, and `a = b ^ m · (const d⁻¹)`. Multiplying by a
   constant tuple leaves every `blockScalarRatio` unchanged, so `a` is still
   strictly contracting. Moreover `blockScalar a = (blockScalar b)^m · scalar d⁻¹`
   (`blockScalar_mul`, `blockScalar_const`), and `determinantNorm_scalar` gives
   normalized determinant norm `|d|^m · |d|^{-m} = 1`. Put `t = blockScalar a`.
   By `mulSingle_mem_determinantUnitSubgroup`, every `Pi.mulSingle i₀ (t ^ r)`
   lies in `G°`.
5. **Jacquet kernel via compression.** The published
   `Jacquet.blockPowerKernel_eq_jacquetKernel`, applied to `ρ₀`, `K i₀` and `a`,
   identifies the Jacquet kernel on `K i₀`-fixed vectors with
   `powerKernelSup ρ₀ (K i₀) t`. `compressedAction_blockScalar_pow` shows, by
   induction with `Jacquet.blockCompressedAction_mul`, that
   `(compressedAction t)^r = compressedAction (blockScalar (a ^ r))`. Here
   `IsWeaklyContracting` is preserved under products. So it suffices to find `r`
   with `averageMap ρ₀ (K i₀) (ρ₀ (t ^ r) v) = 0`.
6. **Linear algebra (BZ76 §2.40).** `exists_eq_zero_of_eventually_dual` states:
   if every `ℓ ∈ Module.Dual ℂ V` eventually vanishes on a sequence `w r`, then
   some `w r = 0`. The proof extends a linearly independent spanning subset `s`
   of the range to a basis. If `s` is finite, the finitely many coordinate
   functionals vanish simultaneously at some `r`, so `w r = 0`. If `s` is
   infinite, the functional equal to `1` on `s` is nonzero at infinitely many
   terms, a contradiction. We apply this with
   `w r = averageMap ρ₀ (K i₀) (ρ₀ (t ^ r) v)`.
7. **Smoothing the functional.** For any `ℓ`, put
   `ℓ' = ℓ ∘ averageMap ρ N`. By `averageMap_apply_mem`, averaging over `N`
   absorbs the action of elements of `N`, so `ℓ'` is fixed by the compact open
   subgroup `N.comap (determinantUnitInclusion T B)` of `G°`
   (`continuous_determinantUnitInclusion`). So `ℓ'` is smooth for `ρ°.dual`,
   and the hypothesis makes `g ↦ ℓ' (ρ° g v)` compactly supported on `G°`.
   `N` itself need not lie in `G°`.
8. **Escape from compact sets.** `eventually_blockScalar_pow_notMem` shows that
   powers of a strictly contracting block scalar with at least two blocks
   eventually leave every compact subset of `GL(m, F)`. The continuous function
   `φ g = |g_{yy}| · |(g⁻¹)_{xx}|` uses the first diagonal positions `x`, `y` of
   blocks `0` and `1` (normalized absolute value, `continuous_normalizedAbsHom`).
   It is bounded on a compact set and equals `u^r` on `t ^ r`, where `u > 1` is
   the normalized absolute value of `a 1 · (a 0)⁻¹`. Applying this to the image
   of the support under the continuous projection `G° → GL(m, F)`, `g ↦ g i₀`,
   shows that eventually `Pi.mulSingle i₀ (t ^ r)` lies outside the support, so
   `ℓ' (ρ (Pi.mulSingle i₀ (t ^ r)) v) = 0`
   (`image_eq_zero_of_notMem_tsupport`).
9. **Orbit comparison.** `orbit_pi_eq_orbit_single`: when a vector is fixed by
   `Subgroup.pi univ K`, then after acting by `Pi.mulSingle i₀ t'` its `N`-orbit
   equals its `K i₀`-orbit under `ρ₀`. For each `g ∈ N`, the product identity is
   `g * Pi.mulSingle i₀ t' = Pi.mulSingle i₀ (g i₀) * Pi.mulSingle i₀ t' * Function.update g i₀ 1`,
   and the last factor fixes `v`. Unfolding `orbitMean`, the `N`-average of
   `ρ (mulSingle i₀ (t ^ r)) v`
   equals its `K i₀`-average under `ρ₀`. So
   `ℓ (w r) = ℓ' (ρ (Pi.mulSingle i₀ (t ^ r)) v)`, which is eventually zero.

Steps 6–9 give some `r` with `w r = 0`. Step 5 then puts the class of `v` in
`powerKernelSup`, so `v` is zero in the `ρ₀`-Jacquet module. Step 2 finishes the
proof.

## Relation to the source

BZ76 proves (4) ⇒ (2) ⇒ (1). It first passes from compactness on `G°` to
compactness modulo the centre on `G`, then applies Lemma 3.22. The implemented
route never leaves `G°`. The contracting element is normalized to lie in `G°`
(step 4), and the converse of Lemma 3.22 is replaced by the published block
compression identity `blockPowerKernel_eq_jacquetKernel` on one Levi factor.
The averaged-orbit criterion of §2.40 enters only through its linear-algebra
core (step 6) and the smoothing of `ℓ` (step 7). No compactness-modulo-centre
statement, Cartan decomposition or finiteness of `G/(G° Z)` is used.

Source: I. N. Bernshtein and A. V. Zelevinskii, *Representations of the group
GL(n,F) where F is a non-Archimedean local field*, Russian Math. Surveys 31:3
(1976), 1–68 (literature ID `bernstein-zelevinsky-1976-representations-gln`),
§§2.39–2.40 (p. 26) and §§3.18–3.23 (pp. 34–35).
The retained original is
`/home/taskhub/central-library/Bernstein-Zelevinsky--Representations of the group GL(n,F) where F is a non-archimedean local field (survey)--1976.pdf`,
SHA256 `72dc22eb9991112936a88327f00d0f02a16a2bf8747518ca0ecfeeadd188e50c`.
Worker 324 directly read these sections on PDF pages 26, 34 and 35.
No applicable errata note was present in the current Library.

The source's finite-representation condition in §2.40 means compact support
of coefficients against smooth contragredient vectors, not finite dimension.
Its §2.39 coefficient is `g ↦ ℓ (ρ° g⁻¹ v)`; the Library uses
`g ↦ ℓ (ρ° g v)`. These differ by inversion, a homeomorphism of `G°`, so
compactness of support is equivalent. The proof uses the restricted smooth
dual directly and needs no comparison with the original group's smooth dual.

## Rank zero

No case split is needed. For `n = 0` the shape has no blocks. The argument of
step 1 then shows that every refined parabolic is `⊤`, so there is no proper
refinement to treat.

## Dependencies

Imports: the published `HarishChandraConverseStatement`,
`Jacquet.BlockPowerKernelProof`, `Group.GL.BlockIwahoriBasis` and
`Geometric.RefinementDefinitions`. All helper theorems are public and live in
the namespace `Langlands.CuspidalSupport.HarishChandra`. No imported pair is
modified. The proof uses only the axioms `propext`, `Classical.choice` and
`Quot.sound`.
