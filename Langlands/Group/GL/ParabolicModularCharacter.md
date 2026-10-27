# The modular character of a standard block parabolic

Author: Worker 235.

This module works in `Langlands.GeneralLinear.BlockShape` for a block shape
`B : BlockShape (n + 1)` over a field `𝕜`. Its main theorem,
`modularCharacter_eq`, identifies Mathlib's modular character of the actual
upper block parabolic `P = B.parabolic 𝕜` with a Levi character `δ` applied to
the Levi projection. The theorem is stated for any `δ : B.Levi 𝕜 →* ℝ≥0ˣ`
that scales Haar measure on the unipotent radical in the sense of
`Langlands.GLBlockModulusHaarStatement`. The module is a helper for
`Langlands.Representation.Induction.CompactScalarProof`, which uses
`δ = T.leviModulus B` and `Langlands.glBlockModulusHaar`. It defines only the
auxiliary objects listed below.

## Provenance

The content is derived. Casselman, *Introduction to the theory of admissible
representations of p-adic reductive groups* (draft May 1, 1995, source
`casselman-1995-admissible-representations`), §3.1 p. 32, writes the modulus
character of `P = M N` as `δ_P(mn) = |det Ad_n(m)|`. This module proves the
corresponding statement for Mathlib's `modularCharacter` and standard GL block
parabolics. It takes the effect of Levi conjugation on Haar measure of `N` as
the hypothesis `hδ` rather than as a determinant formula. The proof below is
not taken from the source.

## Main statement

```text
theorem modularCharacter_eq (δ : B.Levi 𝕜 →* ℝ≥0ˣ)
    (hδ : ∀ [MeasurableSpace (B.unipotentRadical 𝕜)] [BorelSpace (B.unipotentRadical 𝕜)]
      (μ : Measure (B.unipotentRadical 𝕜)) [IsHaarMeasure μ] (m : B.Levi 𝕜),
      μ.map (B.leviAction 𝕜 m) = ((δ m : ℝ≥0)⁻¹) • μ)
    (q : B.parabolic 𝕜) :
    modularCharacter q = (δ (B.leviProjection 𝕜 q) : ℝ≥0)
```

The section `Modular` assumes that `𝕜` is a nonarchimedean local field with
`T2Space 𝕜`, that `GL_(n+1)(𝕜)` is second countable and that `P` is locally
compact. The hypothesis `hδ` has exactly the shape of the conclusion of
`GLBlockModulusHaarStatement` for a fixed realization. It keeps that
statement's inverse: pushing Haar measure forward by `Ad(m)` multiplies it by
`δ(m)⁻¹`.

## Section `Parts`: algebra of the Levi decomposition

Write `ι = B.leviInParabolic 𝕜`, `π = B.leviProjection 𝕜` and
`u(p) = B.unipotentPart 𝕜 p`, which is `p ι(π p)⁻¹` by definition.

- `unipotentPart_val` and `unipotentPart_mul_leviInParabolic`:
  `u(p) = p ι(π p)⁻¹` and `u(p) ι(π p) = p`.
- `leviProjection_radical_mul` and `unipotentPart_radical_mul`: for `x` in the
  radical, `π(x p) = π(p)` and `u(x p) = x u(p)`.
- `leviProjection_conj_of_commute` and `unipotentPart_conj_of_commute`: if `m`
  commutes with every Levi element, then `π(ι(m)⁻¹ p ι(m)) = π(p)` and
  `u(ι(m)⁻¹ p ι(m)) = B.leviAction 𝕜 m⁻¹ (u p)`.

## Section `Integral`: integral points

Here `𝕜` has a valuation `v = ValuativeRel.valuation 𝕜`. `K` is the level-zero
subgroup `Conductor.levelSubgroup 𝕜 n 0`.

- `exists_unit_valuation_mul_le_one f`: for a finite family `f`, some unit `t`
  has `v t ≤ 1` and `v (t * f i) ≤ 1` for all `i`. Take `t = ∏ c(f i)`, where
  `c(a) = 1` if `v a ≤ 1` and `c(a) = a⁻¹` otherwise.
- `powBlockScalar : 𝕜ˣ →* B.Levi 𝕜` is a new auxiliary definition. It sends `t`
  to the Levi element with the scalar `t ^ i` on block `i`. It is distinct from
  the Library's `BlockShape.blockScalar` (in `BlockIwahoriDefinitions`), which
  sends a tuple of units to the ambient general linear group.
  `leviEmbedding_powBlockScalar` computes its embedding as a diagonal matrix.
  `conj_powBlockScalar_apply` gives the entries of the conjugate `s⁻¹ g s`:
  `t^(-i(x)) g_xy t^(i(y))`, where `i(x)` is the block of coordinate `x`.
- `valuation_conj_powBlockScalar_le_one`: let `g` lie in the unipotent subgroup,
  with `v t ≤ 1` and `v (t g_xy) ≤ 1` for all `x, y`. Then every entry of
  `s⁻¹ g s` is integral. In a block `(i, j)` with `i < j`, the entry is
  `(t g_xy) t^(j-i-1)`. Diagonal blocks are identity blocks, and blocks below
  the diagonal vanish.
- `mem_levelSubgroup_zero_iff`: `g ∈ K` exactly when all entries of `g` and of
  `g⁻¹` are integral (`levelSubgroup_zero`, `mem_integralSubgroup`).
- `exists_conj_powBlockScalar_mem`: every `g` in the unipotent subgroup is
  conjugated into `K` by some block scalar. Apply the first item to the
  entries of `g` and `g⁻¹`, and use `(s⁻¹ g s)⁻¹ = s⁻¹ g⁻¹ s`.
- `leviEmbedding_leviProjection_mem` and `mem_levelSubgroup_iff_parts`: a
  parabolic element `q` lies in `K` exactly when its block-diagonal part
  `ι(π q)` and its radical part `u(q)` both lie in `K`. Diagonal blocks of an
  integral matrix are integral; apply this to `q` and `q⁻¹`.
- New auxiliary objects: `integralParabolic`, the subgroup `P ∩ K` of `P`;
  `leviIntegral`, the set of `p` with `ι(π p) ∈ K`; and `radicalIntegral`, the
  set of radical elements in `K`. `coe_integralParabolic` gives
  `P ∩ K = leviIntegral ∩ u⁻¹(radicalIntegral)`.
- `conj_preimage_integralParabolic`: for a central Levi element `m`,
  `{p | ι(m)⁻¹ p ι(m) ∈ P ∩ K}` equals
  `leviIntegral ∩ u⁻¹(Ad(m⁻¹)⁻¹(radicalIntegral))`.

## Section `Modular`: the modular character

- Topology: `continuous_unipotentPart` (via `decompositionHomeomorph`) and
  `continuous_leviAction_apply` (the subspace topology of the radical, with
  `MulAut.conjNormal_apply`). `isOpen_integralParabolic`,
  `isOpen_leviIntegral` and `isOpen_radicalIntegral` show the integral sets
  are open. `isCompact_integralParabolic` holds because `P` is closed and `K`
  is compact.
- `modularCharacter_unipotent`: `modularCharacter = 1` on the radical. For a
  radical element `x`, choose a block scalar `s` with `s⁻¹ x s ∈ P ∩ K`. The
  modular character is a homomorphism to a commutative group, so it takes the
  same value on `x` and `s⁻¹ x s`. It is `1` on the compact open subgroup
  `P ∩ K` (`ModularCompactAverage.modularCharacter_eq_one_of_mem`).
- `map_unipotentPart_restrict_eq_smul ν μN`: for Haar measures `ν` on `P` and
  `μN` on the radical, `(ν.restrict leviIntegral).map u = c • μN` for some
  `c : ℝ≥0`. Left translation by a radical element `x` preserves
  `leviIntegral`, and `u(x p) = x u(p)`. So the pushforward is left invariant
  (`Measure.restrict_map`, `map_mul_left_eq_self`). It is finite on compact
  sets: if `E` is compact, every point of `leviIntegral ∩ u⁻¹(E)` is
  `u(p) ι(π p)`, so the set lies in the compact product `E · (P ∩ K)`.
  Uniqueness of Haar measure (`isMulLeftInvariant_eq_smul`) gives `c`.
- `modularCharacter_leviInParabolic_of_commute δ hδ m hm`: if `m` commutes
  with the whole Levi factor, then `modularCharacter (ι m) = δ m`. Use the
  Borel structures and Haar measures `ν`, `μN`, and `c` from the previous item.
  Then `ν(P ∩ K) = c μN(radicalIntegral)`. The conjugated set
  `{p | ι(m)⁻¹ p ι(m) ∈ P ∩ K}` has `ν`-measure
  `modularCharacter (ι m) · ν(P ∩ K)` (`measure_preimage_conj`). By
  `conj_preimage_integralParabolic`, the same measure is
  `c · μN(Ad(m⁻¹)⁻¹ radicalIntegral) = c · (map Ad(m⁻¹) μN)(radicalIntegral)`.
  By `hδ` at `m⁻¹`, this equals `δ(m) · c · μN(radicalIntegral)`. The common
  factor `ν(P ∩ K)` is positive and finite, so it cancels
  (`ENNReal.mul_left_inj`).
- `modularCharacter_leviInParabolic δ hδ m`: `modularCharacter (ι m) = δ m`
  for every Levi element. Both `modularCharacter ∘ ι` and `δ` (coerced to
  `ℝ≥0`) are homomorphisms on the finite product `B.Levi 𝕜 = ∏ GL_(size j)`,
  so they agree once they agree on each factor (`MonoidHom.pi_ext`). On block
  `j`, the character `χ_j(x) = modularCharacter(ι(single_j x)) · δ(single_j x)⁻¹`
  of `GL_(size j)(𝕜)` is trivial on scalar matrices. Indeed, `single_j` of a
  scalar commutes with every Levi element (`scalar_commute`), so the previous
  item applies. `RankinSelberg.GeneralLinearUnimodularity.character_eq_one`
  then shows `χ_j = 1`.
- `modularCharacter_eq`: write `q = u(q) ι(π q)`. The radical factor
  contributes `1`, and the Levi factor contributes `δ(π q)`.

## Scope

The rank is written as `n + 1`, as in `Conductor.levelSubgroup`. The theorem
covers every block shape, including the one-block shape, where `P` is all of
`GL_(n+1)` and the radical is trivial. It proves nothing about induced
representations.
