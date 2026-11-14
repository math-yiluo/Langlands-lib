# The parahoric Hecke operator and the extension of the spherical section

Author: Worker 392.

This helper module of the proof of
`Langlands.Conductor.OrderedUnramifiedSphericalCyclicityStatement` (see
[`OrderedUnramifiedSphericalCyclicity`](../OrderedUnramifiedSphericalCyclicity.md))
proves **Step A**. It is the only place where the ordering of the parameters is used.
Let `S` be a subrepresentation of the principal series of rank `n + 2` with
parameters `z` that contains the spherical section, and let `‖z_i‖` be weakly
increasing. Then `S` contains the extension by zero
([`Extension`](Extension.md)) of the spherical section of rank `n + 1` with
parameters `tailParam z`. The definitions are internal auxiliary constructions, with
no literature source. All declarations are in `Langlands.Conductor.SphericalCyclicity`.
The notation is from [`Parahoric`](Parahoric.md), [`Weyl`](Weyl.md) and
[`Counting`](Counting.md). `𝓀` is the residue field
`IsLocalRing.ResidueField 𝒪`. It is finite by Mathlib's instance, and the module
fixes a local `Fintype` instance on it.

## A reindexing lemma

`sum_mul_reindex`: let `H ≤ G` be a subgroup, `g : ι → G` a family over a finite type,
and `φ` a right `H`-invariant function. Suppose that for every `c` there is `c'` with
`(g c')⁻¹ k g c ∈ H`, and that `(g c₁)⁻¹ g c₂ ∈ H` implies `c₁ = c₂`. Then
`Σ_c φ(x k g c) = Σ_c φ(x g c)`. The chosen map `c ↦ c'` is injective, hence
bijective on a finite type, and `φ(x k g c) = φ(x g c')`.

## Residue classes

- `resLift` is a chosen integral lift of each residue class (`Function.surjInv`), with
  `residue_resLift`. `liftVec c` is the coordinatewise lift of
  `c : Fin m → 𝓀`, with `liftVec_mem`.
- `lowerUnip_mem_integral`: `L(y) ∈ K` for integral `y`.
- `weyl_mul_lowerUnip_self` and `weyl_mul_lowerUnip_succ`: the first column of
  `w_j L(y)` has `1` in row `j` and `y_i` in row `i + 1 ≠ j`.
- `residue_eq_zero_iff_val`: `residue x = 0 ↔ v x < 1`. `residue_eq_iff`: two
  integral elements have the same residue if and only if their difference has
  valuation `< 1`. `val_liftVec_lt_one_iff` (`v (liftVec c i) < 1 ↔ c i = 0`) and
  `val_liftVec_eq_one` follow.

## The Hecke translates

- `heckeElt ϖ c = t' L(liftVec c)` for `c : Fin (n + 1) → 𝓀`.
- `conj_mem_integral_of_parahoric`: `t'⁻¹ x t' ∈ K` for `x ∈ J`.
  `tPrime_mul_lowerUnip`: `t' L(y) = L(ϖ y) t'`.
- `heckeElt_inj`: `(g_(c₁))⁻¹ g_(c₂) = L(s(c₂) - s(c₁))`. If it lies in `J`, the
  differences have valuation `< 1`, so `c₁ = c₂`.
- `heckeElt_perm`: for `k ∈ J` and every `c` there is `c'` with
  `(g_(c'))⁻¹ k g_c ∈ J`. Proof: `k g_c = t' Y`, where
  `Y = t'⁻¹ (k L(ϖ s(c))) t' ∈ K` and `v(Y_00) = 1` (`parahoric_head`). Put
  `u = colT Y / Y_00`, which is integral, and let `c'` be its residue. Then
  `(g_(c'))⁻¹ k g_c = L(-s(c')) Y`. Its first-column tail is
  `-Y_00 (s(c') - u)`, which has valuation `< 1`.
- `card_residue`: `Fintype.card 𝓀 = q`, by `IsResidueCardinality`.

## The Hecke operator

- `hecke f = Σ_{c : Fin (n+1) → 𝓀} ρ(g_c) f`. `value_hecke` evaluates it as
  `Σ_c f(x g_c)`. `hecke_mem`: it preserves every subrepresentation.
  `hecke_parahoricInvariant`: it preserves `IsParahoricInvariant`, by
  `sum_mul_reindex` with `heckeElt_perm` and `heckeElt_inj`.
- `value_weyl_mul_lowerUnip`: for parahoric-invariant `f`,
  `f(w_j L(s(c))) = f(w_(cellIndex j c))`, where `cellIndex j c = max j (top c)`. This
  is the cell lemma `value_eq_weyl` with `m = max j (top c)`. If `top c ≤ j`, row `j`
  has entry `1`. Otherwise row `top c` has entry `s(c_(top c - 1))`, a unit by
  `ne_zero_of_top_eq`. All lower rows have entries `s(0)` of valuation `< 1`, by
  `eq_zero_of_top_le`.
- `weylEval f = (f(w_j))_j`, as a linear map to `Fin (n + 2) → ℂ` (`weylEval_apply`).
- `heckeConst q z = √q^(n+1) Π_i z_i`, nonzero by `heckeConst_ne_zero`.
- `weylEval_hecke`: for parahoric-invariant `f`,
  `weylEval (hecke f) = heckeConst • (cellMatrix (n + 2) q z *ᵥ weylEval f)`. Proof:
  `w_j g_c = τ_j (w_j L(s(c)))` (`weyl_mul_tPrime`), so
  `(hecke f)(w_j) = χ_z(τ_j) Σ_c f(w_(cellIndex j c))`. By `sum_cellIndex` this is
  `χ_z(τ_j) z_j q^j (cellMatrix *ᵥ weylEval f)_j`, and
  `χ_z(τ_j) z_j q^j = heckeConst` (`normalizedCharacter_lamJ`).

## Step A

- `parahoricInvariants` is the submodule of parahoric-invariant vectors.
  `sphericalSection_parahoricInvariant` holds because `J ⊆ K`.
- `extend_sphericalSection_parahoricInvariant`: the extension `h_J` of the spherical
  section of rank `n + 1` is parahoric invariant. This uses `cellFun_mul_parahoric`
  and `sphericalSection_mul_integral`, applied to the integral matrix
  `lowGL (L(cellVec x) k)`.
- `not_isUnit_det_low_weyl`: for `j ≠ 0`, the lower-right block of `w_j` has a zero
  row, so `w_j` is not in the cell.
- `weylEval_extend_sphericalSection`: `weylEval h_J = Pi.single 0 1`, since `w_0 = 1`
  lies in the cell with value `1`, and `w_j` for `j ≠ 0` does not.
- `extend_sphericalSection_mem`: let `V = S ⊓ parahoricInvariants` and
  `W = weylEval(V) ⊆ ℂ^(n+2)`. The spherical section lies in `V`, and its image is the
  all-ones vector (`sphericalSection_integral`, since `w_j ∈ K`). For `f ∈ V`, the
  vector `heckeConst⁻¹ • hecke f` lies in `V` and maps to `cellMatrix *ᵥ weylEval f`.
  So `W` is `cellMatrix`-stable. `q ≥ 2` holds because a finite field has at least
  two elements. The norms of `z` are monotone, so `eq_top_of_cellMatrix_stable`
  ([`LinearAlgebra`](LinearAlgebra.md)) gives `W = ⊤`. Hence some `f ∈ V` has
  `weylEval f = Pi.single 0 1 = weylEval h_J`, and `eq_of_weyl` gives `f = h_J`, so
  `h_J ∈ S`.
