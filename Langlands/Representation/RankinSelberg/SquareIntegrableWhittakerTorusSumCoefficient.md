# Whittaker values on the antitone torus cone as smooth matrix coefficients

Authors: Worker 906; Worker 70 (reused conjugation lemmas); Workers 277 and 307
(Levi commutation and factorization pattern).

This module is the first helper for the proof of
`Langlands.RankinSelberg.SquareIntegrableWhittakerTorusSumStatement`
(see [`SquareIntegrableWhittakerTorusSumProof`](SquareIntegrableWhittakerTorusSumProof.md)).
It contains internal helper lemmas only; none of them is a published statement.
The argument is the standard one that, on an antidominant cone of torus elements,
a Whittaker function `g ↦ ℓ (π g v)` agrees with a smooth matrix coefficient. The
particular route below (averaging over a principal level with its Iwahori
factorization) is internal to this project.

## Averaging a functional over a compact open subgroup

Section `Averaging` works for any topological group `G` with a Borel measurable
structure, a complex representation `ρ` of `G` on `V`, a compact open subgroup `K`
and a linear functional `ℓ` on `V`. The measure is
`RankinSelberg.normalizedCompactOpenHaar K hK`, the Haar measure giving `K` mass one.

- `isLocallyConstant_apply_inv`: for a smooth vector `w`, the function
  `g ↦ ℓ (ρ g⁻¹ w)` is locally constant. If an open subgroup `H` fixes `w`, the
  function is constant on each coset `H g`.
- `integrableOn_apply_inv`: if `ρ` is smooth, this function is integrable on `K`,
  since it is continuous and `K` is compact.
- `averagedFunctional ρ hρ K hK ℓ` is the linear functional
  `w ↦ ∫_K ℓ (ρ g⁻¹ w) dg`; `averagedFunctional_apply` unfolds it.
- `averagedFunctional_apply_mul`: for `k ∈ K`, the average of `ρ k w` equals the
  average of `w`. The proof writes the integral over `K` as the integral of an
  indicator function and uses left invariance of Haar measure under `k⁻¹`.
- `averagedFunctional_mem_fixedVectors`, `averagedFunctional_mem_smoothVectors`: the
  average is fixed by `K` in the full dual representation `ρ.dual`, hence smooth.
- `averagedFunctional_apply_of_forall`: if `ℓ (ρ g⁻¹ w) = ℓ w` for every `g ∈ K`, then
  the average of `w` is `ℓ w`, because `K` has mass one.

## Principal levels and the antitone torus cone

Section `Conjugation` takes a field `k` with a valuative relation, an element `ϖ` of
valuation at most one, the torus element `Iwasawa.torus ϖ lam`
(diagonal entries `ϖ ^ lam i`), and the principal level
`Conductor.principalLevelSubgroup k m r` of `GL_(m+1)(k)`.

The conjugation steps reuse Worker 70's public
`GeneralLinear.principal_upper_conj` and `GeneralLinear.principal_lower_inv_conj`
from `Langlands.Group.GL.PrincipalLevelDominance`. Their entry-ideal support stays
in that module.

- `torus_conj_upper_mem`: for antitone `lam`, the conjugate `a u a⁻¹` of an
  upper-unipotent element `u` of the level by `a = torus ϖ lam` lies in the level.
- `torus_inv_conj_lower_mem`: for antitone `lam`, the conjugate `a⁻¹ l a` of a
  lower-unipotent element `l` of the level lies in the level.

  Both rewrite the torus element as a singleton block scalar
  (`torus_eq_blockScalar`) and use `ratio_mem_integer` from
  `Langlands.Group.GL.PrincipalLevelDominance`.
- `torus_commute_levi`: torus elements commute with the diagonal (singleton Levi)
  subgroup. The proof is the commutation step of `exists_dominant_sandwich` in
  `Langlands.Group.GL.PrincipalLevelDominance`.
- `apply_inv_torus_eq`: let `r > 0`, let `v` be fixed by the level, and let
  `ℓ (π u w) = ℓ w` for every upper-unipotent `u` in the level. Then for every `g` in
  the level and every antitone `lam`, with `a = torus ϖ lam`,
  `ℓ (π(g⁻¹) π(a) v) = ℓ (π(a) v)`.

  Proof: the Iwahori factorization `principalLevelSubgroup_iwahoriProduct_surjective`
  of the level for the singleton block shape writes `g = l d u`, with `l` lower
  unipotent, `d` diagonal and `u` upper unipotent, all in the level. Since `a` commutes
  with `d`,

  `g⁻¹ a = u⁻¹ a (d⁻¹ (a⁻¹ l⁻¹ a))`.

  The last factor lies in the level by `torus_inv_conj_lower_mem`, so it fixes `v`.
  The factor `u⁻¹` is absorbed by `ℓ`.

## Smooth functionals agreeing with a Whittaker functional

`exists_smooth_eq_on_antitone F T m`: let `π` be a smooth representation of
`GL_(m+1)(F)`, `ℓ ∈ glFunctionals ψ m π` a standard Whittaker functional, `v ∈ V`, and
`ϖ` of valuation at most one. Then there are `r > 0` and a linear functional `L` such
that:

- the level `K(r)` fixes `v`;
- `L` is a smooth vector of `π.dual`;
- `L (π g w) = L w` for every `g ∈ K(r)` and every `w`;
- `L (π(torus ϖ lam) v) = ℓ (π(torus ϖ lam) v)` for every antitone `lam`.

Proof: choose `r₁ > 0` with `K(r₁)` inside an open subgroup fixing `v`, using
`Conductor.exists_pos_principalLevelOpenSubgroup_subset`. The kernel of the standard
character `standardCharacter ψ m` is open in the upper-unipotent group, since the
character is continuous (`isOpen_ker_of_continuous_complex_character`). Choose `r₂`
with every upper-unipotent element of `K(r₂)` in that kernel. On the level
`r = max r₁ r₂`, `ℓ` is invariant under upper-unipotent elements of the level. The
functional `L` is `averagedFunctional` for the compact open subgroup
`principalLevelOpenSubgroup F m r`. The last property follows from
`averagedFunctional_apply_of_forall` and `apply_inv_torus_eq`.
