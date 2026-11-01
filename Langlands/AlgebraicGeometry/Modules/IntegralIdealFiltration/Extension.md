# Killed sections extending multiples of the witness section

Author: Worker 716. This is an internal helper module for
`Langlands.AlgebraicGeometry.Modules.coherentIntegralIdealFiltration`. Its predicates
are derived devices for the proof.

## Predicates

Fix a witness `w` (module `Witness`), an open `W` of `X` and `a ∈ Γ(Z, i⁻¹ W)`.

- `w.Agrees W a t` (for `t : Γ(Q, W)`): on every affine open `V ≤ W ⊓ U`, `t|_V` equals
  `w.mu V (a|_{i⁻¹ V})`, the multiple of `s` by `a`.
- `w.InT W a`: some `t : Γ(Q, W)` is killed by `J` and agrees with `a`. In words, the
  multiple `a · s`, defined on `W ∩ U`, extends to a section over `W` killed by the ideal
  of the closed set.

## Results

- `agrees_unique`: two killed sections agreeing with the same `a` are equal. Their
  difference is killed and vanishes on all affine opens inside `W ⊓ U`, so it vanishes by
  the witness's torsion property.
- `Agrees.res` and `InT.res`: compatibility with restriction.
- `Agrees.add`, `InT.add`, `agrees_zero`, `inT_zero`: additivity.
- `Agrees.smul`, `InT.smul`: multiplication by `r ∈ Γ(X, W)` on `Q` corresponds to
  multiplication by `i.app W r` on `Z`.
- `inT_of_disjoint`: if `W` misses `Zc`, every `a` is admissible with the zero extension,
  since `s` vanishes on affine opens disjoint from `Zc`.
- `inT_of_local`: admissibility is local on `W`. The local extensions are compatible on
  overlaps by `agrees_unique`, and they glue (`TopCat.Sheaf.existsUnique_gluing'`). The
  glued section is killed (`killed_of_cover`) and agrees with `a`, which is checked near
  each point on smaller affine opens using `mu_res`.
- `inT_iff_forall`: `InT W a` holds if and only if `InT W' (a|)` holds for every open `W'`
  with `i⁻¹ W' ≤ i⁻¹ W`. For the forward direction, use `inT_of_local` on `W'`. Near points
  of `Zc` one has `W' ⊓ W`, because such points lie in `W`; away from `Zc` use
  `inT_of_disjoint`.
- `inT_one_U`: the constant `1` over `U` is admissible, with extension `s`.
- `mem_J_of_smul_eq_zero`: for `g ∈ Γ(X, U)` and `r ∈ Γ(X, D(g))`, if `r • s|_{D(g)} = 0`
  then `r` lies in the ideal of `Zc` on `D(g)`. Write `r = b / g ^ k`
  (`IsAffineOpen.isLocalization_basicOpen`); then `b • s` vanishes on `D(g)`, so
  `g ^ m * b ∈ p`. If `g ∈ p`, the ideal contains the unit `g` and is the unit ideal;
  otherwise `b ∈ p` and `r` is `b` times a unit.
