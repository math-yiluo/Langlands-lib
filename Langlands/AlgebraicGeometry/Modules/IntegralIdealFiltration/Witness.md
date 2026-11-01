# Sections extending multiples of a minimal associated section

Author: Worker 716. This is an internal helper module for
`Langlands.AlgebraicGeometry.Modules.coherentIntegralIdealFiltration`. It packages the
output of `exists_minimal_witness` as derived data.

## The witness

`Witness Q` is a structure. It has an affine open `U`, a section `s : Γ(Q, U)` and a prime
`p` of `Γ(X, U)`, with `ann : c • s = 0 ↔ c ∈ p`. Its field `tor` is the torsion property of
`exists_minimal_witness`. `nonempty_witness` provides a witness for every nonzero
quasi-coherent `Q` on a noetherian scheme.

For `w : Witness Q`:

- `w.pt = U.fromSpec p` is the point and `w.Zc` its closure (a closed set).
- `w.J = vanishingIdeal w.Zc` is the vanishing ideal sheaf.
- `w.Z = w.J.subscheme` is the reduced closed subscheme, with closed immersion
  `w.i = w.J.subschemeι`.

Basic facts:

- `pt_mem_U`, `pt_mem_Zc`, and `pt_mem_of_mem_Zc`: every open meeting `Zc` contains the
  point.
- `J_U`: `w.J.ideal U = p`.
- `s_killed`: `s` is killed by `J`.
- `ideal_eq_top`: the ideal is the unit ideal on affine opens disjoint from `Zc`.
- `range_i`: the image of `w.i` is `Zc` (Mathlib's `range_subschemeι`).
- The instance `IsIntegral w.Z` comes from the Library's
  `Scheme.isIntegral_subscheme_vanishingIdeal`, since the closure of a point is irreducible.
- `app_surjective`, `app_eq_zero_iff`: on an affine open `V`, `w.i.app V` is surjective with
  kernel `w.J.ideal V` (Mathlib's `subschemeι_app_surjective`, `ker_subschemeι_app`).

## Multiplication of `s` by functions on `Z`

For an affine open `V ≤ U` and `a ∈ Γ(Z, i⁻¹ V)`, `w.mu V hV a` is `r • s|_V` for a chosen
lift `r ∈ Γ(X, V)` of `a`. `mu_eq` shows that every lift gives the same value: two lifts
differ by an element of the kernel `J.ideal V`, which kills `s|_V`. Consequently:

- `mu` is additive (`mu_add`, `mu_zero`);
- it is `Γ(X, V)`-linear (`mu_mul`: `mu (i.app r * a) = r • mu a`);
- `mu 1 = s|_V` (`mu_one`);
- it is compatible with restriction to smaller affine opens (`mu_res`, via the Library's
  `QuasicoherentLocal.app_rres`).
