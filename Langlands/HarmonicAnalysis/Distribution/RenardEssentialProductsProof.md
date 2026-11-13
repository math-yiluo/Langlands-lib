# Renard II.3.13: proof of the essentially compact product statements

The theorem `RenardEssentialProducts.statements` proves exactly
`Langlands.HarmonicAnalysis.Distribution.RenardEssentialProducts.Statements.{uG}`
in its unrestricted group universe. Source: Renard, *Représentations des
groupes réductifs p-adiques*, French version of 9 July 2026, II.3.13,
printed pp.54–55 / PDF pp.60–61; registered as
`renard-2026-representations-groupes-reductifs-padiques`. The proof uses
the helper modules `RenardEssentialProductsKernels`,
`RenardEssentialProductsRight` and `RenardEssentialProductsLeft`. Their
paired Markdown explains the analytic identities and the two one-sided
products.

## Agreement on the intersection

`two_sided_eval` covers `T` left essentially compact and `U` right
essentially compact. It proves the source's final identity
`T(rconv U f) = U(lconv T f)`, that is `T_x U_y f(xy) = U_y T_x f(xy)`.
Choose a compact-open `K` fixing `f` on both sides, and take `k` with
`kμ = U * e_K`. The identity then follows from:

- `rconv U f = f ⋆ ǩ`;
- `rightHecke_eval`, which gives `T(f ⋆ ǩ) = (kμ)(lconv T f)`;
- `(U * e_K)(lconv T f) = U(lconv T f)`, because `lconv T f` is right
  `K`-invariant.

This uses only the right essential compactness of `U` and the left
essential compactness of `T`.

`toR` and `toL` are the inclusions of `essentiallyCompact μ` into the two
one-sided submodules. By `pR_eq_pL` the right and left products agree on
the intersection. Therefore `pEDist_mem` shows that the right product of two
elements of the intersection lies in the intersection. `pE` is this product,
bundled as a complex-bilinear map.

## The final statement

- `pE_algebraLaws`:
  - associativity comes from `pR_assoc`;
  - the unit `dirac 1` comes from `pR_dirac_left` and `pR_dirac_right`;
  - extension of compact convolution comes from `pR_compact`;
  - agreement with both Hecke actions comes from `pR_hecke_right` and
    `pR_hecke_left`.

  All lifts are the actual distributions. `compact_mem_essentiallyCompact`
  places compact distributions in the intersection.
- `pE_spec`: let `pr` and `pl` be arbitrary products satisfying the right
  and left specifications. Uniqueness (`eq_pR`, `eq_pL`) identifies them
  with `pR` and `pL`. The required lifts are `toR T`, `toR U`, `toL T` and
  `toL U`, and agreement is `pR_eq_pL`.
- `eq_pE`: any product satisfying the two-sided specification equals `pR`
  on the lifts. Those lifts are forced to be `toR T` and `toR U`, so the
  product equals `pE`.
- `statements` assembles `right_existsUnique`, `left_existsUnique` and,
  for every compatible pair `pr` and `pl`, existence and uniqueness of `pE`.

The proof does not change the published statement pair or its imports. It
adds no countability, unimodularity or universe restriction. Besides the
published Library results named in the helper Markdown, it uses only
Mathlib's integration and Haar measure lemmas. The axioms used are
`propext`, `Classical.choice` and `Quot.sound`.
