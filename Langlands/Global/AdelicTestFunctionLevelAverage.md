# Averaging adelic test functions over a compact open level

Module `Langlands.Global.AdelicTestFunctionLevelAverage` (namespace
`Langlands.Global.AdelicGroupPoints`).

## Definitions

- `LevelCosets L L'` is the coset space `L ⧸ L'.subgroupOf L` of two subgroups `L'`, `L` of
  the finite adelic points `G(𝔸_f)`, that is, the left cosets of `L ∩ L'` in `L` (written
  `L / L'` when `L' ≤ L`).
- `levelAverage L L' h` is the function
  `g ↦ [L : L ∩ L']⁻¹ ∑ᶠ_c h(l_c⁻¹ g)` on `G(𝔸)`, where `c` runs over `LevelCosets L L'`,
  `l_c = c.out` is the chosen representative of `c`, included in `G(𝔸)` by `ofFinite`, and
  `[L : L ∩ L'] = Nat.card (LevelCosets L L')`. The definition uses a `finsum` and needs no
  hypothesis. When there are infinitely many cosets, `Nat.card` is zero and the function is
  zero. Each result below states its own hypotheses; finiteness of the cosets is assumed only
  where it is listed.

## Results

- `finite_levelCosets`: if `L` is compact and `L'` is open, then `L ∩ L'` has finitely many
  cosets in `L`
  (Mathlib's `Subgroup.quotient_finite_of_isOpen` in the compact group `L`).
- `translate_eq_of_mk_eq`: if `h` is left invariant under `L'`, two representatives of the
  same coset give the same translate `h(l⁻¹ ·)`.
- `levelAverage_mul_left`: if `h` is left invariant under `L'`, then `levelAverage L L' h` is
  left invariant under `L`, with no finiteness hypothesis. Left translation by `l ∈ L`
  permutes the cosets (`MulAction.toPerm`), and the previous lemma replaces each
  representative.
- `levelAverage_eq_sum`: with a `Fintype` instance the `finsum` is the finite sum.
- `isAdelicTestFunction_levelAverage`: if `L` is open, `LevelCosets L L'` is finite, `h` satisfies
  `IsAdelicTestFunction` and `h` is left invariant under `L'`, then `levelAverage L L' h`
  satisfies `IsAdelicTestFunction`, with `L` as its subgroup of left invariance. Continuity
  and right invariance (under the subgroup of `h`) pass to finite sums of left translates;
  the infinite slice at `b` of the translate by `l_c⁻¹` is the slice of `h` at `l_c⁻¹ b`
  (`pair_mul`), and plot-smooth functions form a submodule; the support lies in the finite
  union of the translates `l_c · tsupport h`.
- `exists_common_level`: for finitely many test functions and a compact open `L` there is an
  open `L' ≤ L`, with finitely many cosets, under which all of them are left invariant
  (intersect `L` with their subgroups of left invariance).
- `rightConvolution_translate`: for every `l ∈ G(𝔸_f)`,
  `δ(h(l⁻¹ ·)) f (x) = δ(h) f (x l)`, by left invariance of `Measure.haar`
  (`integral_mul_left_eq_self`).
- `integrable_kernel_mul`: for continuous compactly supported `h` and locally integrable `f`,
  `a ↦ h(a) f(x a)` is integrable.
- `rightConvolution_levelAverage`: for continuous compactly supported `h`, locally integrable
  `f` and finitely many cosets,
  `δ(levelAverage L L' h) f (x) = [L : L ∩ L']⁻¹ ∑ᶠ_c δ(h) f (x l_c)`.
- `sum_rightConvolution_levelAverage`: let `f` be locally integrable and right invariant
  under `L`, and let `∑_{k ∈ s} b_k δ(h_k) f = c f` hold everywhere, with continuous compactly
  supported `h_k`. Then `∑_{k ∈ s} b_k δ(levelAverage L L' h_k) f = c f` everywhere, for any
  `L'` with finitely many cosets. Indeed the left side at `x` is the average over `c` of the
  left side of the original equation at `x l_c`, which is `c f(x l_c) = c f(x)`.

## Provenance

Bernstein–Lapid, *On the meromorphic continuation of Eisenstein series*, J. Amer. Math. Soc.
37 (2024), 187–234, §7.6, pp. 219–220 (literature id
`bernstein-lapid-2024-meromorphic-continuation-eisenstein`). In the last step of the proof of
Theorem 7.2 the reproducing equation `δ(h(s)) f = f` is used to map the Hilbert-space
witness into the smooth functions of uniform moderate growth `𝔉_umg`. The prescription of a
fixed compact open level `L` and the use of level-averaged kernels `e_L * h * e_L` come from
the Library's derivation of the Fréchet form, item 5 of the Markdown of
`Langlands.Global.AdelicLocalFinitenessStatement`, not from BL. This module realizes the left averaging
`e_L * h` for a compact open `L` by a finite sum over the cosets of an open subgroup `L'`
under which `h` is already left invariant; the averaged kernel is the same function as
`e_L * h` for the normalized Haar measure `e_L` of `L`, but the module neither uses nor
proves that comparison. The point is that a test function left invariant under `L` produces
right `L`-invariant convolutions, while the Harish-Chandra equations of the system keep
holding for right `L`-invariant solutions.
