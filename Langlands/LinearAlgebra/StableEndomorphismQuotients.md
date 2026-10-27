# Adjacent kernel and range quotients of an endomorphism

This module builds the quotient modules `E_k = N_(k+1) / N_k` and
`F_k = I_k / I_(k+1)`, with `N_k = ker (t ^ k)` and `I_k = Im (t ^ k)`, and the
three linear maps between them that appear in the proof of Lemma (iv) of David Renard,
*Représentations des groupes réductifs p-adiques*, French version dated 9 July 2026,
Appendix C.II. Everything here is a definition or one of its basic laws.
The kernel and image identities, the injectivity and surjectivity of the outer
arrows, and exactness are left to separate successors (see "Excluded content").

## Sources

- Governing source: registered literature
  `renard-2026-representations-groupes-reductifs-padiques`, SHA256
  `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`, file
  `/home/taskhub/central-library/Renard--Representations des groupes reductifs p-adiques (2026 version)--2026.pdf`
  (printed page = PDF page − 6).
  - Printed page 277 / PDF page 283, statement of C.II Lemma (iv): the notation
    `N_k = ker t^k` and `I_k = Im t^k`.
  - Printed page 278 / PDF page 284, proof of Lemma (iv): "Posons
    `E_k = N_{k+1}/N_k` et `F_k = I_k/I_{k+1}`". The restriction of `t^k` to `N_{k+1}`
    takes values in `I_k` and vanishes on `N_k`, so it induces `t̄_k : E_k → F_k`.
    A map `t̄ : E_{k+1} → E_k` is induced by the composite
    `N_{k+2} → N_{k+1} → N_{k+1}/N_k = E_k` (first arrow `t`), whose kernel the source
    gives as exactly `N_{k+1}`. A map `t̄ : F_k → F_{k+1}` is induced by
    `I_k → I_{k+1} → I_{k+1}/I_{k+2} = F_{k+1}` (first arrow `t`), whose kernel the
    source says contains `I_{k+1}`. Then come the kernel/image identities and the
    exact sequence `0 → E_{k+1} → E_k → F_k → F_{k+1} → 0`.

  Worker 277 read the text of PDF pages 283–284 and visually checked a rendered
  image of PDF page 284.
- Author errata: registered `renard-2010-corrections-complements`, SHA256
  `fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`. The task
  cites PDF pages 18–19. Worker 277 found the relevant entries on PDF page 19:
  - "p. 321, l. 4 : remplacer l'indice k + 1 par k + 2". This fixes the image of
    `t̄ : E_{k+1} → E_k` to `N_k + t(N_{k+2})/N_k = N_k + (Im t ∩ N_{k+1})/N_k`.
    The 2026 text on PDF 284 already has this corrected index.
  - "p. 320, l. -7", a `ker`/`Im` fix in the proof of Lemma (iii).

  Neither correction changes any object built here. This module states no image
  formula, and the old index `k + 1` appears nowhere.

## Hypotheses and universes

All declarations are in the namespace `Langlands.LinearAlgebra.StableEndomorphism`,
under the variables

```
{R : Type uR} {V : Type uV} [Ring R] [AddCommGroup V] [Module R V]
(t : Module.End R V) (k : ℕ)
```

- The coefficient ring `R` is any ring, not necessarily commutative. Renard's
  setting (an arbitrary complex vector space and a complex-linear endomorphism) is
  the case `R := ℂ`. The final section `ComplexSpecialization` checks this case for a
  general `{W : Type uV} [AddCommGroup W] [Module ℂ W]` and an arbitrary
  `s : Module.End ℂ W`, at every `k : ℕ`. Its `example`s type-check `E_k` and `F_k` as
  `ℂ`-modules, both projections, all three arrows, the `k = 0` values of `N_0` and
  `I_0`, and that `simp` proves the three application laws.
- No finite dimension, finite generation, noetherian or artinian condition,
  stability, eventual stability, nontriviality, or nonzero index is assumed. The
  zero module and `k = 0` are allowed.
- The universes `uR` (coefficients) and `uV` (vector carrier) are independent.
  The quotient types `KerQuotient t k` and `RangeQuotient t k` live in `Type uV`.
  The inspected definitions have level parameters `uR uV`.
- Powers `t ^ k` use Mathlib's monoid structure on `Module.End R V`, where
  multiplication is composition and `t ^ 0 = 1` is the identity map.
- Imports: `Mathlib.LinearAlgebra.Quotient.Basic`, which provides submodule quotients,
  `mkQ` and `liftQ`, and `Mathlib.Basic.Complex.Basic`, used only by the `ℂ` examples.

## The actual quotient models

Every object is an actual Mathlib submodule, quotient module, or linear map. None
is a predicate, an unspecified object, or a record that assumes quotient properties.

- `kerPow t k := LinearMap.ker (t ^ k)` is `N_k`, and
  `rangePow t k := LinearMap.range (t ^ k)` is `I_k`. Both are `Submodule R V`.
- The denominators are pulled back along the subtype inclusion of the numerator into
  `V`:
  `kerPowInSucc t k := (kerPow t k).comap (kerPow t (k + 1)).subtype`, a submodule of
  `kerPow t (k + 1)`, and
  `rangePowSuccIn t k := (rangePow t (k + 1)).comap (rangePow t k).subtype`, a submodule
  of `rangePow t k`.
  `map_subtype_kerPowInSucc` and `map_subtype_rangePowSuccIn` show that their images
  in `V` are exactly `N_k` and `I_(k+1)`. These use `N_k ≤ N_(k+1)` and
  `I_(k+1) ≤ I_k`.
- `KerQuotient t k := kerPow t (k + 1) ⧸ kerPowInSucc t k` is `E_k`, and
  `RangeQuotient t k := rangePow t k ⧸ rangePowSuccIn t k` is `F_k`. These are Mathlib
  quotient modules (`Submodule.Quotient`). They are not the ambient quotients `V ⧸ N_k`
  or `V ⧸ I_(k+1)`.
- The canonical projections are `kerQuotientMk t k := (kerPowInSucc t k).mkQ`, from
  `N_(k+1)` onto `E_k`, and `rangeQuotientMk t k := (rangePowSuccIn t k).mkQ`, from
  `I_k` onto `F_k`.

`kerPow`, `rangePow`, the two denominators, the two quotient types and the two
projections are `abbrev`s. Mathlib's submodule, quotient and `mkQ` API therefore
applies to them directly.

## Indexing at k = 0

The source fixes no range for `k`. Here every `k : ℕ` is allowed, including
`k = 0`, where `t ^ 0` is the identity map:

- `kerPow_zero : kerPow t 0 = ⊥` (`N_0 = 0`) and
  `rangePow_zero : rangePow t 0 = ⊤` (`I_0 = V`).
- `E_0 = N_1 / N_0` is `ker (t ^ 1)`, which equals `ker t`, modulo the zero
  submodule. `F_0 = I_0 / I_1` is `V` (as the submodule `⊤`) modulo
  `Im (t ^ 1) = Im t`. These identifications are mathematical descriptions. The
  module proves only `kerPow_zero` and `rangePow_zero`.
- `kerToRangeQuotient t 0 : E_0 → F_0` is induced by `t ^ 0`, the identity. It sends
  the class of `x ∈ ker t` to the class of `x` in `V / Im t`.
- `kerQuotientShift t 0 : E_1 → E_0` is `N_2 / N_1 → N_1 / N_0`, and
  `rangeQuotientShift t 0 : F_0 → F_1` is `I_0 / I_1 → I_1 / I_2`. Both are induced
  by `t`.

## Declaration correspondence

| Lean declaration | Kind | Content and source correspondence |
| --- | --- | --- |
| `kerPow t k` | `abbrev` | `N_k = ker (t ^ k)`, printed 277 / PDF 283 |
| `rangePow t k` | `abbrev` | `I_k = Im (t ^ k)`, printed 277 / PDF 283 |
| `mem_kerPow`, `mem_rangePow` | theorems | membership unfolded: `(t ^ k) x = 0`, `∃ y, (t ^ k) y = x` |
| `kerPow_zero`, `rangePow_zero` | theorems | `N_0 = ⊥`, `I_0 = ⊤` |
| `apply_mem_kerPow` | theorem | `x ∈ N_(k+1) → t x ∈ N_k` |
| `apply_mem_rangePow` | theorem | `x ∈ I_k → t x ∈ I_(k+1)` |
| `pow_apply_mem_rangePow` | theorem | `(t ^ k) x ∈ I_k` for every `x : V` |
| `kerPow_le_succ` | theorem | `N_k ≤ N_(k+1)` (source: "croissante", PDF 284) |
| `rangePow_succ_le` | theorem | `I_(k+1) ≤ I_k` (source: "décroissante", PDF 284) |
| `kerPowInSucc t k` | `abbrev` | denominator `N_k` of `E_k`, pulled back into `N_(k+1)` |
| `rangePowSuccIn t k` | `abbrev` | denominator `I_(k+1)` of `F_k`, pulled back into `I_k` |
| `mem_kerPowInSucc`, `mem_rangePowSuccIn` | theorems | membership is membership of the underlying vector in `N_k`, respectively `I_(k+1)` (by `Iff.rfl`) |
| `map_subtype_kerPowInSucc`, `map_subtype_rangePowSuccIn` | theorems | the pulled-back denominators map onto `N_k`, respectively `I_(k+1)`, in `V` |
| `KerQuotient t k` | `abbrev` | `E_k = N_(k+1) / N_k`, PDF 284 |
| `RangeQuotient t k` | `abbrev` | `F_k = I_k / I_(k+1)`, PDF 284 |
| `kerQuotientMk t k` | `abbrev` | canonical projection `N_(k+1) →ₗ[R] E_k` |
| `rangeQuotientMk t k` | `abbrev` | canonical projection `I_k →ₗ[R] F_k` |
| `kerQuotientMk_apply`, `rangeQuotientMk_apply` | theorems | the projections are `Submodule.Quotient.mk` |
| `kerQuotientMk_surjective`, `rangeQuotientMk_surjective` | theorems | the projections are surjective |
| `ker_kerQuotientMk`, `ker_rangeQuotientMk` | theorems | the projections' kernels are the pulled-back denominators |
| `kerQuotientMk_eq_zero_iff`, `rangeQuotientMk_eq_zero_iff` | theorems | a class is zero iff its representative lies in `N_k`, respectively `I_(k+1)` |
| `kerShift t k` | `def` | representative map `N_(k+2) →ₗ[R] N_(k+1)`, `x ↦ t x` (the arrow `t` of the first composite on PDF 284) |
| `kerToRange t k` | `def` | representative map `N_(k+1) →ₗ[R] I_k`, `x ↦ (t ^ k) x` ("la restriction de `t^k` à `N_{k+1}` est à valeurs dans `I_k`") |
| `rangeShift t k` | `def` | representative map `I_k →ₗ[R] I_(k+1)`, `x ↦ t x` (the arrow `t` of the last composite on PDF 284) |
| `coe_kerShift_apply`, `coe_kerToRange_apply`, `coe_rangeShift_apply` | `@[simp]` theorems | underlying vectors: `t x`, `(t ^ k) x`, `t x` |
| `kerShiftMk t k` | `def` | the source's prequotient composite `N_(k+2) → N_(k+1) → N_(k+1)/N_k = E_k` |
| `kerToRangeMk t k` | `def` | the composite `N_(k+1) → I_k → F_k` of `t ^ k` with the projection |
| `rangeShiftMk t k` | `def` | the source's prequotient composite `I_k → I_(k+1) → I_(k+1)/I_(k+2) = F_(k+1)` |
| `kerShiftMk_apply`, `kerToRangeMk_apply`, `rangeShiftMk_apply` | theorems | the composites are projection after representative map |
| `kerPowInSucc_le_ker_kerShiftMk` | theorem | the first composite vanishes on `N_(k+1)` (the denominator of `E_(k+1)`) |
| `kerPowInSucc_le_ker_kerToRange` | theorem | the restriction of `t ^ k` vanishes on `N_k` ("nulle sur `N_k`") |
| `kerPowInSucc_le_ker_kerToRangeMk` | theorem | hence the middle composite vanishes on `N_k` |
| `rangePowSuccIn_le_ker_rangeShiftMk` | theorem | the last composite vanishes on `I_(k+1)` ("dont le noyau contient `I_{k+1}`") |
| `kerQuotientShift t k` | `def` | arrow 1, `E_(k+1) →ₗ[R] E_k`, the source's `t̄` |
| `kerToRangeQuotient t k` | `def` | arrow 2, `E_k →ₗ[R] F_k`, the source's `t̄_k` |
| `rangeQuotientShift t k` | `def` | arrow 3, `F_k →ₗ[R] F_(k+1)`, the source's `t̄` |
| `kerQuotientShift_mk`, `kerToRangeQuotient_mk`, `rangeQuotientShift_mk` | theorems | application laws stated with the named projections: `[x] ↦ [kerShift t k x]`, `[x] ↦ [kerToRange t k x]`, `[x] ↦ [rangeShift t k x]` |
| `kerQuotientShift_quotient_mk`, `kerToRangeQuotient_quotient_mk`, `rangeQuotientShift_quotient_mk` | `@[simp]` theorems | the same laws stated with `Submodule.Quotient.mk`, which is `simp` normal form after the `abbrev` projections unfold |
| `kerQuotientShift_comp_mk`, `kerToRangeQuotient_comp_mk`, `rangeQuotientShift_comp_mk` | theorems | each arrow composed with its source projection is the corresponding composite (`kerShiftMk`, `kerToRangeMk`, `rangeShiftMk`) |
| `kerPowInSucc_le_comap_kerShift`, `kerPowInSucc_le_comap_kerToRange`, `rangePowSuccIn_le_comap_rangeShift` | theorems | each representative map sends the domain's denominator into the target's denominator (`N_(k+1)` into `N_k`, `N_k` into `I_(k+1)`, `I_(k+1)` into `I_(k+2)`) |
| `kerQuotientShift_eq_mapQ`, `kerToRangeQuotient_eq_mapQ`, `rangeQuotientShift_eq_mapQ` | theorems | each arrow equals `Submodule.mapQ` of `kerShift`, `kerToRange`, `rangeShift` |
| `kerQuotientShift_mk_mk`, `kerToRangeQuotient_mk_mk`, `rangeQuotientShift_mk_mk` | theorems | representative formulas with explicit vectors: for `x : V` with the membership proofs, `[x] ↦ [t x]`, `[x] ↦ [(t ^ k) x]`, `[x] ↦ [t x]` |

The application laws are stated for an arbitrary representative. Since the
projections are surjective (`*_surjective`), they determine the arrows.

## Construction route and intrinsic laws

- Chain containments: `kerPow_le_succ` holds because `t ^ (k+1) = t * t ^ k`
  (`pow_succ'`), so `(t ^ k) x = 0` gives `(t ^ (k+1)) x = t 0 = 0`.
  `rangePow_succ_le` holds because `t ^ (k+1) = t ^ k * t` (`pow_succ`), so
  `(t ^ (k+1)) y = (t ^ k) (t y)`.
- Maps into the numerators: `apply_mem_kerPow` rewrites `t ^ (k+1)` as `t ^ k * t`.
  `apply_mem_rangePow` rewrites `t ^ (k+1) y` as `t ((t ^ k) y)`.
  `pow_apply_mem_rangePow` is `LinearMap.mem_range_self`.
- Representative maps: `kerShift`, `kerToRange` and `rangeShift` are the Mathlib
  restrictions `LinearMap.restrict` of `t` and `t ^ k` between the submodules, using
  the preceding membership laws.
- Annihilation of the denominators: if `x ∈ N_(k+1)`, then `t x ∈ N_k`, so
  `kerShiftMk` sends `x` to zero by `Submodule.Quotient.mk_eq_zero`. If `x ∈ N_k`,
  then `(t ^ k) x = 0`, so `kerToRange` already sends `x` to zero, and composing with
  the projection keeps it zero (`LinearMap.ker_le_ker_comp`). If `x ∈ I_(k+1)`, then
  `t x ∈ I_(k+2)`, so `rangeShiftMk` sends `x` to zero.
- Arrows: each arrow is `Submodule.liftQ` of its composite along the denominator of
  its domain, with the annihilation law as the well-definedness proof. So each map is
  given by construction, not by an existential hypothesis. The `_mk`, `_quotient_mk`
  and `_mk_mk` laws hold by `rfl`, and the `_comp_mk` laws are
  `Submodule.liftQ_mkQ`.
- Comparison with `Submodule.mapQ`: the three `*_le_comap_*` laws show that each
  representative map sends the denominator of its domain into the denominator of
  its target. `N_(k+1)` goes into `N_k` because `t x ∈ N_k`. `N_k` goes into `I_(k+1)`
  because `(t ^ k) x = 0`. `I_(k+1)` goes into `I_(k+2)` because `t x ∈ I_(k+2)`.
  The `*_eq_mapQ` laws (by `rfl`, since Mathlib defines `mapQ p q f h` as
  `p.liftQ (q.mkQ.comp f) _`) show that each arrow equals `Submodule.mapQ` of its
  representative map. The middle arrow is therefore also the source's direct
  construction: "the restriction of `t^k` to `N_{k+1}`, with values in `I_k`, vanishing
  on `N_k`, induces `t̄_k`".
- The source distinguishes the prequotient maps `N_(k+2) → E_k` and `I_k → F_(k+1)`
  from the induced maps `E_(k+1) → E_k` and `F_k → F_(k+1)`. Lean keeps this
  distinction: the prequotient maps are the separate declarations `kerShiftMk` and
  `rangeShiftMk`, and the induced arrows are `kerQuotientShift` and
  `rangeQuotientShift`. The `_comp_mk` laws connect the two.

## Excluded content

This module proves only the containment laws above (`≤` a kernel). It does not
prove or assume:

- the source's claim that `ker (kerShiftMk t k)` is exactly `N_(k+1)`, or the
  injectivity of `kerQuotientShift`;
- the kernel `N_k + (Im t ∩ N_(k+1)) / N_k` or the image
  `I_(k+1) + t^k(N_(k+1)) / I_(k+1)` of `t̄_k`;
- the image `N_k + t(N_(k+2)) / N_k` of the first arrow, in the corrected index of
  the errata;
- the surjectivity of `rangeQuotientShift` or its kernel;
- exactness at any place, or the exact sequence
  `0 → E_(k+1) → E_k → F_k → F_(k+1) → 0`;
- the stabilization conclusions of Lemma (iv). The common first stabilization index
  is already covered by `FirstStabilizationIndexStatement` in
  `Langlands.LinearAlgebra.StableEndomorphismStatements` and its published proof.

These are substantive successor obligations. They can be stated about the
actual maps above, for example as `LinearMap.ker (kerQuotientShift t k) = ⊥` or
`LinearMap.range (kerToRangeQuotient t k) = LinearMap.ker (rangeQuotientShift t k)`,
using the named projections and application laws. No definition record and no
local axiom encodes them here.
