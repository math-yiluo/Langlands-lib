# Hecke characters trivial on the positive real ideles are unitary

Lean module: `Langlands.Global.HeckeCharacterPositiveRealUnitary`. It imports
`Langlands.Global.Factors.HeckeEulerProduct` (for
`HeckeEulerProduct.norm_eq_one_of_ideleClass_eq_one`) and
`Langlands.Global.PositiveRealIdeles` (for `PositiveRealIdeles.full` and
`PositiveRealIdeles.absoluteValue_full`). It changes no published file and
introduces no new definition.

## Declaration

```lean
theorem Langlands.Global.HeckeCharacter.isUnitary_of_positiveRealIdeles
    {F : Type u} [Field F] [NumberField F] (χ : HeckeCharacter F)
    (hχ : ∀ a : ℝ≥0ˣ, χ (ideleClassMap F (PositiveRealIdeles.full F a)) = 1) :
    χ.IsUnitary
```

Let `χ : F^× \ 𝔸_F^× → ℂ^×` be a continuous character of the idele class
group of a number field `F` (`HeckeCharacter F`, the abbreviation
`IdeleClasses F →ₜ* ℂˣ` of module `Langlands.Global.HeckeCharacter`). Suppose
`χ` is trivial on the classes of the ideles `PositiveRealIdeles.full F a`, for
every positive real `a`. Then `‖χ(c)‖ = 1` for every idele class `c`, which is
`HeckeCharacter.IsUnitary χ`.

`PositiveRealIdeles.full F a` is the idele whose component at every infinite
place is the positive real `a`, in the real subfield of the completion, and
whose finite component is `1` (published module `Global.PositiveRealIdeles`).
These ideles form the group `A_{G_m}` of Getz–Hahn.

The theorem is used in
`Langlands.Global.Factors.CuspidalSplitCentreUnitaryProof`. It applies to any
idele class character, so it is in its own module.

## Proof

Write `d = [F : ℚ]` (`Module.finrank ℚ F`), and let `|·|` be the normalized
idelic absolute value (`IdeleAbsoluteValue.full F`, with values in `ℝ≥0ˣ`).

1. Every idele class is the class of an idele `z`
   (`QuotientGroup.mk_surjective`).
2. Let `s = |z|`, a positive real, and put
   `y = z ^ d * (PositiveRealIdeles.full F s)⁻¹`. The published lemma
   `PositiveRealIdeles.absoluteValue_full` gives
   `|PositiveRealIdeles.full F s| = s ^ d`, so `|y| = s ^ d * (s ^ d)⁻¹ = 1`.
   The absolute value of the class of `y` is `|y|`
   (`IdeleAbsoluteValue.ideleClass_class`).
3. The published lemma `HeckeEulerProduct.norm_eq_one_of_ideleClass_eq_one`
   (module `Global.Factors.HeckeEulerProduct`) says that a Hecke character has
   absolute value `1` at every idele class of absolute value `1`. It rests on
   the compactness of the kernel of the absolute value on the idele class group
   (`NormOneIdeleClass.isCompact_ker_ideleClass`, module
   `Global.NormOneIdeleClassCompact`). Hence `‖χ([y])‖ = 1`.
4. `χ` is multiplicative and trivial on the class of
   `PositiveRealIdeles.full F s` by hypothesis, so
   `‖χ([y])‖ = ‖χ([z])‖ ^ d`. Thus `‖χ([z])‖ ^ d = 1`.
5. `d ≠ 0` (`Module.finrank_pos`), and a nonnegative real number whose `d`-th
   power is `1` equals `1` (`pow_eq_one_iff_of_nonneg`). So `‖χ([z])‖ = 1`.

Step 2 uses `z ^ d` instead of a `d`-th root of `|z|`, so the proof needs no
real powers.

## Sources and provenance

- J. R. Getz and H. Hahn, *An Introduction to Automorphic Representations*,
  Graduate Texts in Mathematics 300, Springer, 2024. Registered source
  `getz-hahn-2024-automorphic-representations`, PDF
  `/home/taskhub/central-library/Getz-Hahn--An introduction to automorphic representations (book)--2024.pdf`
  (SHA256
  `a125cf9c0f445972cbbd3552b4fb9905ca948108a05880f90eaa43558d09a507`). In
  Chapter 2 the PDF page is the printed page + 17.
  - Display (2.18), printed page 68 (PDF page 85): the idelic norm
    `|·| : F^× \ 𝔸_F^× → ℝ_{>0}`, which is surjective for a number field.
  - Displays (2.19)–(2.20), printed page 68 (PDF page 85): the norm-one group
    `G(𝔸_F)^1` and the group `A_G`. For `G = G_m` over a number field,
    "the group `A_{G_m}` is just the image of the diagonal embedding
    `ℝ_{>0} → F_∞^×`, regarded as a subgroup of `𝔸_F^×`".
  - Lemma 2.6.2, printed page 69 (PDF page 86): for a number field and `G`
    reductive, `A_G G(𝔸_F)^1 = G(𝔸_F)` and `A_G ∩ G(𝔸_F)^1 = 1`. For `G = G_m`
    this is `𝔸_F^× = A_{G_m} · (𝔸_F^×)^1`.
  - Theorem 2.6.3, printed page 69 (PDF page 86): `G(F) \ G(𝔸_F)^1` has finite
    volume, together with a criterion for its compactness in terms of the
    `F`-split tori of `G`. For `G = G_m` the quotient is `F^× \ (𝔸_F^×)^1`,
    whose compactness is used in step 3. The Library proves this compactness
    separately, as `NormOneIdeleClass.isCompact_ker_ideleClass`; this module
    does not rely on Theorem 2.6.3.

The theorem is derived content: Getz–Hahn do not state it separately. It
combines the decomposition of Lemma 2.6.2 for `G_m` with the compactness of
`F^× \ (𝔸_F^×)^1`. The Lean proof does not use the decomposition
`z = a · y` itself. It uses the variant `z ^ d = PositiveRealIdeles.full F s · y`
with `|y| = 1` from step 2, which avoids `d`-th roots. The group `A_{G_m}` is
represented by the published map `PositiveRealIdeles.full`, whose Markdown cites
Mœglin–Waldspurger (1995), Chapter I, §2.1.

## What is not asserted

- No converse: a unitary Hecke character need not be trivial on `A_{G_m}` (for
  example `|·|^{iσ}` with real `σ ≠ 0`).
- Nothing about the decomposition `𝔸_F^× = A_{G_m} · (𝔸_F^×)^1` as a Lean
  statement.

## Lean checks

A build of the module (lake build) compiles with no errors or warnings
(rechecked over Library
`fcb85a7ef43356fec01e6ccf1605f08568c08cb0`).
The theorem depends only on the axioms `propext`, `Classical.choice` and
`Quot.sound`.
