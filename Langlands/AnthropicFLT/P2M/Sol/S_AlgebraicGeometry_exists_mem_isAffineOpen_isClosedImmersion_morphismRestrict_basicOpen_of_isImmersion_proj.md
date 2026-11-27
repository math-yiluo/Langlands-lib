# `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_exists_mem_isAffineOpen_isClosedImmersion_morphismRestrict_basicOpen_of_isImmersion_proj`

Ported for the proof `Langlands.AlgebraicGeometry.finiteFreeQuasiProjectiveQuotient` of `Langlands.AlgebraicGeometry.FiniteFreeQuasiProjectiveQuotientStatement` (quotients of quasi-projective schemes over a field by free actions of finite groups are quasi-projective), which depends on this module through its imports. Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_AlgebraicGeometry_exists_mem_isAffineOpen_isClosedImmersion_morphismRestrict_basicOpen_of_isImmersion_proj.lean` (SHA-256 `d72389821db7a3648b8795e9fffc3439130195367f49c72185b78c8f387a660b`) from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/`.

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; `import Mathlib` is now `import Langlands.MathlibBase` (all of Mathlib except the three modules that clash with weil-conjectures, see `Langlands/MathlibBase.md`).
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file; it records the date of the modifications, 26 November 2026.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- 1 `p2m_open "…"` command(s) (an FLT command from `P2M.Util` that opens the named namespaces and activates their scoped extensions) are replaced by standard `open` commands with the same namespaces, each written with the prefix `_root_.`: `AlgebraicGeometry` becomes `open _root_.AlgebraicGeometry`.
- 1 `p2m_export "N" "a b …"` command(s) (an FLT command from `P2M.Util` that adds aliases `a`, `b`, … in the current namespace for `N.a`, `N.b`, …) are replaced by `export _root_.N (a b …)` with the same names.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

The theorem `P2MW.S_AlgebraicGeometry_exists_mem_isAffineOpen_isClosedImmersion_morphismRestrict_basicOpen_of_isImmersion_proj.solution` proves the statement of the companion theorem in `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_exists_mem_isAffineOpen_isClosedImmersion_morphismRestrict_basicOpen_of_isImmersion_proj`.

Statement. `AlgebraicGeometry.exists_mem_isAffineOpen_isClosedImmersion_morphismRestrict_basicOpen_of_isImmersion_proj`:
let `𝒜` be an `ℕ`-graded ring (`GradedRing 𝒜`, with underlying ring `A`), let `ι : X ⟶ Proj 𝒜` be an
immersion and let `S` be a finite set of points of `X`. Then there is a homogeneous element `F ∈ 𝒜 d` of
positive degree `d` such that the preimage `ι ⁻¹ᵁ D₊(F)` contains `S` and is affine, and the restriction
`ι ∣_ D₊(F)` is a closed immersion.

Proof. The immersion `ι` factors as the closed immersion `ι.liftCoborder` into the open
`ι.coborderRange` followed by the inclusion of that open (Mathlib). The complement `Z` of
`ι.coborderRange` is the zero locus of its vanishing ideal `J`; no prime of a point of `ι(S)` contains
`J ⊓ 𝒜₊`, since these points are outside `Z` and relevant. Homogeneous prime avoidance, the ported
theorem `HomogeneousIdeal.exists_homogeneous_pos_mem_forall_notMem`, gives a homogeneous `F` of positive
degree in `J ⊓ 𝒜₊` outside all these primes (`A1ChartFin.Proj.exists_basicOpen_le_forall_mem_of_finset`).
Then `D₊(F) ≤ ι.coborderRange` and `D₊(F)` contains `ι(S)`. As `D₊(F)` is affine
(`Proj.isAffineOpen_basicOpen`), so is its preimage in `ι.coborderRange`
(`A1ChartFin.isAffineOpen_ι_preimage_of_le`), hence its preimage under the affine morphism
`ι.liftCoborder`; and the restriction of `ι` over an open contained in `ι.coborderRange` has closed
range, hence is a closed immersion
(`A1ChartFin.isClosedImmersion_morphismRestrict_of_le_coborderRange`).

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- theorem `P2MW.S_AlgebraicGeometry_exists_mem_isAffineOpen_isClosedImmersion_morphismRestrict_basicOpen_of_isImmersion_proj.AlgebraicGeometry.A1ChartFin.Proj.exists_basicOpen_le_forall_mem_of_finset`
- theorem `P2MW.S_AlgebraicGeometry_exists_mem_isAffineOpen_isClosedImmersion_morphismRestrict_basicOpen_of_isImmersion_proj.AlgebraicGeometry.A1ChartFin.isAffineOpen_ι_preimage_of_le`
- theorem `P2MW.S_AlgebraicGeometry_exists_mem_isAffineOpen_isClosedImmersion_morphismRestrict_basicOpen_of_isImmersion_proj.AlgebraicGeometry.A1ChartFin.isClosedImmersion_morphismRestrict_of_le_coborderRange`
- theorem `P2MW.S_AlgebraicGeometry_exists_mem_isAffineOpen_isClosedImmersion_morphismRestrict_basicOpen_of_isImmersion_proj.solution`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Theorems.Thm_HomogeneousIdeal_exists_homogeneous_pos_mem_forall_notMem`.
Other imports: `Langlands.MathlibBase`.
