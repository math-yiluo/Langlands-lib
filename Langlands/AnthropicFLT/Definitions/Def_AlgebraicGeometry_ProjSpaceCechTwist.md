# The combinatorial Čech complex of the twisting sheaves on projective space

Module `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ProjSpaceCechTwist`, in namespace
`ProjSpaceCech`. Modules live in a fixed universe `u`; `R` is a commutative ring, `n ∈ ℕ` and `d ∈ ℤ`.

## Definitions and results

The file models the Čech complex of `𝒪(d)` on `ℙⁿ_R` for the standard cover by the opens `D₊(Xⱼ)`,
purely combinatorially. The sections of `𝒪(d)` over `D₊(∏_{j∈I} Xⱼ)` are spanned by the Laurent
monomials of degree `d` whose negative exponents lie in `I`.

- `Idx.succAbove_comp_succAbove` (theorem): the simplicial identity
  `succAbove j.succ ∘ succAbove i = succAbove i.castSucc ∘ succAbove j` for `i ≤ j`.
- `Twist.MonExp n` is the type of exponent vectors `Fin (n+1) → ℤ`, and `Twist.negSupp n a` the set
  of indices with negative exponent (`mem_negSupp`).
- `Twist.Mon n d I`, for `I ⊆ {0, …, n}`, is the set of exponent vectors `a` with `∑ⱼ aⱼ = d` and
  negative support in `I`. It has decidable equality. For `I ⊆ J`, `Twist.Mon.incl` is the inclusion
  `Mon n d I → Mon n d J`, which is injective (`incl_injective`, `incl_val`).
- `Twist.Sec R n d I` is the free `R`-module `Mon n d I →₀ R` on these monomials: the sections of
  `𝒪(d)` on `D₊(∏_{j∈I} Xⱼ)`.
- `Idx n i` is the type of strictly increasing maps `Fin (i+1) → Fin (n+1)` (finite, decidable
  equality). `Idx.img n s` is the image of `s` as a finite set, with `i + 1` elements
  (`Idx.card_img`), and `Idx.face n s j` deletes the `j`-th entry; its image is contained in that of
  `s` (`Idx.img_face_subset`).
- `Twist.faceRes R n d s j` is the restriction map `Sec (img (face s j)) → Sec (img s)` induced by the
  inclusion of monomial sets.
- `Twist.cochain R n d i` is the product of `Twist.Sec R n d (img s)` over `s : Idx n i`, and
  `Twist.d R n d i` the alternating Čech differential (`Twist.d_apply`).
- `Idx.isEmpty_of_lt` and `Twist.cochain_subsingleton_of_lt` (theorems): for `i > n` there are no index
  tuples, so the cochains are trivial.
- `Twist.H R n d i` is the Čech cohomology: the kernel of `d 0` for `i = 0`, and the kernel of
  `d (i+1)` modulo the image of `d i` otherwise. The file provides its abelian group and `R`-module
  instances.

## Provenance and licence

This file is a port of `Definitions/Def_AlgebraicGeometry_ProjSpaceCechTwist.lean` from the Anthropic
Lean formalization of Fermat's Last Theorem at commit `6e837e75355538c7f80bab5b956861e86c4eacc2`
(registered literature `anthropic-flt-complete-lean-source-6e837e75`). That work is Copyright 2026
Anthropic, PBC, and is licensed under the Apache License, Version 2.0. Copies of its `LICENSE`, `NOTICE`
and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/`. `ATTRIBUTION.md` has no row for this file, so no
third-party notice applies. Declaration names and namespaces are FLT's. The port makes only these
changes:

- an attribution header is added above the imports;
- FLT's lakefile options are set after the imports: `maxHeartbeats 4000000`,
  `synthInstance.maxHeartbeats 400000` and `backward.isDefEq.respectTransparency.types false`.

The file imports only Mathlib, so its imports are unchanged.
