# A finite flat module of constant rank is finitely presented

`Langlands.AnthropicFLT.P2M.Sol.S_Module_finitePresentation_of_rankAtStalk_eq` proves the theorem `P2MW.S_Module_finitePresentation_of_rankAtStalk_eq.solution`. Its statement is that of `Module.finitePresentation_of_rankAtStalk_eq`, which `Langlands.AnthropicFLT.Theorems.Thm_Module_finitePresentation_of_rankAtStalk_eq` states under its FLT name.

## Statement

Let `R` be a commutative ring and `M` a finite flat `R`-module whose rank at
every prime is the same number `n`: for every prime `p`, the free module
`M_p` over the local ring `R_p` has rank `n` (`Module.rankAtStalk M p = n`).
Then `M` is a finitely presented `R`-module.

## Provenance and licence

The Lean file is ported from `P2M/Sol/S_Module_finitePresentation_of_rankAtStalk_eq.lean` of the Anthropic Lean formalization of Fermat's Last Theorem at commit `6e837e75355538c7f80bab5b956861e86c4eacc2` (`anthropic-flt-complete-lean-source-6e837e75`). That source is Copyright 2026 Anthropic, PBC, and licensed under the Apache License, Version 2.0 (see `licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`). The file is not listed in the FLT `ATTRIBUTION.md`, and the Lean file carries an attribution header. The mathematics, the declaration names and the proofs are FLT's. The port makes these changes:

- imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged;
- the options of the FLT lakefile (`maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000` and `backward.isDefEq.respectTransparency.types false`) are set in the file;
- the import of FLT's helper module `P2M.Util`, the command library of FLT's own build tooling, is removed. No declaration, statement or proof step changed;

## Proof outline

1. Surjections from `Aⁿ` are isomorphisms. Let `A` be a commutative ring and
   `P` a finite flat `A`-module of constant rank `n`. A surjective linear map
   `ψ : Aⁿ → P` is injective: injectivity is checked after localizing at
   every maximal ideal `J`; there both `A_Jⁿ` and `P_J` are free of rank `n`
   over the local ring `A_J` (`free_of_flat_of_isLocalRing`), so composing
   the localized map with an isomorphism `P_J ≅ A_Jⁿ` gives a surjective
   endomorphism of `A_Jⁿ`, which is injective (`OrzechProperty`). Hence `P` is
   isomorphic to `Aⁿ` and finitely presented.
2. Finite presentation near a prime. For a prime `p`, choose a basis of
   `M_p` and elements `m_i ∈ M` whose images are, up to units, the basis
   vectors. The submodule `N` they span satisfies `N_p = M_p`, so
   `(M/N)_p = 0` (`localized'_eq_top_iff_subsingleton`). Since `M/N` is
   finite, `(M/N)_r = 0` for some `r ∉ p`
   (`LocalizedModule.exists_subsingleton_away`). Then the `m_i` generate `M_r`,
   giving a surjection `A^n → M_r` with `A = R_r`. The rank of `M_r` at every
   prime of `A` is again `n` (`rankAtStalk_baseChange`), so step 1 shows that
   `M_r` is finitely presented over `R_r`.
3. Local to global. The elements `r` from step 2 generate the unit ideal,
   because no maximal ideal contains all of them. Write `M` as a quotient of
   `Rᵏ` by `π`; it suffices that `ker π` is finitely generated
   (`Module.FinitePresentation.fg_ker_iff`). Localization is exact, so the
   localization of `ker π` at each `r` is the kernel of the localized
   surjection `R_rᵏ → M_r`, which is finitely generated because `M_r` is
   finitely presented. Finiteness is local for a family of elements generating
   the unit ideal (`Module.Finite.of_localizationSpan'`).
