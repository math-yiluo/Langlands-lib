# Harris's twisting characters `ν(Gπ)` and `ν̄(π)`

Author: Worker 34. This module defines the Hecke character `ν̄(π)` (nu-bar)
of Harris 1999, (5.4) and Theorem 5.7, from the corrected formula in the
erratum of Harris 1998. It also defines the unconjugated character `ν(Gπ)`
of the same erratum, and the relation saying that a `λ`-adic character realizes
`ν̄(π)`. It proves no existence theorem.

## Sources

M. Harris, *The local Langlands conjecture for GL(n) over a p-adic field,
n < p*, Invent. Math. 134 (1998), 177-210, Erratum to [H1], printed pp.181-182
(registered `harris-1998-local-langlands`, SHA256
`7934239ea37d0b91f741ae70c2ac157fe5d619cda4dd992ac24e39ae460c375b`; checked
against the page images). [H1] is M. Harris, *Supercuspidal representations in
the cohomology of Drinfel'd upper half spaces; elaboration of Carayol's
program*, Invent. Math. 129 (1997), 75-119 (registered
`harris-1997-drinfeld-cohomology`, SHA256
`aea284b917442459028b710dbfd9ae537631490504f3bc6d54a1e76ee697e0d9`).

- p.181: "the calculation of the twisting character `ν` on pp.100-101 was
  inconsistent with the definition of `h_Φ`". Here `Z` is the connected center
  of `GG`, and `r_μ : R_{𝒦/ℚ} G_{m,𝒦} → Z` is the algebraic character which on
  rational points is `𝒦^× → Z(ℚ); a ↦ N_{𝒦/𝒦₀} a`. Then
  "(E.1) `ν(Gπ) = ξ⁻¹ ∘ r_μ · |•|_A^{(n-1)/2}`". Further: "the twisting character
  `ν̄` for the Shimura datum `h̄_Φ` is given by formula (E.1), with `r_μ`
  replaced by `r̄_μ`, where (E.2) `r̄_μ(a) = r_μ(ι(a))`; here `ι` denotes complex
  conjugation."
- p.182: "(E.4) `σ(π_v) = [σ̃(π_v) ⊗ ν̄(Gπ)_v^{-1}]^*`. Here `*` denotes
  contragredient."

M. Harris, *Galois properties of cohomological automorphic forms on GL(n)*,
J. Math. Kyoto Univ. 39-2 (1999), 299-318, §5, printed p.313 (registered
`harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`, SHA256
`525a222c4489ee9d3fe86a52c6c17ffb30fcc7c31f24c16a64669e9615085b26`; checked
against the page image):

- "(5.4) `σ(π_v) = [σ̃(π_v) ⊗ ν̄(π)_v^{-1}]^*`, where `*` denotes contragredient
  … and `ν̄(π)` is the character defined in [H2, Erratum]". [H2] is Harris 1998.
- Theorem 5.7(i): "The semisimplification of the representation of
  `Gal(𝒦̄/𝒦)` on `[H^{n-1}(S̄_{K(N)}, W̃)[π] ⊗ ν̄(π)]^*` is the direct sum of
  `a(π)` copies of an `n`-dimensional representation `ρ(π)`."

Text extractions of p.313 show the symbol as "V(π)"; the page image prints
`ν̄(π)`.

## Definitions

In namespace `Langlands.Global.Harris`, let `𝒦` and `𝒦₀` be number fields with
an algebra map `𝒦₀ → 𝒦`, let `n : ℕ` and let `ξ₀` be a Hecke character of
`𝒦₀`. Harris's case is an imaginary quadratic subfield `𝒦₀ ⊂ 𝒦` and `n ≥ 1`;
the definitions need neither restriction.

- `nuCharacter n ξ₀ : HeckeCharacter 𝒦` is
  `(ξ₀ ∘ N_{𝒦/𝒦₀})⁻¹ · ‖·‖^{(n-1)/2}`, that is
  `ν(a) = ξ₀(N_{𝒦/𝒦₀}(a))⁻¹ · ‖a‖^{(n-1)/2}`. This is (E.1). The norm is the
  published continuous norm on idele classes
  `AdelicFunctoriality.ideleClassNorm`. The second factor is
  `HeckeCharacter.normPower 𝒦 ((n - 1)/2)` from
  `Langlands/Global/HeckeNormPower`, with the normalized idelic norm of `𝒦`.
- `nuBarCharacter n ξ₀`, for a CM field `𝒦`, is
  `((ξ₀ ∘ N_{𝒦/𝒦₀}).complexConj)⁻¹ · ‖·‖^{(n-1)/2}`, that is
  `ν̄(a) = ξ₀(N_{𝒦/𝒦₀}(c(a)))⁻¹ · ‖a‖^{(n-1)/2}`. Here `c` is complex
  conjugation of `𝒦` on idele classes, through the published
  `HeckeCharacter.complexConj` and `ideleClassComplexConj`. This is (E.1) with
  `r_μ` replaced by `r̄_μ = r_μ ∘ c` from (E.2): only `r_μ` is conjugated, the
  norm factor is not. This is Harris 1999's `ν̄(π)`.

In namespace `Langlands.GaloisRepresentation.Harris`, for a CM field `𝒦`, a
number field `L`, `ι : L →+* ℂ` and a finite place `λ` of `L`:

- `IsNuBarRealization ι λ n ξ₀ ψ` says that the `λ`-adic character
  `ψ : Gal(𝒦̄/𝒦) → L_λ^×` realizes `nuBarCharacter n ξ₀` through `ι`. It is
  `IsLambdaAdicRealization` from `Langlands/Galois/HeckeCharacterRealization`.
  This is the `λ`-adic character written `ν̄(π)` in Theorem 5.7(i). As
  everywhere in that module, a lift of geometric Frobenius corresponds to a
  uniformizer, matching Harris 1999 (5.6).

## Proved properties

- `nuCharacter_apply` and `nuBarCharacter_apply`: the displayed value formulas,
  by definition.
- `coe_nuBarCharacter_apply`: as complex numbers,
  `ν̄(a) = ξ₀(N(c(a)))⁻¹ · |a|^{(n-1)/2}` with the real power
  of the idelic norm (from `normPower_ofReal_apply`).
- `nuBarCharacter_eq`: `ν̄ = ((ξ₀ ∘ N) ∘ c)⁻¹ · (ξ₀ ∘ N) · ν`, so the two
  characters differ only in the norm-composed factor.

## Conventions recorded for the statements that use `ν̄(π)`

- **Inverse and contragredient.** (5.4) and (E.4) both put the inverse
  `ν̄_v^{-1}` inside the contragredient: `σ(π_v) = [σ̃(π_v) ⊗ ν̄_v^{-1}]^*`.
  Theorem 5.7(i) instead twists the global cohomology by `ν̄(π)` itself and then
  takes the contragredient: `[H^{n-1}[π] ⊗ ν̄(π)]^*`. These definitions produce
  `ν̄` itself; the inverse, the tensor product and the contragredient belong to
  the statements that use it.
- **`v` versus `v̄`.** Harris 1998, p.181: `ν` is the twisting character for the
  Shimura datum `h_Φ` and `ν̄` the one for `h̄_Φ`. "The replacement of `h̄_Φ` by
  `h_Φ` means we have inadvertently calculated the local Galois representation,
  not at the prime `v` where the Shimura variety admits `p`-adic uniformization,
  but rather at its complex conjugate `v̄`." Harris then returns to the
  conventions of Rapoport and Zink, with the datum `(G, X̄_{n-1})` defined from
  `h̄_Φ`, and uses `ν̄`. So statements at the place `v` of `p`-adic
  uniformization, such as (5.4) and Theorem 5.7, use `nuBarCharacter`, not
  `nuCharacter`. This module defines neither `h_Φ` nor the Shimura data.
- **Local components.** `ν̄(π)_v` in (5.4) is the component
  `(nuBarCharacter n ξ₀).finiteComponent v`, a character of `𝒦_v^×`. Harris uses
  it as a character of the local Weil group through local class field theory.
  That identification and its normalization are not formalized here.
- **Superseded formula.** The Lean follows the corrected (E.1)-(E.2), not the
  formula on pp.100-101 of Harris 1997, which the erratum replaces.

## Reading of `ξ` and boundaries

In (E.1), `ξ` is the central character of the automorphic representation, a
character of `Z(ℚ)\Z(A)`. Harris 1997, printed p.100, describes the connected
center as "the subtorus `N^{-1}_{𝒦/F}(G_{m,ℚ}) ⊂ R_{𝒦/ℚ} G_{m,𝒦}`", with `F` the
maximal totally real subfield and `N_{𝒦/F}(z) = z z^c`. Complex conjugation `c`
restricts to the nontrivial automorphism of the imaginary quadratic field `𝒦₀`,
so `z z^c = N_{𝒦₀/ℚ}(z)` for `z` in `𝒦₀`. Hence the subtorus `R_{𝒦₀/ℚ} G_m` lies
in `Z`, and `r_μ = N_{𝒦/𝒦₀}` takes values in it. So `ξ ∘ r_μ` depends only on
the restriction `ξ₀` of `ξ` to `A_{𝒦₀}^×`. That restriction is trivial on
`𝒦₀^×`, so it is a Hecke character of `𝒦₀`, and the Lean takes `ξ₀` as input.
This reduction is a reading of the source, not a Lean theorem.

The following are not formalized:

- the identification of `ξ₀` with the restricted central character of a
  given automorphic representation `π` of Harris's group (left to the
  statements that use `ν̄(π)`);
- the equality `ν̄ = ν ∘ c`, which would follow from `|c(a)| = |a|`; that
  invariance of the idelic norm is not proved here;
- algebraicity of `ν̄` for the central characters that occur, and the existence
  of a `λ`-adic realization `ψ` (`IsNuBarRealization` only states the relation).
