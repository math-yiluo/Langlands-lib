# Proof of the reduction of Laumon's numerical statement E1b

Module `Langlands.Correspondence.HenniartLaumonNumericalReductionProof`. It imports
`Langlands.Correspondence.HenniartLaumonNumericalReductionStatement` and
`Langlands.Galois.CoefficientIdentification`, and proves the published statement
`Langlands.Henniart.LaumonNumericalReductionStatement` (module
`Langlands.Correspondence.HenniartLaumonNumericalReductionStatement`) as the theorem

```lean
theorem Langlands.Henniart.laumonNumericalReduction :
    LaumonNumericalReductionStatement.{uK, uW}
```

with both universe parameters free. The statement and its relation to Henniart (1988),
§4.3, are explained in its own Markdown. In short: the ℓ-adic/Weil orbit comparison
`LadicWeilOrbitComparisonStatement.{uK, uK, uW}` and Laumon's twist-equivariant bijection
`LaumonLadicTwistBijectionStatement.{uK, uW}` imply Laumon's numerical statement E1b,
`LaumonNumericalStatement.{uK, uW}`.

The theorem is a reduction. It proves E1b from its two premises and does not prove the
premises; it uses no other unproved statement of the Library. Of E1b's two hypotheses on
`d s f` it uses `1 ≤ s` (a hypothesis of Laumon's bijection) and not the divisibility
`f ∣ Nat.gcd (d + 1) s`: the conclusion is proved for every torsion number `f`.

## Declarations

- `Langlands.Henniart.LocalNumerical.ladicUnramifiedOrbitClass_eq_iff`: two ℓ-adic classes
  `ρ ρ'` of rank `k + 1` have the same unramified-twist orbit
  (`ladicUnramifiedOrbitClass K Ω ℓ k ρ = ladicUnramifiedOrbitClass K Ω ℓ k ρ'`) if and
  only if `ladicUnramifiedTwist K Ω ℓ k χ ρ' = ρ` for some unramified character `χ`.
- `Langlands.Henniart.LocalNumerical.ladicRefinedStratum_encard_eq_of_twistEquiv`: over
  any nonarchimedean local field `K` with separable closure `Ω`, for any prime `ℓ` and any
  `ι : PadicAlgCl ℓ →+* ℂ`, a bijection `Φ` from the irreducible ℓ-adic classes of rank
  `k + 1` with `LadicHasSwan K Ω ℓ ι ρ s` onto those of rank `k' + 1` with Swan exponent
  `s`, which satisfies the twist compatibility of `LaumonLadicTwistBijectionStatement`
  (for every `χ` and `ρ`, the twist `χ ρ` again has Swan exponent `s` and
  `Φ (χ ρ) = χ (Φ ρ)`), gives
  `(ladicRefinedStratum K Ω ℓ ι k s f).encard = (ladicRefinedStratum K Ω ℓ ι k' s f).encard`
  for every `f`.
- `Langlands.Henniart.laumonNumericalReduction`: the target.

## The implemented proof

### Equivariant bijections and refined ℓ-adic strata

`ladicUnramifiedOrbitClass_eq_iff` unfolds the orbit class to the quotient of the
twist action `ladicUnramifiedTwistAction` on `Σ k, IrreducibleLadicClass K Ω ℓ k.succPNat`:
equality of classes is `MulAction.orbitRel`, that is, `χ • ⟨k, ρ'⟩ = ⟨k, ρ⟩` for some `χ`,
and the action keeps the rank, so this is equality in the fibre over `k`
(`sigma_mk_injective`).

In `ladicRefinedStratum_encard_eq_of_twistEquiv`, write `A` and `B` for the two subtypes
of classes of Swan exponent `s` and `χ ρ` for `ladicUnramifiedTwist … χ ρ`.

1. **Twists in both directions.** For `ρ₁ ρ₂ ∈ A` and every `χ`: `χ ρ₁ = ρ₂` if and only if
   `χ (Φ ρ₁) = Φ ρ₂`. By the hypothesis, `χ (Φ ρ₁)` is `Φ` of the class `χ ρ₁` (which lies
   in `A`); the forward direction applies `Φ`, the converse uses that `Φ` is injective.
   This is the remark of the route note that an injection commuting with the twists
   preserves stabilizers.
2. **Torsion numbers.** By step 1 with `ρ₁ = ρ₂ = ρ`, the characters fixing `ρ` are those
   fixing `Φ ρ`, so `ladicTorsionNumber (Φ ρ) = ladicTorsionNumber ρ`
   (`Nat.card_congr` of `Equiv.subtypeEquivRight`).
3. **Orbits.** By `ladicUnramifiedOrbitClass_eq_iff` and step 1, `ρ₁, ρ₂ ∈ A` have the same
   orbit if and only if `Φ ρ₁, Φ ρ₂` have the same orbit.
4. **The map of orbits.** The function `F` on `LadicUnramifiedOrbitClasses K Ω ℓ` sends an
   orbit `c` to the orbit of `Φ ρ`, for a chosen `ρ ∈ A` whose orbit is `c` when one
   exists, and fixes `c` otherwise. By step 3, `F` sends the orbit of every `ρ ∈ A` to the
   orbit of `Φ ρ`, whatever representative was chosen, and is injective on
   `ladicRefinedStratum K Ω ℓ ι k s f`.
5. **The image.** `F` maps `ladicRefinedStratum … k s f` onto
   `ladicRefinedStratum … k' s f`: an orbit of `ρ ∈ A` with torsion number `f` goes to the
   orbit of `Φ ρ ∈ B`, of torsion number `f` by step 2; conversely, a class `ρ' ∈ B` of
   torsion number `f` is `Φ ρ` for `ρ = Φ⁻¹ ρ'`, which has torsion number `f` by step 2,
   and the orbit of `ρ'` is `F` of the orbit of `ρ`.
6. The image of a set under a map injective on it has the same `encard`
   (`Set.InjOn.encard_image`).

### The reduction

Let `k` be a finite field, `d s f : ℕ` with `1 ≤ s`, `X = LaurentSeries k` with the
valuative relation `LocalField.Laurent.valuativeRel k`, and `Ω = SeparableClosure X`.

1. **The prime.** If `(2 : k) ≠ 0` take `ℓ = 2`; otherwise `(3 : k) = 2 + 1 = 1 ≠ 0` and
   take `ℓ = 3`. Either way `ℓ` is prime and `(ℓ : k) ≠ 0`.
2. **The embedding.** `ι` is the ring homomorphism underlying the isomorphism
   `Langlands.GaloisRepresentation.padicAlgClComplexEquiv ℓ : PadicAlgCl ℓ ≃+* ℂ`
   (module `Langlands.Galois.CoefficientIdentification`), which exists because both fields
   are algebraically closed of characteristic zero and of the cardinality of the
   continuum (`IsAlgClosed.ringEquiv_of_equiv_of_charZero`).
3. **The residue hypothesis.** `LocalField.Laurent.residueEquiv k` identifies the residue
   field `𝓀[X]` with `k`, and it sends `(ℓ : 𝓀[X])` to `(ℓ : k)`; so
   `((ℓ : ℕ) : 𝓀[X]) ≠ 0`, the hypothesis of the orbit comparison at `K = X`.
4. **Laumon's bijection.** `LaumonLadicTwistBijectionStatement` at `k`, `ℓ`, `ι`, `d`, `s`
   gives `Φ` and its twist compatibility; by the lemma above,
   `ladicRefinedStratum X Ω ℓ ι d s f` and `ladicRefinedStratum X Ω ℓ ι (d + s) s f` have
   the same `encard`.
5. **The orbit comparison.** `LadicWeilOrbitComparisonStatement` at `X`, `Ω`, `ℓ`, `ι`
   gives an equivalence `e` of orbit spaces with
   `e '' ladicRefinedStratum X Ω ℓ ι j s f = weilRefinedStratum X Ω j s f` for all `j`.
   Rewriting both Weil strata as images under the injective `e`
   (`Function.Injective.encard_image`) reduces the goal to step 4.

## Provenance

The proof follows Henniart (1988), §4.3, printed pp. 510–511, and the route note's proof
of Corollary `cor:Laumon` (lines 797–802): "Compatibility with unramified twists gives a
bijection of the sets of orbits that preserves stabilizers" is steps 1–5 of the lemma, and
the correspondence of ℓ-adic and complex Weil orbits with dimensions and conductors is the
orbit comparison premise. The route note's §2.2 (line 197) records that an injection
commuting with the twist action preserves stabilizers, hence torsion numbers, which is
steps 1 and 2. Henniart (§4.1, p. 509) fixes a prime `ℓ` different from the residue
characteristic `p`; the choice `ℓ ∈ {2, 3}` is one such prime. Henniart (§4.2, p. 510)
compares ℓ-adic and complex classes of finite image through an isomorphism of the
algebraic closures of `ℚ` in `ℂ` and in `\bar{ℚ}_ℓ`; in the Library's statements this
comparison is made through a ring homomorphism `ι : PadicAlgCl ℓ →+* ℂ`, a parameter of
both premises, and the proof instantiates it with `padicAlgClComplexEquiv ℓ`.

## Sources

- G. Henniart, *La conjecture de Langlands locale numérique pour GL(n)*,
  Ann. Sci. ÉNS (4) 21 (1988), 497–544, `henniart-1988-numerical`; printed page = PDF
  page + 495. §§4.1–4.3, pp. 509–511 (PDF pp. 14–16).
- *The numerical local Langlands correspondence for GL_n: counts on the two sides and the
  recommended route of proof* (16 November 2026), `operator-numerical-llc-route-2026-11-16`,
  `numerical-LLC-route.tex`, Corollary `cor:Laumon` and its proof, lines 794–802, and §2.2,
  lines 182–197.
- [Laumon's local Fourier transform for E1b: source map](../../notes/henniart/laumon-local-fourier-source-map.md),
  §1, steps (c) and (d).
