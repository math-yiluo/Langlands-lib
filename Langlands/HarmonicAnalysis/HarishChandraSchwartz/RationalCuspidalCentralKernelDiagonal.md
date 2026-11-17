# The diagonal of the VIII.4.1 kernel as conjugation pairings

Source: J.-L. Waldspurger, *La formule de Plancherel pour les groupes
p-adiques (d'après Harish-Chandra)*, J. Inst. Math. Jussieu 2 (2003),
235–333, proof of Proposition VIII.4.1, printed pp. 329–330 (PDF pp. 95–96),
registered source `waldspurger-2003-plancherel`.

This module is a follow-up to focused unit 2 of Task 7439 (revision 2). It
imports `RationalCuspidalCentralKernelStep` (unit 2). It
reduces unit 2's named open prerequisite `RationalLevelKernelDiagonalIntegrable`
to the integrability of the bilinear conjugation pairings of Task 7256
(`conjugationPairing`, `RationalConjugationPairing.lean`, already in the
Library).

## The source step

On printed p. 329 the source writes `α_χ(g, g) = ∫_G °e(g⁻¹ g' g) ψ(g') dg'`,
where `ψ` lives on `A_G H` and `ψ(a h) = χ(a) mes(A_G ∩ H) mes(H)⁻²`. Because
`°e` is supported in `G¹`, it replaces `ψ` by `ψ` times the characteristic
function of `G¹`, and it bounds the diagonal integral by VIII.3.2. The Lean
route avoids the measure identity on `A_G H` behind this formula. Instead it
writes `α_χ(x, x)` as a finite linear combination of pairings with
characteristic functions of cosets `H a`.

## Generic results

`G` is a topological group with a Borel structure, `μ_G` a right-invariant
measure, `H` an open subgroup, and `μ_H = μ_G.comap H.subtype` the
restriction.

- `rightCosetIndicator H a` is the function `g ↦ 1_H(g a⁻¹)`, the
  characteristic function of `H a`.
- `integral_comap_eq_conjugationPairing`:
  `∫_H E(x⁻¹ h a x) dμ_H(h) = conjugationPairing μ_G E 1_{H a} x⁻¹`, where
  `conjugationPairing μ f₁ f₂ y = ∫ f₁(y g y⁻¹) f₂(g) dμ(g)`. The proof
  converts the integral over `H` into a set integral
  (`integral_subtype_comap`), writes it as the integral of an indicator, and
  substitutes `g ↦ g a⁻¹` (`integral_mul_right_eq_self`). No integrability
  is needed.
- `kernelAlphaChi_self_eq`: for central `A` with an inversion-invariant
  measure,
  `α_χ(x, x) = mes(H)⁻² ∫_A χ(a) conjugationPairing μ_G E 1_{H a} x⁻¹ da`.
  It follows from `kernelAlphaChi_eq` (the source's second expression for
  `α_χ`) and the previous identity.
- `conjugationPairing_rightCosetIndicator_eq_zero`: suppose `E` vanishes
  outside a normal subgroup `N ⊇ H` and `a ∉ N`. Then the pairing with
  `1_{H a}` vanishes. Indeed `g ∈ H a` forces `g ∉ N`, hence
  `y g y⁻¹ ∉ N`.
- `rightCosetIndicator_mul_of_mem`: `1_{H a b} = 1_{H a}` for central `a` and
  `b ∈ H`.
- `integrable_kernelAlphaChi_self`. Assume: `A` is central with a Borel,
  inversion-invariant measure that is finite on compacts; `χ` is trivial on
  `A ∩ H`; `E` vanishes outside an open normal subgroup `N ⊇ H`; and
  `{a ∈ A | a ∈ N}` is compact. Assume moreover that every function
  `q ↦ conjugationPairing μ_G E 1_{H a} (q̇⁻¹)` is integrable on `A \ G` for
  a measure `ν`. Then `q ↦ Re α_χ(q̇, q̇)` is `ν`-integrable.

  Proof. Let `S = {a ∈ A | a ∈ N}`. It is open and compact, and the
  integrand over `A` vanishes outside `S`
  (`setIntegral_eq_integral_of_forall_compl_eq_zero`). The family
  `S → (G → ℂ)`, `a ↦ (x ↦ χ(a) conjugationPairing μ_G E 1_{H a} x⁻¹)`, is
  locally constant: it does not change under `a ↦ a b` for `b ∈ A ∩ H`,
  because `χ(b) = 1` and by `rightCosetIndicator_mul_of_mem`. Unit 2's
  `integral_apply_eq_sum_of_isLocallyConstant` therefore writes the integral
  over `S` as a finite combination of members of the family. Each member is
  integrable by hypothesis, so the finite sum is integrable
  (`integrable_finsetSum`), and so is its real part.

## Rational results

- `RationalLevelKernelPairingIntegrable hKc hPK ρ muA muG H E` is the named
  pairing input. Take any right-invariance instance for `muA`, any Borel
  structure on `A_G(F) \ G(F)`, any quotient measure `muQ` compatible with
  `muG` and `muA`, and any `a ∈ A_G(F)`. Then
  `q ↦ conjugationPairing muG E 1_{H a} (q̇⁻¹)` is `muQ`-integrable.
- `IsRationalCuspidalLevelKernel.diagonalIntegrable` assumes: `G` connected
  reductive, `hs : IsSplitComponent s`, a Haar measure `muA`, a Haar measure
  `muG`, a compact open `H` with `χ` trivial on `A_G(F) ∩ H`, and
  `IsRationalCuspidalLevelKernel hKc hPK ρ muG H E`. It proves
  `RationalLevelKernelDiagonalIntegrable hKc hPK ρ muA χ muG H E` from
  `RationalLevelKernelPairingIntegrable hKc hPK ρ muA muG H E`. It applies
  `integrable_kernelAlphaChi_self` with `N = G¹ = rationalCommonNormKernel G`.
  This subgroup is normal and open (`isOpen_rationalCommonNormKernel`). It
  contains `H` because `H` is compact
  (`compactSubgroup_le_rationalCommonNormKernel`). `A_G(F) ∩ G¹` is compact
  for connected reductive `G` (`isCompact_splitComponent_inf_commonNormKernel`).
  `E` vanishes outside `G¹` by the field `eq_zero_of_not_mem`, and `muA` is
  inversion invariant by unit 2's `isInvInvariant_of_le_center`. The right
  invariance of `muG` needed by `integral_comap_eq_conjugationPairing` comes
  from unit 2's `rationalHaar_isMulRightInvariant`.

The theorem requires `χ` trivial on `A_G(F) ∩ H`, as in the source. The
complementary case is handled by unit 1.

## Open hypotheses and their owners

- `RationalLevelKernelPairingIntegrable`. Its source is VIII.3.2, owned by
  Task 7256 (`b0fd13d7-7b2e-4cec-97ef-3a2286d8ed7c`). Task 7439's follow-up
  module `RationalCuspidalCentralKernelPairing` derives it from the VIII.3.2
  integrability form at `f₁ = E`. That form is concluded by Task 7256's
  statement `RationalCuspidalConjugationIntegrabilityStatement` (candidate
  `9f4689cd-0a2e-43cd-bef8-c3551ceb0281`, accepted, not yet in the Library).
- `IsRationalCuspidalLevelKernel hKc hPK ρ muG H E`: focused unit 3 of Task
  7439 and Task 7277 (`eaceb96b-aaaf-4068-9a11-46292b5334e6`), as listed in
  unit 2.
- `IsConnectedReductive G` and `χ` trivial on `A_G(F) ∩ H` are hypotheses of
  the source situation. The complementary case of `χ` is unit 1 of Task 7439.

Nothing here assumes same-rank finiteness, same-rank reconstruction, the
closed target or a dimension bound.
