# Character periods on actual compact left quotients

This internal interface implements the quotient period underlying
Getz–Hahn (2024), §9.2, (9.7) and Proposition 9.2.2, with the corrected
compact quotient after (9.9) in the October 2026 errata. It uses the
existing actual left coset spaces and measures. The group universes are
independent.

Let `Γ ≤ G`, `Λ ≤ H`, and `j : H →* G` with `j(Λ) ⊆ Γ`. For a
character `χ : H →* ℂˣ` trivial on `Λ`, the file defines:

- `periodOrbitMap`: the actual map `Λ \ H → Γ \ G` sending
  `[h]` to `[j(h)g]` for a specified right-translation parameter `g`.
- `periodQuotientCharacter`: the descended character on `Λ \ H`.
- `periodIntegrand`: the function
  `χ(h)⁻¹ φ([j(h)g])` on that actual quotient.
- `HasConvergentQuotientCharacterPeriod`: absolute integrability of
  this integrand for the supplied quotient measure.
- `quotientCharacterPeriod`: its total Bochner integral.
- `normalizedQuotientCharacterPeriod`: the same actual period for the
  existing `normalizedMeasure` built from the canonical Borel fundamental
  domain of a discrete subgroup.

The subgroup inclusion and character triviality prove descent
pointwise. The orbit map is continuous for continuous `j`; the descended
character is continuous for continuous `χ`. The integrand is continuous
for continuous `φ`, and strongly measurable for strongly measurable `φ`
under the stated Borel assumptions. On a compact quotient with finite
Borel measure, continuity proves absolute convergence.

For second-countable Borel topological `H`, discrete `Λ`, a
`Λ`-invariant measure `νH`, and any actual fundamental domain `s`, the
implemented comparison is

`normalized period = ((νH s)⁻¹).toReal • ∫ h in s, χ(h)⁻¹ φ([j(h)g]) dνH`.

This identity requires continuous `j`, continuous `χ`, and a strongly
measurable `φ`. It follows from actual normalized-measure
domain independence and the existing Bochner pushforward integral
formula. It remains an identity of total Bochner integrals; it does not
by itself prove absolute convergence of an arbitrary L² representative.
No character unitarity, subgroup normality, finite total ambient measure,
or unproved equality between different pointwise L² representatives is
used.

The relatively compact Borel-domain refinement supplies the bounded
domain and positive finite mass needed in the subsequent application.
This file imports only already published fundamental-domain and Mathlib
interfaces; it does not import that pending refinement. The actual
parabolic-radical/positive quotient specialization, joint absolute
integrability for L² periods, modular-corrected integrated-action
comparison, test separation, and full almost-everywhere cuspidal
closedness remain later obligations.
