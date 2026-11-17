# T2: Swan conductor = rank × normalized level, for supercuspidal classes

Module `Langlands.BushnellKutzko.SupercuspidalSwanLevelStatement`, namespace
`Langlands.BushnellKutzko`. Uses `IsNormalizedLevel` from
`Langlands.BushnellKutzko.NormalizedLevel` and, from the Library,
`Correspondence.SupercuspidalAutomorphicClass`, `Correspondence.supercuspidalToAutomorphic`
(`Langlands/Correspondence/SupercuspidalRelations.lean`) and `Henniart.Numerical.conductor`
(`Langlands/Correspondence/HenniartNumericalStatement.lean`).

Sources:

- Operator route note `operator-numerical-llc-route-2026-11-16`, Proposition `prop:T2`
  ("Conductor and level; literature", printed p. 12) and Lemma `lem:level`(i), second sentence, printed p. 16: for
  supercuspidal `π`, `sw(π) = n · ℓ(π)`; §4.4 "Matching the conductors", printed p. 15.
- C. J. Bushnell, *Hereditary orders, Gauss sums and supercuspidal representations of GL_N*
  (1987), `bushnell-1987-hereditary-orders-gauss-sums`, Theorem 3 and (3.5)–(3.8), printed
  p. 198 ff. (PDF page = printed page − 183): the Godement–Jacquet ε-exponent of a supercuspidal
  is `m(π) = N(f/e(𝔄) + d + 1)`.
- C. J. Bushnell and A. Fröhlich, *Non-abelian congruence Gauss sums and p-adic simple
  algebras* (1985), `bushnell-frohlich-1985-nonabelian-congruence-gauss-sums`, (3.3.8), printed p. 258 (PDF p. 52).
- Bushnell–Henniart–Kutzko (1998), (6.1.2), as quoted in the route note: `f(π, ψ) =
  n(1 + c(ψ) + m/e)`, giving `a(π) = n(1 + ℓ(π))` for supercuspidals of rank `n ≥ 2`. In rank one this formula also holds for ramified characters; an unramified character instead has `a(π) = ℓ(π) = 0`, which is covered by the truncated subtraction in T2.

`SupercuspidalSwanLevelStatement.{uK, uV} : Prop` is an unproved statement; a later
`lean.proof@1` task proves it.

## Statement

For every prime `p`, every `K : PadicField.{uK} p`, every `k : ℕ`, every supercuspidal class
`π : SupercuspidalAutomorphicClass.{uK, uV} K k.succPNat` of `GL_{k+1}(K)` and every `x : ℚ`
with `IsNormalizedLevel K (k + 1) (supercuspidalToAutomorphic K π) x`, there is `c : ℕ` with

- `Henniart.Numerical.conductor K π = c` (the conductor, a priori in `WithTop ℕ`, is finite),
  and
- `((c - (k + 1) : ℕ) : ℚ) = (k + 1) * x`, with truncated subtraction in `ℕ`.

Here `Numerical.conductor K π` is `GeneralLinear.SupercuspidalClass.firstFixedLevel`, the first
level at which the JPSS congruence subgroup has a nonzero fixed vector. Its interpretation as
the conductor exponent `a(π)` uses the comparison described below. The truncated difference
`c − n`, with `n = k + 1`, is the Swan conductor `sw(π)` of the route note. So the statement is
`sw(π) = n · ℓ(π)`. It is Task 7370's `HasSupercuspidalSwan K π (n · ℓ(π))` written out
(`∃ a, conductor K π = a ∧ a − (k + 1) = s`), stated without depending on Task 7370 or Task 7373,
which are not in the Library.

Sanity checks: in rank one (`k = 0`), `π` is a quasicharacter `χ`; for unramified `χ`,
`a(χ) = 0` and `ℓ = 0`, and `0 − 1 = 0` in `ℕ`; for ramified `χ` with `a(χ) = c ≥ 1`, `χ` is
trivial on `U^c` but not on `U^{c−1}`, so `ℓ = c − 1 = c − (k + 1)`. In level zero, `sw(π) = 0`
and `ℓ(π) = 0`.

## Proof route (for the proof task)

Every supercuspidal `π` of positive level contains a nondegenerate fundamental stratum
(Bushnell 1987, Theorem 2′ and §3); Bushnell 1987, Theorem 3 with Bushnell–Fröhlich (3.3.8)
computes the Godement–Jacquet ε-exponent; L1 identifies `m/e` with `ℓ(π)`; the comparison of
Godement–Jacquet and JPSS ε-factors on `GL_n × GL_1` and the Library's proved
`Langlands.Conductor.supercuspidalPadicConductorExponent` (JPSS 1981, Theorem (5.1), for
supercuspidals) turn the exponent into `Numerical.conductor`.

The published theorem `Langlands.GodementJacquet.whittakerModelComparison`
(`Langlands/Representation/GodementJacquet/WhittakerModelComparisonProof.lean`) proves
`WhittakerModelComparisonStatement` without premises. It identifies the spaces `I₂` and `I₃`
of rational continuations on the coefficient model; applying it to identify the normalized
Godement–Jacquet and JPSS epsilon exponents still requires the corresponding normalization
and functional-equation argument.
