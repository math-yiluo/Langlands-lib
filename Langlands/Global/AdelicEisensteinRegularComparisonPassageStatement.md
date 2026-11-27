# The regular-patch comparison from the standard family comparison: statement

Module `Langlands.Global.AdelicEisensteinRegularComparisonPassageStatement` states
`Langlands.Global.EisensteinRegularComparisonPassageStatement` as a proposition. It supplies no
proof.

## Statement

`EisensteinRegularComparisonPassageStatement.{u}` is the implication

```
BruhatTitsAvailabilityStatement.{u} →
  StandardEisensteinFamilyComparisonStatement.{u} →
  RootPresentationRegularityComparisonStatement.{u} →
  EisensteinFunctionalEquationRegularComparisonStatement.{u}
```

between four propositions of the Library:

- `Langlands.Geometry.Building.BruhatTitsAvailabilityStatement` (module
  `Langlands.Geometry.Building.BruhatTitsAvailabilityStatement`): Bruhat–Tits theory is
  available for every connected reductive group over a nonarchimedean local field (the
  Kaletha–Prasad conclusion recorded there).
- `StandardEisensteinFamilyComparisonStatement` (module
  `Langlands.Global.AdelicEisensteinStandardFamilyComparisonStatement`): for a meromorphic `EP`
  equal to `Σ_v b_v(λ) E(φ_v, λ)` and with `Σ_v b_v(λ) M(n, λ)φ_v = Σ_i coeff_i(λ) ψ_i` for
  regular `λ`, the identity `EP(λ) = Σ_i coeff_i(λ) E(ψ_i, nλ)` on a nonempty open patch of
  parameters with `nλ` as regular as required. Here `φ_v`, `b_v` form a finite family of
  inducing forms with meromorphic coefficients, `P_I`, `P_Q` are standard parabolics of one
  standard family, `n` is a rational point of the normalizer of its maximal split torus whose
  Weyl class maps the simple roots of `I` into `Q` and whose inverse maps those of `Q` into
  `I`, and the maximal compact subgroup is in good position.
- `RootPresentationRegularityComparisonStatement` (module
  `Langlands.Global.AdelicEisensteinRegularityPresentationComparisonStatement`): for two root
  presentations of one parabolic with one Levi image, possibly with different maximal split
  tori, a large enough regularity threshold for the second presentation forces any given
  threshold for the first.
- `EisensteinFunctionalEquationRegularComparisonStatement` (module
  `Langlands.Global.AdelicEisensteinFunctionalEquationRegularComparisonStatement`): the same
  comparison for one inducing form, for arbitrary parabolics `P`, `Q` of a connected reductive
  group with root presentations, an arbitrary Weyl conjugation `(w, c)` from `P` to `Q`, a Levi
  projection of `Q`, and an arbitrary maximal compact subgroup `K` with Iwasawa coverage for `P`
  and `Q`.

So the proposition says that the general comparison reduces to the standard one: no position
of `P`, `Q`, `w` or `K` is required beyond what the general statement assumes.

## Source and provenance

Provenance: derived. J. Bernstein and E. Lapid, *On the meromorphic continuation of Eisenstein
series*, J. Amer. Math. Soc. 37 (2024), §2, registered as
`bernstein-lapid-2024-meromorphic-continuation-eisenstein`, fix a minimal parabolic, a maximal
split torus and a maximal compact subgroup in good position, and work with standard parabolics
and Weyl elements in the normalizer of the torus. The Library's general statement allows any
parabolics, root presentations, Weyl representatives and Iwasawa compacts. This proposition
records that the general form follows from the standard one, given the Bruhat–Tits input for
the existence of a good maximal compact subgroup and the comparison of regularity across
presentations.
