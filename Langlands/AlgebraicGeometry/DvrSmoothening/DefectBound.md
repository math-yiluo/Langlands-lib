# Boundedness of the defect of smoothness

`defectBoundStatement` proves the Library proposition
`Langlands.AlgebraicGeometry.DvrSmoothening.DefectBoundStatement`.

- `length_torsion_le_of_comp_eq_smul`: over a domain `R'`, let `G : R'^m → M` be surjective and
  `H : M → R'^m` with `G ∘ H = c` for some `c ≠ 0`. Then the torsion of `M` has length at most
  `m · ord(c)`, where `ord(c)` is the length of `R' ⧸ c R'`; the torsion is killed by `c` and
  embeds into a quotient of `(R' ⧸ c)^m`.
- `exists_comp_eq_pow_smul`: for a finitely presented `A`-module `M` whose localization away from
  `s` is projective, the surjection `A^m → M` given by generators has a section up to a power of
  `s` (via `exists_lift_of_isLocalizedModule`).
- `defectBoundStatement`: `Ω_{A/R}` is finitely presented (`A` is noetherian), and its localization
  `Ω_{A[1/ϖ]/R}` is projective because `A[1/ϖ]` is smooth over `R`. So `exists_comp_eq_pow_smul`
  gives `m` generators of `Ω_{A/R}` and a section up to `ϖ^e`. For a point `A → R'` of
  ramification index one, base change to `R'` gives the maps of
  `length_torsion_le_of_comp_eq_smul` with `c = ϖ^e`. Since `ϖ` is a uniformizer of `R'`,
  `ord(ϖ^e) = e`, and the defect is at most `m · e`, a bound independent of the point.

This replaces the Fitting-ideal argument of Bosch–Lütkebohmert–Raynaud, *Néron Models*, §3.3,
Proposition 3 (printed pp. 66–67) by a splitting of a presentation of the differentials up to a
power of the uniformizer.
