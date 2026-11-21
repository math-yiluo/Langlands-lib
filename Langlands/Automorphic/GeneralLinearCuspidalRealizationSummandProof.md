# From a cuspidal operator realization to an irreducible cuspidal `L²` summand

`Langlands.Automorphic.GroupSchemeFunctions.generalLinearCuspidalRealizationSummand`
proves the unchanged `GeneralLinearCuspidalRealizationSummandStatement.{u}`. It uses the
positive-central descent hypothesis of that statement. It constructs `Φ` by taking classes of
the descended functions and takes `P` to be `(LinearMap.range Φ).topologicalClosure` inside
`S = fullAEL2CuspidalSubmodule`. The invariance is for the full adelic action `πc`, not only for
the operators defining the realization.

## Sources and scope

- J. R. Getz and H. Hahn, *An Introduction to Automorphic Representations*, GTM 300, Springer,
  2024 (`getz-hahn-2024-automorphic-representations`), §6.5, pp. 168–169 (PDF pp. 182–183),
  for `L²_cusp([G])` and the discrete cuspidal representations. The occurrence of a
  realization in the cuspidal Hilbert space is the realization-to-summand part of Theorem
  9.7.3, p. 265 (PDF p. 277), especially the passage leading to (9.42), pp. 265–266 (PDF
  pp. 277–278). The exact `GL_{r+1}` target, including the identification with classes of
  functions, is described in `GeneralLinearCuspidalSummandRealizationStatement.md`.
- A. Borel and H. Jacquet, *Automorphic forms and automorphic representations*, Proc. Sympos.
  Pure Math. 33, part 1, 1979, pp. 189–202 (`borel-jacquet-1979-automorphic`), §3.3, p. 194
  (PDF p. 189), for cuspidality, and §4.1–4.2, pp. 194–195 (PDF pp. 189–190), for the
  smoothness, finite level, infinitesimal finiteness and slice-growth conventions of the
  Library's form model. The boundedness and square-integrability comparison for cusp forms
  with a central character is §4.4(i)–(iii), p. 196 (PDF p. 191).

The implementation takes a different route from the source proof and the suggested isotypic
placement argument in the statement Markdown. It uses neither rapid decay on the full
positive-central quotient (Getz–Hahn Theorem 9.7.1, p. 264, PDF p. 276), the finite-multiplicity
spectral decomposition (Corollary 9.1.3, p. 241, PDF p. 253), nor `K`-finite density and smoothing
on a previously chosen irreducible summand (Lemma 9.7.2, pp. 264–265, PDF pp. 276–277).
It does not invoke Borel–Jacquet §4.4's comparison or require a unitary central character.
The theorem asserts no converse, multiplicity, or identification of the image with the space
of all `K`-finite vectors of `P`.

## Implemented proof

1. **Class map and band pairings.** The auxiliary `RealizationSummandBandMeasure` compares the
   determinant band of the principal rational quotient with the positive-central rational
   quotient `Q`. Its projection pushes band measure forward to `c • μQ`. The class map in
   `RealizationSummandClassMap` uses the existing `memLp_translate_of_cuspidal` on the band at
   the identity to obtain square integrability of each descended function. Pointwise vanishing
   of proper parabolic periods gives membership of its class in the full AE cuspidal submodule.
   The class map is injective by positivity of quotient Haar measure on nonempty opens, and
   intertwines the finite and archimedean compact actions. The band constant is nonzero and
   finite; `inner_bandPullback_translated` compares the pairing of a pulled-back `L²(Q)` test
   vector with a translated band vector to the quotient pairing, with factor `c.toReal`.
2. **Invariance of the closure.** A vector orthogonal to `range Φ` pulls back to a test vector
   annihilating the original band image. `band_annihilator` applies the analytic jet argument
   of `CuspidalBandOrbitClosure` directly to the covariant smooth `coefficientMap` of
   `CuspidalHilbertOrbitCoefficientProof`. The compact and enveloping operators stay in the
   source, so every enveloping evaluation of the coefficient at a compact representative of
   the component vanishes. Joint finiteness gives analyticity, hence the coefficient vanishes
   throughout the component. The band comparison and `c.toReal ≠ 0` transfer this vanishing to
   the quotient. The orthogonal-annihilator criterion therefore puts every archimedean
   translate of `Φ f` in `P`. A general adelic element factors as an infinite part times a
   finite part, and the finite part preserves `range Φ`. Continuity of the bounded action
   extends the resulting containment to `P`. Injectivity and nontriviality of the realization
   show that `P` is nonzero.
3. **Unitary forms.** For every `w : S` and real Lie direction `X`, the derivative at zero of
   `t ↦ ⟪w, πc(exp(tX)) (Φ f)⟫` is `⟪w, Φ(D_X f)⟫`, with the actual archimedean curve embedded
   adelically. This follows by transferring the scalar derivative of the smooth band
   coefficient, using its Lie covariance and dividing by `c.toReal`. No norm derivative in
   `S` is needed. For a symmetric operator `B` on `S` commuting with the adelic action and
   dominating the identity in real part, `unitaryFormOf` pulls back `⟪B x, y⟫` along `Φ`.
   The compact and finite intertwining give invariance. Unitarity, symmetry, and
   `exp(-tX) = exp(tX)⁻¹` identify the coefficient with the conjugate of the coefficient with
   `f` and `g` exchanged and `t` negated. Differentiation gives the skew-invariance required
   for a full `OperatorRealization.UnitaryForm`.
4. **Minimality.** For a closed invariant `U ≤ P`, its orthogonal projection `E` in `S`
   commutes with the action, since inverse translations preserve `U` and hence translations
   preserve `Uᗮ`. Use `B = 1` and `B = 1 + E` in the preceding construction. The added
   projection is symmetric and positive semidefinite. By
   `OperatorRealization.UnitaryForm.exists_pos_scalar`, using irreducibility of `R` and
   `CuspidalOperatorRealization.isJointlyAdmissible`, the forms are proportional by a real
   scalar `a > 0`. Thus `(1 + E)(Φ f) - a • Φ f` is in `P` and orthogonal to `range Φ`, hence
   also to `P`. It vanishes, so `E(Φ f) = (a - 1) • Φ f`. If `a - 1 = 0`, `P` is contained
   in `Uᗮ`, and `U ≤ P` forces `U = 0`. Otherwise `range Φ ⊆ U`, and closedness gives `U = P`.
   This yields the required minimality without decomposing `S`.
