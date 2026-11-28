# Matching geometric terms of `Res_{L/K} GL_n` and `GL_n`

Module `Langlands.TraceFormula.GeneralLinearBaseChangeTermMatching`, namespace
`Langlands.TraceFormula`. It uses the notation of
`Langlands.TraceFormula.GeneralLinearBaseChangeNormPairing` (`GLₙ`, `Wₙ`, `Θₙ`, the matrix
coordinates `Φ = cyclicWeilAdelicMap K L n` and `GeneralLinearGroupPoints.adelicHomeomorph`,
the ordered norm `N`, the relation `BaseChangeNormRelated`) and the measure data
`TwistedGeometricMeasures` of `Langlands.TraceFormula.SingleOrbitGeometricTrace`.

The module turns the two orbital-integral hypotheses of
`GeneralLinearBaseChangeTraceComparisonStatement` into the term matching and term vanishing
inputs of `geometricExpansion_eq_mul_of_termPairing_continuousMulEquiv` (module
`Langlands.TraceFormula.BaseChangeTermPairing`).

## Definitions

Both are the corresponding hypotheses of `GeneralLinearBaseChangeTraceComparisonStatement`,
for given `σ`, `l`, `n`, finite places `w` of `L` and `v` of `K`, and functions
`φOne : Wₙ(𝔸_K)¹ → ℂ`, `fOne : GLₙ(𝔸_K)¹ → ℂ`. The local abbreviations `Φ`, `N` and `ΦG` of
the statement are written out.

- `BaseChangeOrbitalMatching σ l n w v φOne fOne c` (hypothesis 1 of the statement). Let
  `r, q` be rational norm-one points and `y ∈ GL_n(L)` with
  `Φ(N(r)) · rational(y) = rational(y) · ΦG(q)`, where `Φ(N(r))` is regular elliptic at `w`
  or `q` is regular elliptic at `v`. Let `e` be a group isomorphism of the
  `θ`-centralizer of `r` onto the centralizer of `q` with
  `ΦG(e(x)) = rational(y)⁻¹ Φ(x) rational(y)`. Take a right-invariant measure `μr`, finite on
  compacts and positive on open sets, and a right-invariant `μq` with `μr.map e = μq`. Then
  `twistedOrbitalIntegral θ r νr φOne = c * orbitalIntegral q νq fOne` for all compatible
  quotient measures `νr`, `νq`.
- `BaseChangeOrbitalVanishing σ l n v fOne` (hypothesis 2 of the statement). Let `q` be
  rational and regular elliptic at `v` with `Φ(N(r)) · rational(y) ≠ rational(y) · ΦG(q)` for
  all rational `r` and all `y`. Then every orbital integral of `fOne` at `q`, for a
  right-invariant centralizer measure finite on compacts and positive on open sets and a
  compatible quotient measure, is `0`.

## Results

- `orbitalMatch_toMonoidHom`: an abstract restatement. A matching hypothesis for a
  topological group automorphism `θ : H ≃ₜ* H`, quantified over isomorphisms of centralizers
  satisfying a predicate `P`, holds verbatim for `θ.toMonoidHom`. The twisted centralizers
  and twisted orbital integrals of `θ` and `θ.toMonoidHom` agree definitionally.
- `exists_baseChangeCentralizerEquiv_of_related`: for rational `r`, `q` and `y ∈ GL_n(L)` as
  in the relation, with either regularity condition, there is
  `e : twistedCentralizer Θₙ.toMonoidHom r ≃ₜ* twistedCentralizer (MonoidHom.id _) q` with
  `ΦG(e(x)) = rational(y)⁻¹ Φ(x) rational(y)`, matching rational points; both centralizers
  are commutative. Proof: the rational coordinates `a`, `b` of `r`, `q` exist, `b` is regular
  semisimple (`isRegularSemisimple_of_baseChangeNormRelated`), and
  `exists_baseChangeCentralizerEquiv` gives `e` (module
  `Langlands.TraceFormula.GeneralLinearBaseChangeCentralizerEquiv`). The centralizer of `q`
  is commutative by `centralizer_commutative_of_isRegularSemisimple`, and that of `r` by
  transport along `e`.
- `nonempty_twistedGeometricMeasures_baseChange`: if `Φ(N(r))` is regular elliptic at `w`, the
  term at `r` has measure data. Proof: `exists_baseChangeNormRelated` gives a related `q`, the
  previous result makes the `θ`-centralizer of `r` commutative, and
  `nonempty_twistedGeometricMeasures_of_commutative` applies (the rational subgroup is
  discrete, `isDiscrete_rationalNormOneSubgroup`).
- `baseChange_termMatch`: from `BaseChangeOrbitalMatching`, for related rational `r`, `q`
  with either regularity condition, both `TwistedTermMatchesOrdinaryTerm` and
  `OrdinaryTermMatchesTwistedTerm` hold at `(r, q)` for `Θₙ.toMonoidHom` and the Haar
  measures.
- `baseChange_orbitalIntegral_eq_zero`: from `BaseChangeOrbitalVanishing`, if `q` is rational,
  regular elliptic at `v` and related to no rational `r`, then
  `orbitalIntegral q d'.orbital fOne = 0` for all measure data `d'` at `q`.

## Proof of `baseChange_termMatch`

Unpack the relation to `y` and take `e` from `exists_baseChangeCentralizerEquiv_of_related`.
Specialize `BaseChangeOrbitalMatching` to `r`, `q`, `y` and the regularity hypothesis. Pass
it to `Θₙ.toMonoidHom` with `orbitalMatch_toMonoidHom`, and apply the result to `e`.

- Twisted to ordinary: given `d` at `r`, `exists_twistedGeometricMeasures_map` (module
  `Langlands.TraceFormula.BaseChangeTermPairing`) along `e` gives `d'` at `q` with
  `d'.centralizer = d.centralizer.map e` and the same rational covolume. The specialized
  matching hypothesis compares the orbital integrals.
- Ordinary to twisted: given `d'` at `q`, the same lemma along `e.symm` gives `d` at `r` with
  `d.centralizer = d'.centralizer.map e.symm`. Then `d.centralizer.map e = d'.centralizer`
  (checked on measurable sets), and the matching hypothesis applies again.

`baseChange_orbitalIntegral_eq_zero` applies `BaseChangeOrbitalVanishing` to the measure data
of `d'`.
