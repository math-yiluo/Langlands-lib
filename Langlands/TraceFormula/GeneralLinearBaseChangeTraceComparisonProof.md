# Comparison of the simple trace formula for `GL_n` with its twisted form (proof)

Module `Langlands.TraceFormula.GeneralLinearBaseChangeTraceComparisonProof`, namespace
`Langlands.TraceFormula`.

`generalLinearBaseChangeTraceComparison : GeneralLinearBaseChangeTraceComparisonStatement.{u}`
proves the published statement with its universe parameter free and no added hypothesis. The
statement is in module `Langlands.TraceFormula.GeneralLinearBaseChangeTraceComparisonStatement`,
whose page describes the data, the two hypotheses (matching at norms, vanishing off norms) and
the conclusion `tr (R(φ) ∘ I_θ) = c · tr R(f)`. The module repeats the statement module's local
`IsAffine` and `Smooth` instances for `GLₙ` and its local notations `GLₙ`, `Wₙ`,
`Θₙ = normOneAut K (unitGaloisAut K L GLₙ σ)`.

The proof follows the comparison of the twisted and untwisted simple trace formulas in
Arthur–Clozel, *Simple algebras, base change, and the advanced theory of the trace formula*,
Chapter 1, §4, (4.4)–(4.6), and Henniart–Lemaire, *Changement de base et induction automorphe
pour GL_n en caractéristique non nulle*, II.6.6. Both geometric sides are finite sums over
regular elliptic classes. The norm relation pairs the corresponding terms, and paired terms
are equal up to `c`. Unpaired twisted terms vanish, and unpaired ordinary terms vanish after
multiplication by `c`.

## Supporting modules

- `Langlands.TraceFormula.BaseChangeTermPairing`: the abstract pairing theorem
  `geometricExpansion_eq_mul_of_termPairing_continuousMulEquiv`, the matching propositions
  `TwistedTermMatchesOrdinaryTerm` and `OrdinaryTermMatchesTwistedTerm`, and transport of
  geometric measure data along centralizer isomorphisms (`exists_twistedGeometricMeasures_map`).
- `Langlands.TraceFormula.GeneralLinearBaseChangeNormPairing`: matrix coordinates of rational
  norm-one points, the relation `BaseChangeNormRelated` (the statement's
  `Φ(N(r)) · rational(y) = rational(y) · ΦG(q)` for some `y ∈ GL_n(L)`), and its properties from
  `cyclicNormLemma`.
- `Langlands.TraceFormula.GeneralLinearBaseChangeCentralizerEquiv`: the topological group
  isomorphism of the `θ`-centralizer of `r` with the centralizer of a related `q`
  (`exists_baseChangeCentralizerEquiv`).
- `Langlands.TraceFormula.GeneralLinearBaseChangeTermMatching`: the hypotheses of the
  statement as `BaseChangeOrbitalMatching` and `BaseChangeOrbitalVanishing`, and their
  consequences `baseChange_termMatch` and `baseChange_orbitalIntegral_eq_zero`.

## Proof of `generalLinearBaseChangeTraceComparison`

The private lemma `baseChangeGeometricExpansion_toMonoidHom` restates the geometric side of
the simple twisted trace formula, written with a topological group automorphism `θ`, as
`SimpleTraceGeometricExpansion R θ.toMonoidHom μH f t r`. The two forms are definitionally
equal.

1. **The two trace formulas.** After introducing the data and hypotheses, the theorem
   `generalLinearSimpleTwistedTraceFormula` (module
   `Langlands.TraceFormula.GeneralLinearSimpleTwistedTraceFormulaProof`) is applied to the
   `Wₙ` data, `φ₁`, `φ₂` and the place `w`. It gives `hΘ`, `hΘμ`, integrability `hφ`, trace
   class, and a family `r : Fin m → rationalNormOneSubgroup K Wₙ` with four properties:
   pairwise non-twisted-conjugate under the rational subgroup, regular elliptic norms at `w`,
   covering every rational point whose twisted orbit meets the nonzero locus of `φ¹`, and the
   geometric expansion of `tr (R(φ) ∘ I_θ)`. Likewise `generalLinearSimpleTraceFormula`
   (module `Langlands.TraceFormula.GeneralLinearSimpleTraceFormulaProof`) is applied to the
   `GLₙ` data, `f₁`, `f₂` and `v`. It gives `hf`, trace class and
   `q : Fin m' → rationalNormOneSubgroup K GLₙ` with the corresponding properties for `f¹` and
   `tr R(f)`. The witnesses `hΘ, hΘμ, hφ, hf` and the two trace-class assertions are the first
   six components of the conclusion. The trace identity remains.
2. **Bundled expansions.** `baseChangeGeometricExpansion_toMonoidHom` puts the twisted
   expansion in the form `SimpleTraceGeometricExpansion` for `Θₙ.toMonoidHom`. The
   untwisted expansion already has that form with `MonoidHom.id`. `bundledGeometricTraceSum`
   (module `Langlands.TraceFormula.SingleOrbitSimpleTrace`) then gives
   `tr (R(φ) ∘ I_θ) = ∑ j, (d j).term φ¹` for every family `d` of
   `TwistedGeometricMeasures` at the `r j`. It likewise gives `tr R(f) = ∑ k, (d' k).term f¹`
   for every family `d'` at the `q k`.
3. **Regularity predicates and measure data.** Let `regW x` say that the component at `w` of
   `Φ(N(x))` is regular elliptic, and `regG y` that the component at `v` of the coordinate of
   `y` is regular elliptic. The trace formulas give `regW (r j)` and `regG (q k)`. Measure data
   exist at every `r j` by `nonempty_twistedGeometricMeasures_baseChange`. They exist at every
   `q k` by `nonempty_twistedGeometricMeasures_of_commutative` with
   `isDiscrete_rationalNormOneSubgroup` and `generalLinearRegularCentralizerCommutative`
   (module `Langlands.TraceFormula.AdelicRegularCentralizer`).
4. **Matching and vanishing.** The statement's matching hypothesis is
   `BaseChangeOrbitalMatching σ l n w v φ¹ f¹ c` by definition, and `baseChange_termMatch`
   turns it into `TwistedTermMatchesOrdinaryTerm` and `OrdinaryTermMatchesTwistedTerm` at
   every related pair `(x, y)` with `regW x ∨ regG y`. The statement's vanishing hypothesis is
   `BaseChangeOrbitalVanishing σ l n v f¹`. By `baseChange_orbitalIntegral_eq_zero`, it makes
   the orbital integrals of `f¹` vanish at rational `y` with `regG y` related to no rational
   point of `Wₙ`.
5. **Pairing.** `geometricExpansion_eq_mul_of_termPairing_continuousMulEquiv` is applied with
   `RW = rationalNormOneSubgroup K Wₙ`, `RG = rationalNormOneSubgroup K GLₙ`, `θ = Θₙ`, the Haar
   measures, `φ¹`, `f¹`, `c`, the relation `A x y = BaseChangeNormRelated σ l x y`, `regW`,
   `regG`, `r` and `q`. Its hypotheses are supplied by steps 1–4 and by the relation
   properties of `Langlands.TraceFormula.GeneralLinearBaseChangeNormPairing`:
   - `exists_baseChangeNormRelated`: every rational `x` is related to some `y`;
   - `baseChangeNormRelated_of_twistedConj_left` and `baseChangeNormRelated_of_conj_right`:
     invariance under rational (twisted) conjugation;
   - `isTwistedConjugate_of_baseChangeNormRelated` and `isConjugate_of_baseChangeNormRelated`:
     uniqueness of classes.

   The conclusion is `tr (R(φ) ∘ I_θ) = c · tr R(f)`, for every `c`, including `c = 0`.

The main theorem is elaborated with `maxHeartbeats 24000000` and `maxRecDepth 4000`. It also
sets `backward.isDefEq.respectTransparency.types false`, the option under which the Library
proves `bundledGeometricTraceSum`.
