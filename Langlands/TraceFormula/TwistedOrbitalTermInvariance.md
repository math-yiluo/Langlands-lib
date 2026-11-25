# The orbital terms of the simple trace formula depend only on the class

Module `Langlands.TraceFormula.TwistedOrbitalTermInvariance`, namespace `Langlands.TraceFormula`.

The geometric side of the simple trace formula is a sum, over rational conjugacy classes, of terms
`vol((Γ ∩ C) \ C) · O_γ(φ)`, where `γ` is a representative of the class and `C` its centralizer. The
term is formed with a right-invariant measure on `C`, a quotient measure on `C \ G` and a quotient
measure on `(Γ ∩ C) \ C`. This module proves that it does not depend on these measures nor on the
representative, in the twisted setting of `TwistedOrbital` (`twistedCentralizer`,
`twistedOrbitalIntegral`, `IsTwistedConjugate`), and deduces the untwisted case.

## Setting

`G` is a group with a topology making it a Hausdorff, locally compact, second countable topological
group, with its Borel σ-algebra. `Γ` is a subgroup with `[DiscreteTopology Γ]`, `θ : G →* G` an
endomorphism, continuous where stated (`hθ`), and `γ ∈ G` with `C = twistedCentralizer θ γ`
(`{x | x⁻¹ γ θ(x) = γ}`). The measurable structures on the coset spaces `LeftQuotient C` and
`LeftQuotient (Γ.subgroupOf C)` are instance arguments with `BorelSpace`, as in
`GeneralLinearSimpleTraceFormulaStatement`.

An **admissible triple** at `γ` consists of `μC : Measure C` with
`[μC.IsMulRightInvariant] [IsFiniteMeasureOnCompacts μC] [μC.IsOpenPosMeasure]`, a measure
`νC` on `C \ G` with `IsCompatible C μG μC νC`, and a measure `νΓC` on `(Γ ∩ C) \ C` with
`IsCompatible (Γ.subgroupOf C) μC Measure.count νΓC`. These are exactly the measures over which
`GeneralLinearSimpleTraceFormulaStatement` quantifies.

The norm-one subgroup `G = normOneSubgroup F GLₙ` of `GL_n(𝔸_F)`, with `Γ = rationalNormOneSubgroup
F GLₙ`, `θ = MonoidHom.id _` and `μG = Measure.haar`, satisfies all hypotheses through instances that
are in scope in `GeneralLinearSimpleTraceFormulaStatement`: `normOneIsTopologicalGroup`,
`instT2SpaceSubtype`, `normOneLocallyCompactSpace`, `normOneSecondCountableTopology`,
`Subtype.borelSpace`, `rationalNormOneSubgroup_discreteTopology`, and left invariance of
`Measure.haar` (`isHaarMeasure_haarMeasure`); `continuous_id` gives `hθ`.

## Statements

- `twistedOrbitalTerm Γ θ γ νC νΓC φ : ℂ := ((νΓC Set.univ).toReal : ℂ) * twistedOrbitalIntegral θ γ νC φ`.
  For `θ = MonoidHom.id G` it is the summand `((νΓC j Set.univ).toReal : ℂ) * orbitalIntegral (r j) (νC j) fOne`
  of `GeneralLinearSimpleTraceFormulaStatement`.

- **(1) Independence of the measures.**
  `twistedOrbitalTerm_eq_of_isCompatible Γ θ hθ γ μG μC μC' hνC hνC' hνΓC hνΓC'`: for two
  admissible triples `(μC, νC, νΓC)`, `(μC', νC', νΓC')` at `γ` and any `μG : Measure G`,

  ```
  (νΓC Set.univ ≠ ⊤ ↔ νΓC' Set.univ ≠ ⊤) ∧
    (∀ φ : G → ℂ, Integrable (twistedOrbitFunction θ γ φ) νC ↔
      Integrable (twistedOrbitFunction θ γ φ) νC') ∧
    ∀ φ : G → ℂ, twistedOrbitalTerm Γ θ γ νC νΓC φ = twistedOrbitalTerm Γ θ γ νC' νΓC' φ
  ```

- **(2) Transport along conjugation.**
  `exists_isCompatible_twistedConj Γ θ γ hδ μG μC νC νΓC hνC hνΓC`: for `δ ∈ Γ`, `μG` left invariant
  and an admissible triple at `γ`, with `γ' = twistedConj θ δ γ = δ⁻¹ γ θ(δ)` (no continuity of `θ`,
  no topology hypotheses beyond a topological group with its Borel structure):

  ```
  ∃ (μC' : Measure (twistedCentralizer θ γ')) (_ : μC'.IsMulRightInvariant),
    IsFiniteMeasureOnCompacts μC' ∧ μC'.IsOpenPosMeasure ∧
    ∃ νC' νΓC', IsCompatible (twistedCentralizer θ γ') μG μC' νC' ∧
      IsCompatible (Γ.subgroupOf (twistedCentralizer θ γ')) μC' Measure.count νΓC' ∧
      νΓC' Set.univ = νΓC Set.univ ∧
      ∀ φ : G → ℂ,
        (Integrable (twistedOrbitFunction θ γ' φ) νC' ↔ Integrable (twistedOrbitFunction θ γ φ) νC) ∧
        twistedOrbitalIntegral θ γ' νC' φ = twistedOrbitalIntegral θ γ νC φ
  ```

  The triple is the image of `(μC, νC, νΓC)` under `y ↦ δ⁻¹ y δ` on `C`
  (`twistedCentralizerConj`), `C x ↦ C' δ⁻¹ x` on `C \ G` (`twistedOrbitQuotientConj`), and the
  induced map on `(Γ ∩ C) \ C` (`rationalTwistedCentralizerQuotientConj`).

- `exists_isCompatible_of_isTwistedConjugate Γ θ hγ μG μC νC νΓC hνC hνΓC`: the same conclusion
  for `hγ : IsTwistedConjugate Γ θ γ γ'` in place of `γ' = twistedConj θ δ γ` with `δ ∈ Γ`, the form
  used to merge expansions (`SimpleTraceGeometricExpansionSum`).

- **(3) The term of a class.**
  `twistedOrbitalTerm_eq_of_isTwistedConjugate Γ θ hθ hγ μG μC hνC hνΓC μC' hνC' hνΓC'`: for
  `hγ : IsTwistedConjugate Γ θ γ γ'`, `μG` left invariant, an admissible triple at `γ` and an
  admissible triple at `γ'`,

  ```
  (νΓC Set.univ ≠ ⊤ ↔ νΓC' Set.univ ≠ ⊤) ∧
    (∀ φ : G → ℂ, Integrable (twistedOrbitFunction θ γ φ) νC ↔
      Integrable (twistedOrbitFunction θ γ' φ) νC') ∧
    ∀ φ : G → ℂ, twistedOrbitalTerm Γ θ γ νC νΓC φ = twistedOrbitalTerm Γ θ γ' νC' νΓC' φ
  ```

- **Untwisted cases** (`θ = MonoidHom.id G`): `orbitalTerm_eq_of_isCompatible` (1),
  `exists_isCompatible_conj` (2, with `γ' = δ⁻¹ * γ * δ` and `orbitalIntegral`), and
  `orbitalTerm_eq_of_isConjugate` (3), whose last clause reads

  `((νΓC Set.univ).toReal : ℂ) * orbitalIntegral γ νC φ = ((νΓC' Set.univ).toReal : ℂ) * orbitalIntegral γ' νC' φ`.

No hypothesis on `θ Γ` is needed: the conjugator `δ` lies in `Γ`, and for every endomorphism `θ`
conjugation by `δ` maps `twistedCentralizer θ γ` onto `twistedCentralizer θ (δ⁻¹ γ θ(δ))`.

## Proofs

(1) `C` is closed (`isClosed_twistedCentralizer`), hence locally compact and second countable, and
`Γ ∩ C` is discrete in `C` (`discreteTopology_subgroupOf`), hence closed, with counting measure
finite on compacts and positive on open sets. By `exists_eq_smul_of_isMulRightInvariant`,
`μC' = c • μC` with `c : ℝ≥0`, `c ≠ 0`. `IsCompatible.smul_eq_smul` (`QuotientCompatibleScaling`)
applied on `C \ G` with fixed ambient measure gives `c • νC' = νC`, and applied on `(Γ ∩ C) \ C` with
fixed subgroup measure `count` and ambient measures `μC`, `c • μC` gives `νΓC' = c • νΓC`. Hence
`vol' = c · vol`, integrability for `νC = c • νC'` is integrability for `νC'`
(`integrable_smul_measure`), `O_γ(φ; νC) = c · O_γ(φ; νC')` (`twistedOrbitalIntegral_smul_measure`),
and the two terms are `vol · c · O_γ(φ; νC')`.

(2) The instance arguments are replaced by the Borel σ-algebras (`BorelSpace.measurable_eq`), the
form of the Library's transport lemmas. Then `isCompatible_map_twistedConj` (left invariance of
`μG`) gives the compatibility on `C' \ G`, `isCompatible_map_equiv` with the restriction
`rationalTwistedCentralizerConj` of the conjugation to `Γ ∩ C → Γ ∩ C'` gives the compatibility on
`(Γ ∩ C') \ C'` (counting measure is carried to counting measure, `map_count_measurableEquiv`),
the volume is unchanged because the quotient map is a bijection, and
`twistedOrbitalIntegral_map_conj` gives integrability and the orbital integral. This repeats the
construction of the Library's `twistedGeometricConjugation`, adding the integrability clause and
arbitrary Borel instances.

(3) Write `γ' = δ⁻¹ γ θ(δ)` with `δ ∈ Γ`, transport the triple at `γ` to `γ'` by (2)
(`exists_isCompatible_of_isTwistedConjugate`), and compare the transported triple with the given one
at `γ'` by (1).

## Declarations, in order

- `twistedOrbitalTerm`
- `discreteTopology_subgroupOf`
- `twistedOrbitalTerm_eq_of_isCompatible` (1)
- `twistedCentralizerConj_mem_subgroupOf_iff`, `rationalTwistedCentralizerConj`,
  `rationalTwistedCentralizerQuotientConj`, `map_count_measurableEquiv`
- `exists_isCompatible_twistedConj` (2), `exists_isCompatible_of_isTwistedConjugate` (2, for a
  conjugacy), `exists_isCompatible_conj` (2, untwisted)
- `twistedOrbitalTerm_eq_of_isTwistedConjugate` (3)
- `orbitalTerm_eq_of_isCompatible` (1, untwisted), `orbitalTerm_eq_of_isConjugate` (3, untwisted)

## Literature

- Getz–Hahn, *An introduction to automorphic representations* (2024), §18.4, Corollary 18.4.1 and
  the paragraph after it (printed p. 485): the geometric side of the simple trace formula is a sum
  over elliptic semisimple conjugacy classes `[γ]` of `τ(C_γ) O_γ(f)`; one Haar measure `dg'_γ` on
  `A_G \ C_γ(𝔸_F)` is chosen for each `γ` and used both for the volume `τ(C_γ)` and, through the
  quotient by the fixed Haar measure of the group, for the orbital integral. That the summand is a
  function of the class, and that it does not depend on `dg'_γ`, is implicit there; this module
  proves both.
- Getz–Hahn, §17.8, Theorem 17.8.7 and the remark after it (printed pp. 466–467), and its proof
  (printed pp. 467–469): unfolding over the rational classes `[γ]`, the integral over
  `AH_γ(F) \ H(𝔸_F)` is written as `meas_{dh_γ}(AH_γ(F) \ H_γ(𝔸_F))` times the integral over
  `H_γ(𝔸_F) \ H(𝔸_F)` with the quotient measure `dh/dh_γ` ((17.65), printed p. 468), "the same
  measure `dh_γ`" being used in both factors. The term is thus formed from a quantity that involves
  neither the representative nor `dh_γ`, which is the content of (1) and (3).
- Getz–Hahn, §18.2, (18.14) and Theorem 18.2.5 (printed p. 479): the same convention in the general
  simple relative trace formula.
- Arthur–Clozel, *Simple algebras, base change, and the advanced theory of the trace formula* (1989),
  Chapter 1, §4, (4.4) and (4.5) (printed pp. 43–44): the Deligne–Kazhdan simple trace formula with
  the geometric side indexed by `σ`-conjugacy classes `{δ}` and by conjugacy classes `{γ}`, with the
  Tamagawa measures; the twisted form corresponds to the twisted case here.
