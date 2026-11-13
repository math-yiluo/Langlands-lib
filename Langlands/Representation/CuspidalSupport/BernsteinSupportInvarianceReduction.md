# Renard VI.5.4 for the standard family, from represented VI.5.4

Worker 117. This is a derived conditional reduction for Renard, *Représentations des
groupes réductifs p-adiques*, French version dated 9 July 2026
(`renard-2026-representations-groupes-reductifs-padiques`), VI.5.4, Theorem
(printed pp.173–175 / PDF pp.179–181). It moves the theorem from the
represented-parabolic framework to the standard Bernstein family.

## Statement

`BernsteinAssociatedSupportInvarianceReductionStatement.{uF, uV}` is the implication

> `RepresentedParabolic.LeviSupercuspidalInductionAssociationStatement.{uF, max uF uV}` →
> (for all `F, G, T, i, ν`, the topology `pointTopology` on `G(F)`, instances
> `LocallyCompactSpace G(F)`, `NonarchimedeanGroup G(F)` and every standard family
> `family`: `BernsteinAssociatedSupportInvarianceStatement.{uF, uV} i ν family`).

Both statements are published and unchanged:

- `RepresentedParabolic.LeviSupercuspidalInductionAssociationStatement`
  (`Langlands/Representation/Exponents/LeviSupercuspidalInductionAssociationStatement.lean`)
  states VI.5.4 without the numerical bounds. It applies to rational parabolics
  `P = MN`, `P' = M'N'` and irreducible supercuspidal `ρ`, `ρ'`. Under these
  hypotheses, `i_P^G ρ` has a finite composition series, and four conditions are
  equivalent:
  1. association: a point `g` and an isomorphism `φ : M ≅ M'` conjugating the
     embeddings, together with a linear equivalence `ρ ≃ ρ'` intertwining `ρ(m)` with
     `ρ'(φ m)`;
  2. a nonzero intertwiner;
  3. equal Jordan–Hölder factors;
  4. a common irreducible subquotient.

  It is used with carriers in `Type (max uF uV)`, the carrier universe of the
  standard Bernstein data.
- `BernsteinAssociatedSupportInvarianceStatement i ν family`
  (`Langlands/Representation/CuspidalSupport/BernsteinSupportComparison.lean`)
  is VI.5.4 for the standard family. If two cuspidal data `a`, `b` are associated
  (`AreBernsteinCuspidalDataAssociated`: a rational Levi conjugacy `c` and an
  isomorphism `ρ_a ≅ c^* ρ_b`), then every `π` is an irreducible subquotient of
  `bernsteinInduction a` if and only if it is one of `bernsteinInduction b`. The
  published definition has `F, G, T, i, ν, family` as section variables, so the
  conclusion quantifies over them. It is quantified exactly as the support-invariance
  premise of `BernsteinCenterFunctionsReductionStatement`.

`bernsteinAssociatedSupportInvariance_reduction` proves the implication. The
per-family form is `bernsteinAssociatedSupportInvariance_of_represented`.

## Provenance

The statement is internal: it is an implication between two published forms of the
same theorem, VI.5.4. It isolates the transfer from the represented-parabolic
framework (arbitrary rational parabolics with geometric unipotent radicals) to the
standard Bernstein family. The transfer is needed because the conditional reduction
of VI.10.4, Theorem (second sentence), `BernsteinCenterFunctionsReductionStatement`,
assumes the standard-family form. No proof task covers that form, whereas the
represented form is already the target of a proof task.

## Proof

1. `representedSubquotient_of_associated` (private, general rational parabolics).
   Represented VI.5.4 for `(ρ, ρ')` and for `(ρ', ρ)` gives finite composition
   series of both inductions. Under the association witness, its equivalence
   (condition 1 ⇒ condition 3, `List.TFAE` indices 1 and 3) gives equal
   Jordan–Hölder factors. The Library lemma
   `Classification.HeadDetectingCount.isSubquotient_of_haveSameJordanHolderFactors`
   then transfers irreducible subquotients across. It is used together with
   `LengthCriterionProof.isFiniteLength_of_hasCompositionSeriesLength` and with
   `haveSameJordanHolderFactors_symm` for the converse direction. The result is
   an iff for each irreducible `σ`.
2. `exists_pointwiseIntertwiner_of_pullbackIso` (private, abstract topological
   groups). An isomorphism `ρ ≅ e^* ρ'` gives, through `SmoothRep.equivOfIso`, a
   linear equivalence `ρ ≃ ρ'` that intertwines `ρ(m)` with `ρ'(e m)`. Proving this
   over abstract groups and then instantiating it avoids a kernel timeout on the
   concrete Levi point groups.
3. `bernsteinStandardWitness_of_association` (private). A rational Levi conjugacy
   `c` together with `ρ ≅ rationalIsoPullback c.iso ρ'` gives the represented
   association witness. The point is `c.point` and the isomorphism is `c.iso`; the
   commutation follows from `c.commutes` and `Standard.leviToParabolic_comp`. The
   linear equivalence comes from step 2 with `e = rationalPointIso c.iso`, which is
   `rationalPoints.map c.iso.hom` by definition.
4. `bernsteinStandardSubquotient_iff_of_witness` (private). Step 1 is specialised to
   the standard parabolics of `I` and `J`, with the geometric facts
   `bernsteinStandardRepresentativesGeometric`, and stated for
   `bernsteinStandardRepresentedInductionFunctor`. This uses the same unfolding of
   the topologies as `BernsteinSupportAssociationReduction`.
5. `bernsteinAssociatedSupportInvariance_of_represented` (per family). The data `a`
   and `b` are supercuspidal (`BernsteinCuspidalDatum.isSupercuspidal`) and
   irreducible. Steps 3 and 4 identify the irreducible subquotients of the two
   represented inductions. `bernsteinRepresentedInductionIso` with
   `IsSubquotient.of_iso_right` transfers them to and from `bernsteinInduction`, in
   both directions.
6. `bernsteinAssociatedSupportInvariance_reduction` applies step 5 to every family.

## Qualifications

- This is conditional: represented VI.5.4 remains an explicit premise.
- Only the implication "association ⇒ equal Jordan–Hölder factors" is used from
  VI.5.4, together with finite length of both inductions.
