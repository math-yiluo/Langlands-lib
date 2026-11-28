# Remarks on supercuspidal representations (Renard VI.2.1): proof

Module `Langlands.Representation.CuspidalSupport.SupercuspidalRemarksProof`.
Namespace `Langlands.Aubert.General.RepresentedParabolic`. Universe parameters `u, v`.

`supercuspidalRemarks : SupercuspidalRemarksStatements.{u, v}` proves exactly the
statement of module `Langlands.Representation.CuspidalSupport.SupercuspidalRemarksStatements`
at its universes `u, v`, with no hypotheses.
[Statement](SupercuspidalRemarksStatements.md)

## What is proved

In the represented setting of the statement (a nonarchimedean local field `k` with
`T2Space`, a connected reductive group scheme `G` over `Spec k`, the canonical topology
`RationalPointFamily.pointTopology` on `G(F) = rationalPoints G`, and the
`LocallyCompactSpace` and `NonarchimedeanGroup` binders), with `Z` the centre of `G(F)`
and `IsSupercuspidal` the represented supercuspidality predicate, for complex smooth
representations:

1. every subquotient of a supercuspidal representation is supercuspidal;
2. if `Z` is compact, `A` is supercuspidal if and only if all its coefficients against
   smooth vectors of the dual have compact support
   (`HasCompactSmoothDualCoefficients A.representation`);
3. `A` is supercuspidal if and only if, for every compact open subgroup `K` and every
   `w ∈ A`, there is a compact `C` such that for every `K`-invariant linear form `ℓ` the
   support of `g ↦ ℓ(A(g⁻¹) w)` lies in `C Z`. This is the condition that the function
   `f_{K,w}` of Renard IV.1.3 has support compact modulo `Z`.

## Proof

The Lean term is one application:

```
supercuspidalRemarksReduction
  Langlands.BruhatTits.SpecialCompact.jointSpecialCompactBasisExistence
```

- `supercuspidalRemarksReduction`
  (`Langlands.Representation.CuspidalSupport.SupercuspidalRemarksReduction`) proves
  `JointSpecialCompactBasisExistenceStatement.{u} → SupercuspidalRemarksStatements.{u, v}`.
  [Reduction](SupercuspidalRemarksReduction.md)
- `Langlands.BruhatTits.SpecialCompact.jointSpecialCompactBasisExistence`
  (`Langlands.BruhatTits.SpecialCompact.JointBasisProof`) proves
  `JointSpecialCompactBasisExistenceStatement.{u}` (Renard V.5.1–V.5.2 at one special
  vertex of a Bruhat–Tits apartment) for every nonarchimedean local field in universe `u`.
  [Joint basis](../../BruhatTits/SpecialCompact/JointBasisProof.md)

The universe of the field matches: both are at `u`, and the representation universe `v`
appears only in the reduction's conclusion.

### The argument inside the reduction

For the reader's orientation, the proof of `supercuspidalRemarksReduction` runs as
follows (its Markdown gives the details). Write `H = ⁰G`, the common kernel of the norms of
the rational characters, an open normal subgroup of `G(F)`.

- The first remark is `IsSupercuspidal.of_isSubquotient` and does not use the joint
  basis statement.
- The represented VI.2.1 equivalence "supercuspidal ⇔ coefficients compactly supported
  on `H`" is used in both directions: `isSupercuspidal_of_compactRestriction`
  (compact on `H` ⇒ supercuspidal) and `compactRestriction_of_isSupercuspidal`
  (supercuspidal ⇒ compact on `H`). The second is the one place where the joint basis
  statement, here `jointSpecialCompactBasisExistence`, enters.
- For the second remark, compact support on `G(F)` restricts to the open subgroup `H`;
  conversely, compact support on `H` gives support in `C Z` for the `f_{K,w}`
  (`support_subset_mul_center_of_comp`, using that `H Z` has finite index), and
  compactness of `Z` turns this into compact support on `G(F)`
  (`hasCompactSmoothDualCoefficients_of_support_of_isCompact_center`).
- For the third remark, the forward direction is `support_subset_mul_center_of_comp`
  again; the backward direction uses that `H ∩ Z` is compact
  (`hasCompactSmoothDualCoefficients_comp_of_support`) and then the implication
  compact on `H` ⇒ supercuspidal. This follows Renard's hint: adapt the proof of IV.1.3,
  using that `⁰G Z` has finite index in `G` and `⁰G ∩ Z` is compact.

## Axioms

The theorem depends only on `propext`, `Classical.choice` and `Quot.sound`.

## Provenance

The statement formalizes the remarks of David Renard, *Représentations des groupes
réductifs p-adiques* (French edition dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`), VI.2.1, printed
pp.137–139 / PDF pp.143–145; the statement's Markdown quotes the source text. This proof is
an internal composition of the two Library theorems named above.

## Imports

| Module | Used for |
| --- | --- |
| `Langlands.Representation.CuspidalSupport.SupercuspidalRemarksReduction` | `supercuspidalRemarksReduction`, and the target `SupercuspidalRemarksStatements` (transitively) |
| `Langlands.BruhatTits.SpecialCompact.JointBasisProof` | `jointSpecialCompactBasisExistence` |
