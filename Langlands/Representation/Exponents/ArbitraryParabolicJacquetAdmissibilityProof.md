# Admissibility of the actual normalized Jacquet module: proof

Author: Worker 4776. Module
`Langlands.Representation.Exponents.ArbitraryParabolicJacquetAdmissibilityProof`.

The theorem
`Langlands.Aubert.General.RepresentedParabolic.arbitraryParabolicJacquetAdmissibility`
has as its whole type the published proposition
[`ArbitraryParabolicJacquetAdmissibilityStatement.{u, v}`](ArbitraryParabolicJacquetAdmissibilityStatement.md).
The field universe `u` and the representation-carrier universe `v` stay
independent. The statement is Renard 2026, VI.6.1 Corollary, normalized clause
(printed pp.176–177 / PDF pp.182–183), stated for every represented parabolic.
The paired statement Markdown explains how the statement corresponds to the
source.

## Statement proved

Fix a nonarchimedean local field `k` with
`[Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
[T2Space k]`. Fix a connected reductive `G` over `k`, and give `rationalPoints G`
the canonical topology `RationalPointFamily.pointTopology`, together with the
instances `[LocallyCompactSpace (rationalPoints G)]` and
`[NonarchimedeanGroup (rationalPoints G)]`. Take any data
`p : P ⟶ G`, `l : M ⟶ P`, `r : U ⟶ P` with `hp : IsParabolicSubgroup p`,
`hl : IsRationalLeviSubgroup l`,
`hr : LeviSubgroup.IsGeometricUnipotentRadical r` and
`hmul : IsIso (subgroupMultiplication l r)`. Then for every admissible
`π : SmoothRep.{0, u, v} ℂ (rationalPoints G)` the object
`(jacquetFunctor p l r hp hr hl hmul).obj π` is admissible. Its carrier is the
actual coinvariant quotient by the literal radical point image
`pointImage (r ≫ p)`. The literal Levi point image `pointImage (l ≫ p)` acts on
it, twisted by `HaarModulus.closedInverseHalfCharacter`.

The proof adds no hypothesis. It assumes no contraction basis, simultaneous
basis, standard cocharacter, finite length, finite generation or target
admissibility, and it changes no construction.

## Implemented proof

The proof is a single term that composes three published Library results:

```lean
arbitraryParabolicJacquetAdmissibility_of_dynamic parabolicDynamic
  dynamicGeometricUnipotentRadical
```

1. `arbitraryParabolicJacquetAdmissibility_of_dynamic` (module
   [`ArbitraryParabolicJacquetAdmissibilityReduction`](ArbitraryParabolicJacquetAdmissibilityReduction.md))
   proves the published implication
   `ArbitraryParabolicJacquetAdmissibilityReductionStatement.{u, v}`, namely
   `ParabolicDynamicStatement.{u} → DynamicGeometricUnipotentRadicalStatement.{u} →
   ArbitraryParabolicJacquetAdmissibilityStatement.{u, v}`.
2. `Langlands.GroupScheme.parabolicDynamic` (module
   [`GroupScheme.Absolute.ParabolicDynamicProof`](../../GroupScheme/Absolute/ParabolicDynamicProof.md))
   proves `ParabolicDynamicStatement.{u}` (Milne, Theorem 25.1) for every field
   and every connected reductive group. A closed subgroup is parabolic exactly
   when its range is `Dynamic.parabolic χ` for a cocharacter `χ` defined over
   `k`.
3. `Langlands.GroupScheme.dynamicGeometricUnipotentRadical` (module
   [`GroupScheme.Dynamic.GeometricUnipotentRadicalProof`](../../GroupScheme/Dynamic/GeometricUnipotentRadicalProof.md))
   proves `DynamicGeometricUnipotentRadicalStatement.{u}`. For every field and
   every connected reductive group, a representative of the dynamic unipotent
   subgroup `Dynamic.unipotent χ` is the geometric unipotent radical of a
   representative of `Dynamic.parabolic χ`.

Both structural inputs are taken at the field universe `u` of the target, as
the reduction requires. Applying the reduction to them yields the target
proposition with every quantifier unchanged.

The imported reduction proceeds as follows. These steps are already published
and are not reproved here.

- `DynamicLeviConjugacy.exists_cocharacter_parabolic_levi` uses the two
  structural theorems to find one cocharacter `χ` over `k`. The range of `p` is
  `Dynamic.parabolic χ`, and the range of `l ≫ p` is `Dynamic.centralizer χ`.
- `pointImage_radical_eq_dynamic` shows that the literal point image of the
  supplied radical `r ≫ p` equals the rational points of `Dynamic.unipotent χ`.
  The literal Levi image equals the rational points of `Dynamic.centralizer χ`.
- `RationalPointFamily.dynamic_hasOppositeIwahoriContractionBasis` gives an
  ambient-cofinal opposite Iwahori contraction basis for the dynamic radical,
  the dynamic centralizer and the opposite dynamic radical
  `Dynamic.unipotent (Dynamic.inverseCocharacter χ)`, in the canonical topology.
  It uses a Levi-central contracting point and the rational open-cell
  neighbourhood theorem.
  `HasOppositeIwahoriContractionBasis.hasIwahoriContractionBasis` turns this
  into `Jacquet.HasIwahoriContractionBasis` for the subgroup topology on the
  Levi.
- After rewriting along the two point-image equalities, the generic theorem
  `isAdmissible_normalizedJacquetFunctor_obj_of_iwahoriContraction` (module
  [`Aubert.General.JacquetAdmissibility`](../Aubert/General/JacquetAdmissibility.md))
  proves that the actual normalized Jacquet object is admissible. This is the
  weak-Jacquet-lemma argument of Renard's proof on printed p.177 / PDF p.183.
  Admissibility is unaffected by the twist by the inverse half Haar modulus,
  because that character has open kernel.

So the contraction-basis premise of the generic admissibility theorem is
discharged, for the actual displayed data, by published structural theorems. It
is not assumed.

## Provenance and scope

This module adds no mathematics beyond the composition. It changes neither the
target pair nor anything the target imports. The reduction is by Worker 1218.
The proof of `ParabolicDynamicStatement` was published by task
`42c85926-0d43-4d0d-abef-f3350c4273ae`, credited to Worker 3813 with
Worker 4153. The geometric-radical proof is by Worker 1281. The theorem uses
only the axioms `propext`, `Classical.choice` and `Quot.sound`.

The module proves only the normalized clause of VI.6.1 Corollary, which is the
whole of the target proposition. It does not prove the unnormalized clause,
quotient compactness, Jacquet finite length, Casselman's criterion or the VII.2
results.
