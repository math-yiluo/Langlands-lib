# The two remaining inputs of actual rational cuspidal factor extraction

Worker 4358 authored this internal supporting unit for the proof task
`e6add7c5-44c5-45ea-afe9-7f48c98fb927` of
`RationalCuspidalJacquetFactorExtractionStatement`
([RationalCuspidalJacquetFactorTarget](RationalCuspidalJacquetFactorTarget.md)).
It names two Prop-valued inputs and proves that together they imply the
extraction target. It proves neither input, so it does **not** prove
`RationalCuspidalJacquetFactorExtractionStatement`.

Module `Langlands.Representation.Aubert.General.RationalCuspidalExtractionInputs`,
namespace `Langlands.Aubert.General.RationalPointFamily`.

## Setting

The section variables are those of the published helpers
[RationalCuspidalGeometricExtraction](RationalCuspidalGeometricExtraction.md) and
[RationalProperTargetGeometricTerm](RationalProperTargetGeometricTerm.md): a field
`k : Type u` with a topology, a group scheme `G` over `Spec k` with affine
structure map, a monomorphism `i : T ⟶ G` from a commutative group scheme, a
cocharacter `ν` with finitely many simple roots `SimpleRoot i ν`, the canonical
`pointTopology` on `G(k)` with `LocallyCompactSpace` and `NonarchimedeanGroup`,
the comparisons `hN`, `hZ`, the statements `hStandard`, `hInter`, and
`hG : IsConnectedReductive G`, `hi : IsMaximalSplitTorus i`,
`hν : IsGenericCocharacter i ν`, with closed standard Levis (`hM`) and closed
standard radicals (`hU`). `i_I` is the published `normalizedInductionFunctor`
and `r_J` the published `jacquetFunctor` of the standard semidirect
decompositions given by `isSemidirectDecomposition_of_standardCocharacterStatement`.

## The two inputs

`PointInducedJacquetGeometricFiltration cs` (input (G), Renard VI.5.1). For a
supplied actual point Coxeter system `cs : ActualCoxeterSystem (torusPoints i) C`:
for all simple-root subsets `I`, `J` and every smooth complex representation
`σ` of `levi i ν I` with carrier universe `max (u + 1) v`, the actual object
`r_J (i_I σ)` has a finite filtration `s : ObjectRepFiltration _ r`, with
zero bottom and full top, such that each graded object
`s.smoothGradedObject q` is actually isomorphic to
`(geometricTermFunctor … J I n hs ht).obj σ`. Here `w : Weyl i` is a minimal
representative (`IsMinimal cs J I w`), `n` is a normalizer point with
`QuotientGroup.mk n = w`, and `hs`, `ht` are source and target decompositions.
All of these may depend on `q`. The input does not require one grade for
each double coset or distinct representatives.

`PointLeviStandardInductionCuspidalExclusion` (input (E), Renard VI.5.2
inside each standard Levi). For every `J` and every proper subset
`K ≠ Finset.univ` of `J`, every smooth representation `ρ` of the fine Levi
`(levi i ν (leviIndex J K)).subgroupOf (levi i ν J)`, and every irreducible
`τ` on `levi i ν J` satisfying the inside-Levi `IsLeviCuspidal`, `τ` is not an
actual `SmoothRep.IsSubquotient` of the normalized induction of `ρ` inside
`levi i ν J`. The induction uses `isSemidirectDecomposition_in_levi` and the
restricted closedness of the fine radical. `ρ` is arbitrary: no
irreducibility, cuspidality or finiteness condition.

## The implication at one datum

`inducedCuspidalJacquetFactorExtraction_of_filtration_exclusion` assumes
`hRoots : HasRelativeRootSystem i`, one Coxeter system `cs` with
`RootLengthComparison i ν hN hZ cs` and input (G) for `cs`, and input (E). It
concludes `InducedCuspidalJacquetFactorExtractionTarget` of
[CuspidalJacquetFactorReduction](CuspidalJacquetFactorReduction.md) for the
standard families, with `IsAssociate := rootAssociation i ν hN hZ`.
The proof is a composition of published theorems:

1. `positiveSimpleReflectionComparison_of_rootLength`
   ([RationalSuppliedCoxeterComparisons](RationalSuppliedCoxeterComparisons.md))
   turns the root-length comparison into the positive simple-reflection
   comparison, using `hi.isSplitSubtorus.1`, `hRoots` and `hν`.
2. `pointCuspidalExtractionGeometry_of_rootComparisons`
   ([RationalCuspidalExtractionGeometry](RationalCuspidalExtractionGeometry.md))
   proves `PointCuspidalExtractionGeometry` from the two comparisons.
3. `pointProperTargetGeometricTermExclusion_of_standardInduction`
   ([RationalProperTargetGeometricTerm](RationalProperTargetGeometricTerm.md))
   turns input (E) into `PointProperTargetGeometricTermExclusion`, using the
   source intersection identities from step 2.
4. For `I`, `J`, `σ`, `τ` and the subquotient hypothesis `τ ⊆ r_J i_I σ`,
   input (G) gives a filtration of `r_J i_I σ` with geometric grades, and
   `pointCuspidalJacquetFactor_of_geometricFiltration`
   ([RationalCuspidalGeometricExtraction](RationalCuspidalGeometricExtraction.md))
   returns the rational point `n`, its membership witness, the root
   association and the actual isomorphism `τ ≅ (conjugationFunctor n hn).obj σ`.
   All three come from the same `n` and `hn`.

## The closed input statement and the final implication

`RationalCuspidalExtractionInputsStatement.{u, v}` has exactly the binders of
`RationalCuspidalJacquetFactorExtractionStatement.{u, v}`: every
nonarchimedean local field `k : Type u` (any characteristic), every connected
reductive `G` with maximal split torus `i`, `pointTopology` with
`LocallyCompactSpace`, `NonarchimedeanGroup` and `T2Space`, every generic `ν`,
and the premises `hStandard`, `hInter`, `hRoots`, `hN`, `hZ`, `hU`, `hM`, with
the enumeration `simpleRelativeRootFintype`. Its conclusion is the conjunction
of input (G) for some Coxeter system with the root-length comparison and
input (E).

`rationalCuspidalJacquetFactorExtraction_of_inputs` proves
`RationalCuspidalExtractionInputsStatement.{u, v} →
RationalCuspidalJacquetFactorExtractionStatement.{u, v}`. It rewrites the
target with the published equivalence
`rationalCuspidalJacquetFactorExtractionStatement_iff_induced`
([CuspidalJacquetFactorReduction](CuspidalJacquetFactorReduction.md)), which
uses actual Jacquet exactness to move from an arbitrary smooth subquotient `π`
of `i_I σ` to the whole induced object. It then introduces the binders as the
target does and applies the previous theorem.

The implication adds no premise to the target. The universes `u` and `v` are
independent, carriers have universe `max (u + 1) v`, and empty simple-root
sets and relative rank zero are included. No finite-length, admissibility,
finite-generation, compactness or endpoint hypothesis occurs. Neither input
contains a classification, adjointness or K0 statement. The axioms used are
`propext`, `Classical.choice` and `Quot.sound`.

## Provenance and remaining obligations

This is a derived (internal) unit. It follows the route of Renard,
*Représentations des groupes réductifs p-adiques*, French edition dated
9 July 2026 (`renard-2026-representations-groupes-reductifs-padiques`,
SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`):
Proposition VI.5.3(ii),(iii), printed p.173 / PDF p.179, and the first proof
paragraph of Théorème VI.5.4, printed p.174 / PDF p.180. Input (G) is the
geometric lemma VI.5.1 (printed pp.161–164 / PDF pp.167–170) for the
actual standard families, in the normalized-grade form the published
extraction helper consumes. Input (E) is Lemme VI.5.2 (printed p.173 /
PDF p.179) inside each standard Levi.

Both inputs remain unproved in the Library. Input (G) needs an ordered
orbit cover of the double cosets and the identification of the
Mackey-orbit coinvariant grades of the published
[ParabolicSupportFiltration](ParabolicSupportFiltration.md) with
`geometricTermFunctor`. Input (E) needs Renard's compactness argument for
cuspidal representations over `ℂ` (VI.2.1, VI.3.4–VI.3.5), or some other
proof. It fails for coefficients of positive characteristic, where cuspidal
representations need not be supercuspidal.
