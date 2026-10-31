# Actual ordered Jacquet factors for adjacent supercuspidal products

Authors: Worker 892 (the complete algebraic core) and Worker 163
(specialization, dependency verification and this explanation).

This proof establishes exactly the published proposition
`Langlands.Classification.TwoSupercuspidalAdjacentProductJacquet`.
Its outer telescope is
`{p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)`.
It has no additional theorem-valued premises.

## Actual objects and conventions

For every positive rank `k`, let `B = Shahidi.twoBlocks k k hk hk`. The
inducing factors are the actual objects
`twoBlockFactors hk hk ρ.obj ρ'.obj`; the product `P` is their image under
`T.normalizedProductInductionFunctor B`. The upper normalized induction uses
positive half-modulus covariance and right translation. The normalized
Jacquet functor uses the inverse half-modulus.

For either adjacency alternative, `ρ' ≅ νρ` or `ρ ≅ νρ'` with `ν = |det|`,
and every actual invariant subspace
`S : Subrepresentation P.representation` satisfying `S ≠ ⊥` and `S ≠ ⊤`,
the theorem provides both actual `Representation.Equiv` witnesses:

- The representation of
  `(T.normalizedJacquetFunctor B).obj (SmoothRep.subrepresentation P S)`
  is equivalent to
  `FiniteTensor.externalSmoothObject (twoBlockFactors hk hk ρ.obj ρ'.obj)`.
- The representation of
  `(T.normalizedJacquetFunctor B).obj (SmoothRep.quotient P S)`
  is equivalent to
  `FiniteTensor.externalSmoothObject (twoBlockFactors hk hk ρ'.obj ρ.obj)`.

The factor order is the same for both adjacency alternatives. The field
universe `uF` and input-carrier universe `uV` are independent. The product,
subspace, quotient and Jacquet carriers are in `max uF uV`, while the
tensor targets are in `uV`. The witnesses cross these universes.

## Implemented proof

The proof introduces the rank, actual factors and adjacency condition, and
takes the Jacquet conclusion of
`TwoSupercuspidalAdjacent.adjacentStructure`. It supplies that lemma's two
premises with the published theorems
`CuspidalSupport.nonassociatedJacquetSubquotients F T (k + k)` and
`CuspidalSupport.associatedJacquetFiltration F T (k + k)`.
They prove exactly `NonassociatedJacquetSubquotientsTheorem` and
`AssociatedJacquetFiltrationTheorem` in the original independent universes.

The general argument is described in the paired
`TwoSupercuspidalAdjacentStructure.md`. The associated geometric filtration
has exactly two irreducible factors, the inducing tensor and its block
swap. Their central characters differ on the first-block scalar uniformizer,
so they are inequivalent. Minimal nonzero Jacquet descent and the
nonassociated theorem make Jacquet length strictly increase along invariant
subspaces. Thus every nonzero proper subspace and its quotient have Jacquet
length one.

First adjointness sends the nonzero inclusion of `S` into the induced
representation to a nonzero map from its Jacquet module to the inducing
tensor. Irreducibility makes this map bijective, yielding the first
equivalence. Exactness gives a two-step filtration of the product's Jacquet
module by the image of the Jacquet module of `S`. Jordan–Hölder comparison
identifies its complementary graded representation with the swapped tensor.
The canonical equivalence with the quotient's actual Jacquet module gives
the second witness. Consequently the proof constructs equivalences of the
full Jacquet modules; factor counts alone are not used as equivalences.

This proposition quantifies over proper nonzero invariant subspaces; it does
not assert that one exists. Adjacent reducibility and the full product
structure theorem remain separate obligations.

## Provenance and independence

Provenance is Zelevinsky 1980, Proposition 1.11(b), printed p.175/PDF p.12
(`zelevinsky-1980-induced-ii`), using the length argument of
Bernstein–Zelevinsky 1977, §2.16(1), printed pp.449–450/PDF pp.10–11
(`bernstein-zelevinsky-1977-induced-i`). The specialization is internal derived
content, and its proof uses the actual Library constructions.

The recursive project import closure has 457 modules, all with nonempty
paired Markdown. All 455 imported Library pairs agree with the workspace
base. Of these, 410 modules have identical Lean and Markdown hashes to the
previously checked associated and nonassociated Jacquet proof closures.
The additional modules supply the algebraic core, statements, Jacquet-length
detection and subquotient transport, finite tensor properties, central
character separation, normalized first adjointness, and
Jordan–Hölder/quotient algebra. The core's own closure has 185 modules.

The associated and nonassociated inputs are fully proved geometric-lemma
specializations on actual filtrations and coinvariant quotients. Their
proofs use only lower representation, matrix, compactness and filtration
constructions. The direct lower results used by the core are
`minimalNonzeroJacquet`, `totalConjugatingCount`, `glCuspidalTensor`,
`admissibleSchur_centralCharacter`,
`IntegralTwistFreeness.scalar_uniformizer_value`,
`Parabolic.FirstAdjointness.equiv`, `normalizedJacquetMap_exact`,
`jordanHolderSeriesComparison`, the Jacquet-length/count lemmas, and the
algebraic tensor flip and Weyl transport equivalences. Each is an actual
proved Library declaration or a proved lemma in the supplied core.

Neither the imports nor the mathematical route use general derivatives,
Ze80's segment derivative formulas, segment product irreducibility or segment
Jacquet formulas, special-head or reverse-socle existence, ordered
multisegment head/socle existence, quotient coverage, ordered conversion,
analytic segment classification, square-integrability, tempered uniqueness,
or any classification or exhaustion conclusion excluded by the parent task.
The inherited `Classification.Segments` module supplies lower definitions
only; the route through `SupercuspidalSupport` uses elementary subquotient
transport. Compact-object and unipotent-subgroup exhaustion constructions are
unrelated to the excluded classification exhaustions. The Shahidi imports
supply the tensor flip, without an analytic intertwining-operator premise.
No second adjointness is used.

The core also contains conditional composition and product-structure
assemblies. Their nonadjacent-irreducibility and adjacent-reducibility inputs
remain explicit hypotheses of those lemmas. This theorem uses only the
Jacquet conclusion, which requires neither input, so those assemblies do not
assume the parent conclusion in this proof.
