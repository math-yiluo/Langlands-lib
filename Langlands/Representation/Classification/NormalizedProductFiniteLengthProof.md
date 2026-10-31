# Finite-length preservation for normalized parabolic products

Author: Worker 325.

`Langlands.Classification.admissibleFiniteLengthProductPreservation.{uF,uV} F T`
proves the complete existing proposition
`Langlands.Classification.AdmissibleFiniteLengthProductPreservation.{uF,uV} F T`.
The only ambient parameters are a prime `p` with `[Fact p.Prime]`, an actual
`F : PadicField.{uF} p`, and compatible topological data `T`.
The field and representation-carrier universes remain independent.

For every positive total rank, ordered positive block shape, and family of
smooth complex block representations, admissibility and finite group-algebra
length of each factor imply finite group-algebra length of the actual normalized
product induction. Factors may be reducible or zero. The conclusion is
`IsFiniteLength` over the actual complex group algebra, rather than finite
complex dimension. The induced carrier remains the covariant function space
in `Type (max uF uV)`. The construction uses the supplied topology, upper
block parabolic, positive half-modulus in left covariance, and right translation
from the existing normalized induction functor.

The module also exports
`Langlands.Classification.normalizedInductionFiniteLength.{uF,uV} F T hn B`.
For `hn : 0 < n` and `B : GeneralLinear.BlockShape n`, this helper accepts any
representation `ρ : Representation ℂ (B.Levi F.Carrier) V`, with `V : Type uV`,
its additive and complex-module structures, admissibility of `ρ`, and
`IsFiniteLength (MonoidAlgebra ℂ (B.Levi F.Carrier)) ρ.asModule`.
It concludes
`IsFiniteLength (MonoidAlgebra ℂ (GeneralLinear n F.Carrier))
(T.normalizedParabolicInduced B ρ).asModule`.
Admissibility supplies smoothness. This helper does not require a chosen tensor
factorization of `ρ`; it applies to arbitrary admissible finite-length standard
Levi representations. Both public theorems use published proofs and have no
remaining irreducible-case or other replacement proof input.

The implemented argument first proves the arbitrary-Levi helper in the namespace
`Langlands.Classification.ProductLengthProof`.

1. The generic module helpers convert actual intertwiners to group-algebra linear
   maps using `Representation.IntertwiningMap.equivLinearMapAsModule`.
   Finite length transfers along injections and surjections. For a pair whose
   image equals the following kernel, the Noetherian and Artinian extension
   criteria give finite length of the middle representation.
2. An admissible irreducible Levi representation is factored, by the published
   `CuspidalSupport.padicLeviAdmissibleFactorization`, into irreducible smooth
   representations of its GL blocks in the prescribed carrier universe.
   The published `Classification.irreducibleProductFiniteLength` gives finite
   length of their normalized product. The actual induced equivariant
   equivalence transfers it to the given Levi representation's induction.
3. For consecutive invariant subspaces `S ⋖ R`, form the actual quotient
   `R / S` using the published `LengthCriterionProof.quotientRep`. The covering
   relation makes it irreducible. Admissibility of `R` follows by inclusion into
   the original representation. Admissibility of the quotient follows from
   `Unramified.SphericalExistence.isAdmissible_of_surjective`, using the proved
   compact-open subgroup basis for the actual Levi. Step 2 therefore gives
   finite length of its normalized induction.
4. The inclusion and quotient intertwiners are injective and surjective, and
   their image and kernel agree. The published
   `Parabolic.normalizedInductionExactness` supplies the corresponding equality
   for the actual induced maps. Step 1 extends finite length from the induced
   subspace and quotient to the induced middle subspace.
5. A group-algebra composition series for the original Levi representation is
   converted to a finite filtration by invariant subspaces using the published
   `LengthCriterionProof` helpers. Induction along this filtration uses step 4.
   The induction of the bottom subrepresentation is zero: every value of each
   induced function lies in the zero subspace. Finally the top subrepresentation
   is transported back by its actual equivariant equivalence.

To obtain the block-factor target, each factor's finite composition series gives
self-matching Jordan–Hölder factors. Apply the published
`FiniteTensor.padicExternalTensorFactors` to the family paired with itself.
One of its output composition series establishes finite length of the actual
external tensor representation of the product Levi. Its admissibility follows
from `FiniteTensor.isAdmissible_external`. The arbitrary-Levi helper now gives
exactly the normalized product functor's requested finite length. Zero factors
and zero-length composition series are included in these constructions.

This is an internal assembly of published results. Its source correspondence is
the block-factor specialization of Casselman, *Introduction to the theory of
admissible representations of p-adic reductive groups*, draft of 1 May 1995,
Corollary 6.3.8, printed/PDF p.60. That corollary assumes an admissible
finite-length Levi representation and cites Propositions 2.4.4–2.4.5,
printed/PDF p.28, for induction exactness and transitivity. These original
passages were read directly. The implemented composition-series extension uses
the proved normalized exactness theorem; the separately published
irreducible-product theorem handles the cuspidal embedding and transitivity
route. The initial tensor composition series is an additional translation from
the factorwise hypotheses, not the literal wording of Corollary 6.3.8.

The registered source is `casselman-1995-admissible-representations`, SHA-256
`78b921fc6331ad2b75389f37d15bd5ac3399e6cfc2d7555e1a4d666e0d42612a`,
retained at
`/home/taskhub/central-library/Casselman--p-adic groups lecture notes/Introduction to representations of p-adic groups/Casselman--Introduction to the theory of admissible representations of p-adic reductive groups--1995.pdf`.
No source-specific errata file was present at this check.

The proof uses neither `InducedFiniteTypeStatement` nor the GL
admissibility-plus-finite-generation criterion. It proves the preservation clause
and the stated arbitrary-Levi helper at positive total rank; the adjacent
irreducible-factor statement and aggregate retain their existing meanings.
The target pair and every imported pair are unchanged.
