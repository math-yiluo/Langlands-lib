# Induced exact-K0 Weyl conjugacy from admissibility and generic isomorphism

Author: Worker 60. This internal reduction keeps the independent universes
`u` and `v`. Its conclusion is the unchanged, unapplied published
`RationalInducedK0WeylConjugacyStatement.{u,v}`.

## Statement

`RationalInducedK0WeylFromGenericIsoStatement.{u,v}` is the implication from
three propositions to the target:

1. `RationalPointsFiniteLengthAdmissibleStatement.{u, max (u+1) v}`:
   finite-length smooth representations of `G(k)` are admissible;
2. `DynamicLeviFiniteLengthAdmissibleStatement.{u, max (u+1) v}`: the same for
   every actual dynamic Levi `Z(χ)(k)`;
3. `RationalSameLeviGenericInductionIsoStatement.{u, max (u+1) v}`: generic
   isomorphism of the normalized inductions from `P_J` and `g P_I g⁻¹` of
   unramified twists of an irreducible admissible representation of `L_J`.

`rationalInducedK0WeylConjugacy_of_genericIso` proves it. The module proves
none of the three premises. The first two are the published prerequisite
targets of `PrerequisiteStatements`. The third is stated in the companion
module `RationalSameLeviGenericIsoStatement`. All three are
representation-theoretic proof obligations. The carrier universe
`max (u+1) v` is that of the target.

## The finite-length comparison

`exists_ne_zero_vanishing_of_irreducible` is generic. Let `Δ` be an
integer-linear map from the exact finite-length Grothendieck group of any
topological group into functions `X → D`. Let `Z p ⊆ X` be sets indexed by
multivariate polynomials, with `Z (p * q) ⊆ Z p ∩ Z q`. Suppose that for
every irreducible `A` some nonzero `p` has `Δ [A] = 0` on `Z p`. Then every
class has such a polynomial. The proof writes the class as the realization of
an element of the free lattice on irreducible classes, using the published
bijectivity `irreducibleGrothendieckStatement`. It then inducts on that
finitely supported function (`Finsupp.induction_linear`). Sums use the
product polynomial, which is nonzero because `MvPolynomial` over `ℂ` is a
domain. Generators use `IrreducibleIsoClass.exists_eq` and
`realizeIrreducibles_generator_irreducibleIsoClass`.

`exists_principalOpen_subset_comparisonLocus_of_genericIso` works under the
section hypotheses of the published `RationalConjugateInductionK0Comparison`:
two actual decompositions with Levis `L_I` and `L_J`, a conjugation witness
`hIJ`, closed radicals, continuous projections, a regular Haar measure and
compact left quotients. For every unramified character `χ` it forms two
integer-linear maps on the exact K0 of `L_J`. Each composes the actual twist
`FiniteLengthGrothendieckGroup.twist` with `inductionK0` and the exact
character map `Character.exactK0DistributionCharacter`. The first uses
induction from `Q = L_J V`; the second uses the actual conjugate
decomposition `hI.conjugateWithLevi g hIJ`. Its finite-length and exactness
preservation come from `conjugateInductionFunctor_preservesFiniteLength` and
`conjugateInductionFunctor_preservesShortExact`. On an actual finite-length
object, `twist_ofRepresentation`, `inductionK0_ofRepresentation` and
`exactK0DistributionCharacter_ofRepresentation` identify the two values with
the genuine distributions `rationalLeviUnramifiedInductionDistribution`. The
two admissibility proofs agree by proof irrelevance.

For irreducible `σ`, the generic-isomorphism hypothesis gives a nonzero
polynomial and an isomorphism at each `χ` of its principal open.
`SmoothRep.equivOfIso` and `Character.distribution_eq_of_equivariant` then
give equal distributions. `mem_leviUnramifiedPrincipalOpen` and
multiplicativity of evaluation verify the product condition on principal
opens. The generic lemma therefore supplies, for every finite-length `σ`, a
nonzero polynomial whose principal open lies in the published
`rationalConjugateInductionComparisonLocus`.

## The main theorem

The proof introduces every binder of the target, with the canonical point
topology, and fixes `I`, `J`, a normalizer point `n` and the literal Levi
transport `hIJ`. It then supplies each input of the published
`inductionK0_comp_conjugationK0_of_rationalPrincipalOpen`, instantiated at
carrier universe `max (u+1) v`:

- the decompositions are `isSemidirectDecomposition_of_standardCocharacterStatement`,
  with the target's closedness, projection-continuity and preservation data;
  `standardParabolicFiniteLength` gives the four preservation properties,
  exactly as in the target;
- the measurable structure is `borel`, with `BorelSpace` by definition, and the
  measure is Mathlib's `Measure.haar`, which is a regular Haar measure;
- compactness of both left quotients is
  `compactSpace_leftQuotient_parabolic` applied to the published proof
  `BruhatTits.dynamicParabolicQuotientCompact`;
- connected reductivity of `Standard.leviScheme i ν (rootSet i ν J)` is
  `standardLeviScheme_isConnectedReductive` applied to the published proof
  `GroupScheme.dynamicCentralizerReductive`;
- ambient admissibility is premise 1 directly, and admissibility on `L_J` is
  `standardLevi_isAdmissible_of_hasFiniteLength` applied to premise 2;
- the principal-open comparison is the theorem above, fed by premise 3 at the
  same data.

The conclusion of the published reduction is literally
`i_J.comp (conjugationK0 n hIJ) = i_I` on the whole exact finite-length
Grothendieck group, with the inverse-conjugation pullback
`x ↦ σ(n⁻¹ * x * n)`. Every normalizer lift and every displayed premise of the
target is retained. No Coxeter system, root enumeration or root-sign premise
is used.

## Dependency ledger

Beyond the three premises, the route uses only published proofs. These
include the character-independence chain behind the published reduction
(`Character.exactK0CharacterRealization` and
`Character.exactK0CharacterInjectivity`, hence
`Character.distributionShortExactAdditivity`,
`Character.finiteFamilyLinearIndependence` and
`SmoothRep.irreducibleGrothendieckStatement`), the published density and
continuity results for unramified induced distributions, and the conjugation
transport `inductionConjugationIso`. The structural inputs are the published
proofs `BruhatTits.dynamicParabolicQuotientCompact` and
`GroupScheme.dynamicCentralizerReductive`. This module itself uses no
Langlands classification, geometric lemma, adjointness or cuspidal-support
theorem. The dependency accounts in `RationalLeviInductionK0Comparison.md`
and `RationalConjugateInductionK0Comparison.md` record none for the published
reductions it applies. A proof of premise 3 may use such results; its own
ledger must record them. Aubert Proposition 3.2 is not used.
