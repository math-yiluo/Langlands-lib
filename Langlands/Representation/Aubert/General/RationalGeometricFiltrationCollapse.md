# Conditional collapse of actual rational geometric filtrations

Worker 167. This is an internal consumer of the published finite-filtration
collapse theorem, actual rational geometric-term vanishing, and surviving-term
comparisons. It proves conditional statements about supplied actual filtrations;
it does not construct or assume the truth of a general geometric-lemma theorem.

`smoothSingleSurvivingPieceIso` works over an arbitrary commutative coefficient
ring and topological group, with independent coefficient, group and carrier
universes. It takes an actual finite zero-to-full filtration of a smooth object
`A`, a smooth object for each grade, and actual representation isomorphisms from
the filtration quotients to those objects. If all objects except a distinguished
occurrence have subsingleton carriers, their quotient carriers do too, by the
injectivity of the grade isomorphisms. The published
`ObjectRepFiltration.singleSurvivingGradeIso` identifies the ambient algebraic
representation with that distinguished quotient. Composing with its grade
isomorphism and using `SmoothRep.mkIso` gives the stated actual smooth
isomorphism. No splitting, finite-length or nonvanishing premise is used.

`smooth_isIrreducible_of_iso_pullback` works over the complex numbers for two
arbitrary topological groups, with independent group and carrier universes. An
actual isomorphism from `B` to the pullback of `A` along a continuous group
equivalence transports irreducibility from `A` to `B`. Its proof first applies
`isIrreducible_comp_continuousMulEquiv_iff` to the equivalence, then transports
irreducibility along the inverse of the displayed smooth isomorphism.

`pointInducedJacquetObject` names the original actual normalized induction
from source Levi `J`, followed by the original actual normalized Jacquet functor
toward Levi `I`. Both use the semidirect decompositions supplied by the retained
standard-cocharacter statement. It changes neither the functors nor their
normalization.

The rational consumers retain the canonical evaluation topology `pointTopology`,
actual simple-root labels and actual standard subgroup families, independent
field and carrier universes `u` and `v`, and carrier universe `max (u + 1) v`.
They retain connected reductivity, the actual maximal split torus and generic
cocharacter, standard-cocharacter and standard-Levi intersection statements,
closed Levi and radical families, point-normalizer and point-centralizer
comparisons, finite simple roots and Weyl group, the actual Coxeter system,
root-length and positive-simple-reflection comparisons and the minimality
criterion.

For a maximal subset `J` different from its associate, the consumers take the
original `IsCorollaryLeviCuspidal` condition on `σ`. Their additional inputs are
an actual finite filtration of the displayed induced Jacquet object, an
injective ordered list of minimal Weyl classes, an actual normalizer lift and
the actual source and target decompositions for each listed class, an
isomorphism from each actual graded quotient to its actual normalized
`geometricTermFunctor` value, and a specified surviving occurrence. These
filtration and grade isomorphisms are mathematical hypotheses, not constructed
outputs. Injectivity excludes a second occurrence of the surviving class.
No surjectivity of the class list is required for this conditional deduction.

`pointSelfJacquetIsoOfGeometricFiltration` takes a distinguished occurrence of
class `1`. Every other class differs from `1` by injectivity. The actual
`pointGeometricSelfTerm_subsingleton_of_ne_one` kills each corresponding term
using maximality, non-self-association and original cuspidality. The generic
smooth collapse identifies the whole Jacquet object with the surviving term.
`pointGeometricTermIdentityClassIso` then identifies that term with `σ` for its
actual chosen normalizer lift. The resulting isomorphism uses no finite-length
preservation premise.

`pointAssociatedJacquetIsoOfGeometricFiltration` additionally takes the
associated-subset laws, a fixed longest normalizer lift, and a distinguished
occurrence of the inverse-longest class. The target Levi is literally
`associatedSubset actual J`. The actual associated non-survivor vanishing
theorem kills every other term. Collapse followed by
`pointGeometricTermInverseLongestClassIso` identifies the whole object with
pullback of `σ` along the inverse associated-Levi equivalence for that fixed
longest lift, independently of the survivor's chosen lift.

The corresponding irreducibility corollaries assume `σ.IsIrreducible` and
transport it through these actual isomorphisms. The associated corollary applies
`smooth_isIrreducible_of_iso_pullback` with the inverse associated-Levi
equivalence and the constructed associated Jacquet isomorphism. Thus the
irreducibility argument uses the invariant-submodule lattice comparison under
a group equivalence.

The dependency route is actual finite-filtration algebra, actual cuspidal
vanishing and conjugation transport. It invokes no classification theorem,
character independence, adjointness or cuspidal-support existence theorem.
The normalized geometric filtration and its actual grade comparisons remain
unproved inputs here. Consequently this unit does not prove the unconditional
two-Jacquet equivalences or `RationalRankOneSelfAssociationStatement`, and these
intermediate filtration hypotheses must not be added to that final target.
