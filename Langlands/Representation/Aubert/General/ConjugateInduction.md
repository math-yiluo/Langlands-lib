# Induction from the actual conjugate parabolic

This internal supporting construction uses the actual subgroups
`g P g⁻¹` and `g U g⁻¹` and a supplied actual subgroup `N` satisfying
`x ∈ N ↔ g⁻¹ * x * g ∈ M`. The functor
`conjugateInductionFunctor` is the published actual normalized induction
functor for the semidirect decomposition supplied by
`IsSemidirectDecomposition.conjugateWithLevi`. Closedness of the conjugate
radical is proved by `isClosed_conjugateSubgroup`.

Finite-length preservation and preservation of short exact sequences of
finite-length representations are derived from the corresponding hypotheses
for the original induction functor. For arbitrary simultaneously conjugate
decompositions, the proof applies `inductionConjugationIso` with `g⁻¹` and the
membership equivalences supplied by `conj_inv_iff`. This identifies induction
from the conjugate parabolic with inverse conjugation followed by the original
induction. Pullback along a topological group isomorphism preserves finite
length and short exactness. The proofs compose those preservation results and
transfer them through the natural isomorphism using
`PreservesFiniteLength.of_iso` and
`PreservesFiniteLengthShortExact.of_iso`.

`conjugateInductionK0` is therefore an actual integer-linear map on the exact
finite-length Grothendieck group, defined without new preservation hypotheses
on the conjugate parabolic. Its composition with `conjugationK0 g hMN` equals
the original `inductionK0`, by specialization of the published theorem
`inductionK0_comp_conjugationK0`. This equality concerns the entire exact
Grothendieck group, including its short-exact-sequence relations.

The declaration dependencies are the subgroup transport in
`Langlands.Representation.Aubert.General.ConjugateParabolic`, conjugation
compatibility in `Langlands.Representation.Aubert.General.Conjugation`, the
pullback preservation laws in
`Langlands.Representation.Smooth.FiniteLengthGrothendieckTransport`,
the composition laws in
`Langlands.Representation.Smooth.FiniteLengthGrothendieckFunctor`, and the
isomorphism transport laws in
`Langlands.Representation.Smooth.FiniteLengthGrothendieckIso`.
This is a derived internal construction. It invokes no Langlands
classification, character independence, geometric lemma, adjointness or
cuspidal-support theorem. In particular,
`pullbackFunctor_preservesFiniteLength` uses
`Langlands.FiniteLengthAssembly.finiteLength_comp_surjective_iff`, which uses
`length_comp_surjective` and the elementary invariant-subspace order isomorphism
`Langlands.CuspidalSupport.JacquetLength.compSubrepresentationOrderIso`.
Those declarations hold for arbitrary surjective changes of acting monoid.
Although their source modules also import classification and cuspidal-support
developments, these declaration bodies use only equality of the invariant
subspace lattices and invariance of module length under an order isomorphism.

`inductionK0_comp_conjugationK0_of_sameLevi` records the precise remaining
comparison: an induction map for a second decomposition with the same actual
Levi `N` must equal `conjugateInductionK0`. Under that explicit hypothesis it
rewrites the second induction map and applies the proved conjugation identity.
The required comparison for two different parabolics is not proved here.
These declarations alone do not prove the full rational-point Weyl-conjugacy
target.
