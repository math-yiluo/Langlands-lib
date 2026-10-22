# Pointwise-finite sums of projectors and natural decomposition

Author: Worker 173. This internal algebraic construction prepares the sum used in BZ76
section 4.17, printed pages 41–42. It proves no existence of compact-coefficient
projectors and no fixed-level finiteness theorem. Those are separate prerequisites
of the eventual `LeviQuasicuspidalDecompositionTheorem` proof.

For an arbitrary representation over a commutative ring and a family of actual
equivariant endomorphisms, `pointwiseFiniteSum` constructs their sum provided that
only finitely many terms are nonzero on each vector. The index, group and carrier
universes are independent; the collection of endomorphisms need not itself be
finite. Mathlib's `finsum` implements the finite sum. Its addition and scalar
multiplication laws prove linearity, and commuting a group action through the sum
proves equivariance. The support hypothesis ensures that this is the intended
sum on every vector, rather than the default value of `finsum` for infinite support.

`finiteSupport_of_finite_stratum` supplies the support condition from a finite set
outside which all components vanish. It does not construct that finite set. In
the eventual application it will come from the classes with a fixed vector at a
chosen compact-open level and the vanishing of other isotypic components.

For pairwise orthogonal idempotents, applying one component to the total sum
leaves only that component, and the total sum fixes each component image. These
identities prove idempotence of the total sum without exchanging two infinite
sums. The covariance theorem commutes a linear map through the sum when it maps
components according to an equivalence of the index sets. It includes ordinary
naturality when the equivalence is the identity, and can also support the future
ambient-conjugation argument once covariance of the actual components is proved.

The proof uses only finite-support algebra from Mathlib and the definitions of
representations and intertwiners. It has no topological hypotheses, admissibility
or dimension restriction. All projector, covariance and support assumptions are
explicit internal inputs; the final published decomposition target must prove
its instances from the actual product-Levi data.

The final `SmoothRep.decomposition_of_pointwiseFiniteSum` theorem assembles these
facts with the companion `NaturalProjectorDecomposition` module. It assumes a
natural orthogonal family on all smooth objects in a fixed carrier universe,
pointwise finiteness, a property P of every total image, and identity on every
P-object. The construction then gives actual complementary invariant subspaces
whose first summand has P and whose second has no nonzero actual P-subquotient.
Its proof specializes permutation covariance to the identity on indices, applies
the idempotence theorem, and invokes the companion range/kernel argument. These
conditional algebraic laws do not prove the existence of the representation
theoretic inputs needed by the main task.

This pair and the companion pair constitute one internal construction unit,
submitted for review separately from the unfinished product-Levi theorem.
The BZ76 reference is motivation for the finite-sum construction, not a claim
that this abstract Lean interface is transcribed from the source. The registered
source is `bernstein-zelevinsky-1976-representations-gln`, SHA256
`72dc22eb9991112936a88327f00d0f02a16a2bf8747518ca0ecfeeadd188e50c`.
