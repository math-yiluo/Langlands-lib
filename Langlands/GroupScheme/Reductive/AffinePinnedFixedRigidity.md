# Affine pinned solutions and rigidity on arbitrary common schemes

Worker 591. This derived adapter assumes the exact published proposition
`AffinePinnedIsomorphismTheoremStatement`; it does not prove that proposition.
It constructs its scalar-extended affine solution and derives uniqueness of
fixed comparisons over arbitrary common schemes. The setting is Conrad,
*Reductive group schemes* (2014), Theorem 6.1.17, p.197.

The two supplied affine pinned models may have different original rings,
coordinate index types and root data. Fix one full root-datum equivalence
from the target model to the source model, matching their chosen bases.
For any common coefficient ring with the two original algebra structures,
`IsAffineSolution` is exactly the affine pinned theorem's torus-square,
all-test character and pinning-vector differential predicate for their
actual scalar extensions. `affineSolution` chooses the unique solution
provided by the supplied theorem, with an exact predicate specification.

The canonical fixed torus map has the prescribed character monomials on
every test scheme by the published exponent-character identity. A supplied
`FixedComparison` over the coefficient spectrum therefore satisfies the
torus/character clause. Its pinning-point condition on the identity affine
test, together with the actual scalar-extension pinning-point identity,
gives precisely the differential clause. Affine full faithfulness makes
two such supplied fixed comparisons equal over that spectrum.

Finally, any common test scheme is covered by its affine open spectra.
The original endpoint maps induce the two algebra structures on each
coordinate ring. Fixed comparisons pull back to these spectra with the
same fixed datum. The preceding affine uniqueness gives equality there;
reindexing equal endpoints and the actual direct/iterated pullback identities
recover equality of the ordinary pulled-back group maps. The published
étale locality of homomorphism equality then proves equality over the whole
common scheme. No connectedness or affineness is assumed on this scheme.
This establishes rigidity conditional on the supplied affine theorem;
existence of fixed comparisons and compatible local gluing remain separate.
