# Quasi-split inner-form comparison through one sectioned Borel

This internal module assembles the common-source inner-form comparison
and actual Borel-stabilizer descent. A single supplied inner form with
suitable sectioned Borel geometry suffices to construct isomorphisms
between all quasi-split inner forms of the original source.

The base is Spec R for a commutative ring object R. The anchor group G is
reductive, has an actual relative Borel iG : B to G, and has a supplied
full-centre fppf quotient qG : G to Gad with an action c whose restriction
is conjugation. The original group F has its own supplied full-centre
fppf quotient qF : F to Fad and compatible action a. The anchor is
assumed to be an étale inner form of F for a. The original group need
not be assumed reductive for these comparison constructions.

All sectioned geometry is supplied on this one anchor Borel:

- Homomorphisms i : K to B, p : B to T and t : T to B with t followed
  by p the identity, and z : Z to T.
- Fppf quotients qB : B to P and qT : T to D, with full kernel ranges
  range (z followed by t) and range z. The full kernel of p is range i.
- The map i is monic, K is affine over the base and has an actual finite
  vector-bundle series, and the total space of P is affine.
- The actual group D is isomorphic to WeilGm(R, C) for a module-finite
  projective commutative R-algebra C.
- A homomorphism k : P to Gad represents the full c-action stabilizer
  of range iG. The P in this presentation is exactly the P in qB.

No quotient, action, Borel section, radical filtration or induced torus
presentation on either of the two arbitrary forms being compared is
assumed. Their quasi-split hypotheses include reductivity and the
existence of a relative Borel.

`quasiSplitEtaleInnerIsoOfPicTrivial` chooses a relative Borel on a
quasi-split target H and an étale inner local family from G to H.
Étaleness supplies flatness and local finite presentation of its
surjective cover. `borelInnerIsoOfPicTrivial` then descends that family
using the supplied anchor geometry. Classical choice of the resulting
nonempty isomorphism type gives an actual isomorphism G to H.

`quasiSplitInnerFormsIsoOfPicTrivial` takes quasi-split forms H₁ and H₂
that are étale inner forms of F. The existing
`AutomorphicAction.IsEtaleInnerForm.compare` constructs innerness of
each Hᵢ relative to the anchor's action c. Applying the preceding
construction twice gives G isomorphic to H₁ and G isomorphic to H₂;
composing the inverse of the first with the second gives an actual
isomorphism H₁ to H₂. Only Pic C is required to be trivial.

`quasiSplitInnerFormsIsoOfFiniteAlgebrasHaveTrivialPicard` derives this
Picard hypothesis from finite-algebra Picard triviality of R.
`quasiSplitInnerFormsIsoOfSemilocal` obtains that property from finiteness
of the maximal spectrum of R. The theorem
`existsUnique_quasiSplitInnerForm_of_sectionedBorel` records the two
existence and uniqueness clauses for this particular F and a: the
supplied anchor itself supplies the existential witness.

The provenance is internal composition of `RelativeInnerForm` and
`RelativeLevi.BorelSectionedInnerDescent`. The proof constructs comparison
inner families through their full-centre quotients and composes the
isomorphisms obtained by actual Borel descent; it adds no vanishing
assumption on the full adjoint group.

This module does not construct the anchor, its full-centre quotient or
any of the supplied sectioned geometry. In particular it proves no
unconditional quasi-split existence or semi-local inner-form statement.
The statement this module serves, `ReductiveSemilocalQuasiSplitInnerFormStatement`
(assembled in `Langlands.GroupScheme.Reductive.SemilocalInnerFormAssembly`),
still requires these inputs for every
reductive group and each of its supplied quotient actions.
