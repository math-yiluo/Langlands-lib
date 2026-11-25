# Original canonical quotient comparison under coordinate conjugacy

This internal adapter for the finite vector-bundle filtrations of supplied
relative radicals proves scalar equivariance and
linearity of the original ambient-compatible `sameParabolicQuotientIso`.
It combines actual root-transport comparison with actual parabolic
conjugation. The original quotient comparison is retained throughout.

The final coordinate-conjugacy interface assumes an arbitrary nontrivial
commutative base ring at universe `u`, an affine reductive group `G`,
two fibrewise maximal split tori with finite coordinate types, their
actual fibrewise root data and actual root parametrizations, and supplied
split parabolic face charts `C` and `D`. The original actual contracting
subgroup functors agree, as do the original actual parabolic subgroup
functors. The latter equality is an explicit geometric input.
There is an actual base point `u` of the represented source original
parabolic, an integral coordinate isomorphism `E`, and the actual square
`i ≫ innerIso(g).hom = precompTorus E j`, where `g` is the image of `u`
under the original parabolic inclusion.

No equivalence of root data, matching root ranges, equality of face
heights, term compatibility, scalar equivariance or linearity is supplied
to this final interface. The proof derives these consequences from the
stated geometric data. There is no assumption that `g` centralizes the
face-realizing cocharacter. The original cocharacters may have zero
roots. The source and target retain their respective exact-support index
types, but their cardinalities agree for corresponding layers; both may
be zero. This equality follows from the height-preserving root bijection
and is also forced by the resulting linear equivalence over a residue
field of the nontrivial base ring.

Two generic lemmas isolate the composition argument.
`AutomorphicAction.isEquivariant_of_iso_comp` removes an equivariant
source automorphism from an equivariant composite. On each test scheme
it pulls the input point back through the given inverse isomorphism and
uses the two equivariance equations and the composite equation.
`FppfQuotientComparison.comp_eq_of_fac` proves that compatible actual
term-map compositions give the same composition after a full fppf
quotient. It applies the existing quotient `hom_ext` to the three
factorization equations. Neither generic lemma assumes global lifting
of points through a quotient.

The first face-chart composition helpers allow a supplied compatible
full-root transport, to expose the actual factorization separately from
the subsequent derivation of its inputs.
`sameParabolicTermIso_parabolic_factorization` proves
`J_term.hom ≫ original_term.hom = transported_term.hom`. It evaluates the
actual parabolic term automorphism at the universal source point to
obtain its ambient morphism equation. Direct cancellation of the target
representing monomorphism and the existing ambient equations then prove
the equality of actual term morphisms.
`sameParabolicQuotientIso_parabolic_factorization` applies the generic
full-quotient composition lemma to give
`J_quot.hom ≫ original_quot.hom = transported_quot.hom`.
`sameParabolicQuotientIso_eq_parabolic_inv_comp_rootTransport` rewrites
this as
`original_quot.hom = J_quot.inv ≫ transported_quot.hom`.
The supporting hypotheses of these factorization helpers are actual
root ranges and exact unscaled face heights; the final interface below
derives both.

`rootTransportQuotientIso_isEquivariant_of_parabolicRootTransport`
proves actual transported quotient equivariance from the actual source
and transported target cocharacter actions, their quotient equivariance
and their actual term equivariance. Local flat surjective quotient
lifts, supplied by the existing comparison theorem, transfer these
equations to the quotient. The common scalar power is the source
`C.faceMultiplier * (d+1)`, even if the target has a different chosen
realization multiplier.
`sameParabolicQuotientIso_isEquivariant_of_parabolicRootTransport`
combines this assertion, the proved actual original-parabolic quotient
equivariance and the actual quotient factorization. It concludes scalar
equivariance of the original canonical quotient comparison.

The final
`sameParabolicQuotientIso_isEquivariant_of_coordinateConjugacy`
derives all those transport inputs. The actual coordinate-torus square
determines a full root-datum equivalence with exactly the specified
coordinate weight map and matches every actual root range.
The point `g` lies in the actual original parabolic. Its normalization
of the actual contracting subgroup shows that transport through
`innerIso(g)` preserves the common contracting functor. Actual positive
and zero root-sign detection then identifies the two faces; the
existing root-height comparison gives equality of their exact original
unscaled heights. The prescribed weight map makes the original actual
torus square precisely the square required by root-transport linearity.
Applying the preceding composition result proves the final scalar
equivariance assertion without any remaining abstract transport input.

`sameParabolicQuotientIso_hasScalarWeight_of_coordinateConjugacy`
derives the all-coefficient-algebra scalar identity.
`sameParabolicLayerLinearEquivOfCoordinateConjugacy` constructs the
linear equivalence of the original canonical quotient on every
coefficient algebra; positivity follows from the source face multiplier
and `d+1>0`.
`sameParabolicQuotientIso_eq_matrixHom_of_coordinateConjugacy`
identifies the original actual quotient morphism with the morphism of
its base-ring matrix.
`coordinates_sameParabolicQuotientIso_of_coordinateConjugacy`
gives that matrix formula on every scheme test, with coefficients mapped
by the actual base scalar map. Nonreduced tests and empty layers are
included.

The provenance is internal. The implementation combines the existing
actual coordinate-torus/root transport, actual contracting sign and
face-height comparisons, actual parabolic quotient linearity and full
fppf quotient uniqueness. It uses arbitrary-ring positive-weight
rigidity for the final linear and matrix constructors. There is no
field, noetherian, reducedness or fixed-rank assumption; the nontrivial
ring premise is retained from the actual root comparison.

The implemented consumer `SplitFaceGlobalQuotientLinearity` constructs actual
étale coordinate-conjugacy neighborhoods and reflects this local result to the
original canonical quotient comparison on all tests. The further consumer
`AffineFaceQuotientRestriction` derives the linear comparison of the original
quotients on arbitrary common affine restrictions, retaining the actual ambient,
step and full fppf quotient squares, including empty overlaps. These are the
specific transitions needed to descend vector-bundle quotients of the actual
finite face series. This pair is an intermediate transition result towards
the unchanged arbitrary-universe
`RelativeUnipotentRadicalFiltrationStatement`: actual descent of the quotient
modules and final assembly of the finite series on every supplied radical are
separate consumers, and this module does not prove that statement (it is
proved as `relativeUnipotentRadicalFiltration` in
`RelativeUnipotent.RadicalFiltrationProof`).
