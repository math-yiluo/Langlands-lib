# Coordinate comparisons for the full actual orbit representation

Author: Worker 200.

This derived comparison makes the existing integer-coordinate equivalence
compatible with the full actual product action, the actual orbit coefficient,
and the original entire invariant form. It is an internal consequence of the
published objects and the proved full-action construction. The source context
is Waldspurger, *La formule de Plancherel pour les groupes p-adiques* (2003),
VI.1, printed pp.295–296/PDF pp.61–62, for coherent sections and their compact
finite smooth-family model; V.1, printed p.288/PDF p.54, for the coefficient;
V.2, printed p.293/PDF p.59, for the inverse-degree fiber form; and the proof
of Proposition VI.4.1, printed p.306/PDF p.72, for the full product action.
Registered source `waldspurger-2003-plancherel`, SHA256
`4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`.
No separately stated coordinate-comparison theorem is attributed to those
passages.

## Laurent evaluation after an integer basis change

Fix finite bases `b : Basis J ℤ L` and `c : Basis J' ℤ L` of the same integer
module. The existing `finiteTorusBasisChange c b` reconstructs in basis `c`
the lattice character specified by the input coordinates, then evaluates
that character on basis `b`. For an exponent vector `n : J → ℤ`, define the
lattice element `l = b.repr.symm n`, using the existing finite-function to
finitely supported function equivalence. The new exponent vector is
`k ↦ c.repr l k`.

The private reconstruction lemma expands a lattice character with
`Basis.constr_apply_fintype`. Passing from the additive circle to its
multiplicative form and then to the complex inclusion gives exactly the
existing `torusCharacter`. Applying the published identity that basis
reconstruction retains the same lattice character proves
`torusCharacter_comp_basisChange`. It includes empty finite bases.

`hasLaurentUnitaryCoordinates_rebase` uses that equality at each actual group
element to transfer `HasLaurentUnitaryCoordinates ν e` to
`e.trans (finiteTorusBasisChangeMulEquiv b c)`, which is exactly the existing
`rebaseUnitaryTorusCoordinates ν e b c` when the group is a Levi subgroup.
The Laurent premise is proved for the new coordinates from the original
algebraic premise. Neither scalar smoothness nor continuity is added as a
substitute. The scalar prerequisite already discharges the original premise
for canonical rational coordinates; rational parabolic realization remains
separate.

## Full smooth representations and the actual coefficient

For the representation comparisons retain the existing generic locally
compact nonarchimedean group, actual semidirect `P = M U`, closed `P` and `U`,
compact open `K`, actual `G = P K`, continuous norm characters and Levi
projection, and canonical irreducible admissible complex inducing object.
Group, character-index, inducing-carrier, both finite parameter-index and
integer-module universes are independent. The inducing carrier needs no
topology, norm or finite dimension.

The published `productInducedSmoothOrbitRebaseEquiv` fixes the value at every
actual inducing representative. Both full actions are the restrictions of
one ambient actual fiber action. Thus their values after applying this
linear equivalence agree as raw sections. Subtype extensionality proves
`productInducedSmoothOrbitRebaseEquiv_action`; the rebased action uses the
Laurent premise just proved. `productInducedSmoothOrbitRebaseRepresentationEquiv`
bundles the same existing linear equivalence with this intertwining law.
The entry `productInducedSmoothOrbitRebaseIso` then applies the canonical
`SmoothRep.mkIso`. Its hom-application theorem confirms that its underlying
map is the original identity on actual fibers.

`unitaryOrbitCoefficientMap_rebase` retains the coefficient construction's
additional second countability, Hausdorff and Borel assumptions, local
compactness of `P`, ambient unimodularity and full parabolic modulus identity.
It also fixes the same normal central quotient, Haar measure and
square-integrability witness defining the actual discrete-series orbit.
The theorem compares entire functions from that same orbit into
`LocallyConstant G ℂ`. The auxiliary representative chosen by the actual
coefficient definition is independent of coordinates, and the coordinate
equivalence preserves the section value at that representative. Equality is
therefore definitional. It needs no Laurent premise, coordinate continuity,
finite stabilizer, positive inducing form or orbit measure. The original
compact Haar probability is unchanged.

## The original invariant form and its existing isometry

The form comparisons retain the hypotheses of `ProductInducedOrbitFormCoordinates`:
second countability and Borel structures, the same group/parabolic data and
modulus identities, compact-open cofinality in the Levi, the same central
quotient Haar measure with inversion invariance, square-integrability,
finite central norm quotient, continuous forward coordinates, and a finite
open-positive character measure `η`. In addition the original coordinates
satisfy the algebraic Laurent premise required for the full action.

`productInducedSmoothOrbitRebaseForm_inner` compares the entire full
invariant forms on every pair of sections. Their underlying cores are
definitionally the original orbit-integral cores, so the result is the
published whole-core comparison. It retains the actual orbit measure, its
inverse stabilizer-cardinality scale and the same inverse-degree fiber forms.
No rescaling or newly chosen inner product is involved.

`productInducedSmoothOrbitRebaseIsometry_action` proves that the already
published linear isometric equivalence for the norms of these actual cores
intertwines the full product actions. Its underlying map is the same
coordinate equivalence, so the proved action comparison applies directly.

The unit covers integer basis changes of the supplied finite torus
coordinates. It adds no arbitrary torus-coordinate invariance, Hilbert
completion, density weight, intertwining continuation, constant-term
regularity, wave packet estimate or Fourier inversion. The standing
Plancherel task remains open.
