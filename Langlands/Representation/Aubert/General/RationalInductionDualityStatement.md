# Natural induction duality on the actual rational-point group

Author: Worker 196.

`Langlands.Aubert.General.RationalPointFamily.RationalNaturalInductionDualityStatement`
is a proposition definition awaiting proof. It specifies a coherent family of
same-parabolic induction-duality isomorphisms on admissible objects. It supplies
no proof of those isomorphisms or of Aubert commutation.

## Actual groups and normalization

The field `k : Type u` is every nonarchimedean local field, with no
characteristic-zero restriction. The ambient group scheme is every connected
reductive `G` over `k`, including nonsplit and non-quasisplit groups. A maximal
split torus map `i` and a generic cocharacter `ν` specify the literal labels
`SimpleRoot i ν` and every finite subset `I` of them. There is no nonemptiness
condition on the labels or on `I`.

The actual point group `RationalPoint k G.X` carries the canonical
`RationalPointFamily.pointTopology`. Local compactness, nonarchimedeanness and
Hausdorffness are displayed hypotheses for that topology. All subgroup
topologies are induced from it. `StandardCocharacterStatement` constructs the
semidirect decomposition of the actual `parabolic i ν I`, `levi i ν I` and
`unipotent i ν I`, through the published theorem
`isSemidirectDecomposition_of_standardCocharacterStatement`. Closedness of the
parabolic and unipotent and continuity of this decomposition's actual Levi
projection are displayed. The latter two parabolic/projection premises do not
enter the expression defining the isomorphisms; their inclusion restricts the
target to the topological setting used by its intended consumer.

Write `F` for the published `General.normalizedInductionFunctor` on this exact
decomposition. It inflates along the actual projection, twists by
`HaarModulus.closedHalfCharacter` on the parabolic, and takes smooth induction
with right translation. Thus the covariance is
`f(p g) = δ(p)^(1/2) A(m(p)) f(g)`. Here `δ` is the actual positive Haar modulus
of conjugation on the closed unipotent subgroup and the square root is the
positive real square root embedded in `ℂ`. The same parabolic and the same
positive half character occur on both sides of duality.

An input is an actual bundled smooth complex representation `A` of the actual
Levi with `A.IsAdmissible`. This asks for finite-dimensional fixed spaces at
every open subgroup; it does not require finite length or a finite-dimensional
whole carrier. The inducing and induced carrier universes are
`max (u + 1) v`, where `u` and `v` remain independent. No topology on a
representation carrier or tensor decomposition of a Levi representation is
assumed.

## Coherence on the actual morphisms

For each fixed field, group, torus, cocharacter and subset, one family `E`
is chosen simultaneously for all admissible inducing objects:

`E_A : (F(A))∨ ≅ F(A∨)`.

The dual is the existing `SmoothRep.contragredient`: the smooth part of the
complex-linear algebraic dual, acted on by inverse transpose. For every actual
morphism `f : A ⟶ B` between admissible objects the required equation is

`(F(f))∨ ≫ E_A.hom = E_B.hom ≫ F(f∨)`.

Both sides are actual morphisms from `(F(B))∨` to `F(A∨)`. `F.map` is the
published postcomposition map on covariant functions, and `contragredientHom`
is pullback of smooth functionals. Coherence is required, rather than inferred
from arbitrary choices of unrelated objectwise equivalences.

## Source correspondence and derived formulation

The registered original source is Bill Casselman, *Introduction to admissible
representations of p-adic groups*, Chapter III, revision April 29, 2019,
source `casselman-2019-jacquet-module`, SHA256
`377edac998669bc88da1224c4582a173854232f7fea5caf945d140ee92fde5c1`.
The retained original is
`/home/taskhub/central-library/Casselman--p-adic groups lecture notes/Introduction to representations of p-adic groups/Casselman--Chapter III - Induced representations and the Jacquet module--2019.pdf`.
Pages 1–2 were read and Proposition III.1.1 on page 2 was visually checked.
No separate errata file for this source was found in the inspected public
notes or source folder.

Page 1 fixes rational points of a Zariski-connected reductive group, the
positive-half normalized covariance and right translation. Proposition III.1.1
on page 2 identifies the contragredient of normalized induction with normalized
induction of the contragredient from the same parabolic. Its displayed pairing
integrates the evaluation of an induced dual vector on an induced vector over
a good compact subgroup `K`.

The present rational-point/topology formulation and the coherent naturality
requirement are internal specializations of that assertion and its pairing,
not separate verbatim source theorems. For a fixed group and parabolic, choose
`K` and one Haar normalization uniformly in the coefficient representation.
Let `J_A : F(A∨) → (F(A))∨` be the map defined by that pairing. Evaluation of
the integrand gives

`J_A(F(f∨)(φ))(s) = J_B(φ)(F(f)(s))`.

Once the duality maps `J_A` have been proved to be equivalences, their inverses
give the stated family and its naturality equation. Establishing the actual
compact-picture integral, its invariance, the needed topological structure and
any normalization comparison remains part of a proof; none is added as a
premise of this proposition.

The published general module
`Langlands.Representation.Induction.CompactPairingDuality` provides conditional
pairing proofs that may be reused, but this target does not assume its scalar
integral hypothesis or a supplied duality equivalence. The published
`Langlands.Representation.Parabolic.NaturalInductionDualityStatement` treats
standard and refined general linear groups; it motivates the coherent
formulation but does not prove this general reductive target.

## Intended use and retained obligations

This target isolates one prerequisite for
`RationalContragredientCommutationStatement`. Using its admissible-input family
on a finite-length Jacquet object still requires an actual proof that that
object is admissible. The separately owned dynamic-Levi finite-length
admissibility task remains responsible for that input. No admissibility or
duality premise is added to the final commutation proposition.

This statement establishes no finite-length preservation, opposite-Jacquet
duality, associated-Levi representation-class comparison, Weyl invariance,
geometric lemma, classification theorem or commutation on an exact
Grothendieck group. Aubert 1995 formula (1.3) is the geometric-lemma identity;
it is not a same-parabolic induction-duality assertion.
