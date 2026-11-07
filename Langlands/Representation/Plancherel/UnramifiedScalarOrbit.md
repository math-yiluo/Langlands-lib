# Rational scalar values on actual complex twist orbits

This module identifies the existing complex twist orbit of a smooth
representation with its character quotient by the full twist stabilizer.
It transports the invariant scalar presentations from
`UnramifiedScalarDescent` to this actual orbit, with continuous values on a
nonempty dense open regular region and agreement between presentations.
It also connects the stabilizer to the existing actual central-image
finite-index criterion, so that criterion and fraction-field fixedness
give an invariant presentation for an irreducible admissible input.

The orbit consists of actual smooth-representation isomorphism classes.
Its topology is the existing topology coinduced from the complex character
space. No algebraic-variety structure on the orbit is constructed here.

## Source and provenance

The original source is J.-L. Waldspurger, *La formule de Plancherel pour les
groupes p-adiques (d'après Harish-Chandra)*, J. Inst. Math. Jussieu 2
(2003), 235–333, DOI
[10.1017/S1474748003000082](https://doi.org/10.1017/S1474748003000082),
registered as `waldspurger-2003-plancherel`. The supplied PDF has SHA256
`4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`.

IV.1, printed pp.276–277 / PDF pp.42–43, defines the complex orbit using
isomorphism classes of twists. Polynomial scalar functions are defined
through their pullbacks to the character space. Rational scalar functions
on an open region have a regular numerator and a denominator that is
nonzero above that region. The beginning of IV.3, printed p.285 / PDF p.51,
uses generic induced irreducibility and Schur's lemma to obtain a rational
opposite-composition scalar on this orbit.

The constructions in this module are derived support for those
definitions, rather than a separately numbered source theorem. They
combine the existing orbit, its stabilizer relation and open parameter
map, the previously constructed invariant fraction presentations, and the
previously proved central-image finiteness theorem. In particular, this
module does not deduce fraction-field fixedness for an intertwining scalar
from those source passages.

## Generic orbit and its quotient

The generic section takes a group `H : Type uG`, its supplied topology and
`NonarchimedeanGroup` structure, a family
`ν : I → (H →* ℝ≥0ˣ)` with `I : Type uI`, and
`π : SmoothRep.{0, uG, uV} ℂ H`. The group, norm-index and representation
carrier universes are independent. The `NonarchimedeanGroup` hypothesis
provides the existing smooth twists.

Write `X = unramifiedCharacters ν` and
`S = smoothRepUnramifiedTwistStabilizer ν π`. The imported
`UnramifiedTwistOrbit ν π` is the range of the map
`χ ↦ SmoothRep.isoClass (π.twist χ)` inside `SmoothRep.IsoClass`.
It carries the topology coinduced by `unramifiedTwistOrbitMap ν π`.
The imported stabilizer criterion says that two twists have the same
class exactly when `χ⁻¹ * ψ ∈ S`.

- `unramifiedTwistOrbitMap_surjective` unpacks this range and produces a
  character representative of every orbit point.
- `isOpenQuotientMap_unramifiedTwistOrbitMap` combines surjectivity,
  continuity from the coinduced topology, and the existing openness
  theorem.
- `unramifiedTwistOrbitQuotientMap` is the quotient lift
  `X ⧸ S → UnramifiedTwistOrbit ν π`. The stabilizer criterion is exactly
  the well-definedness condition for Mathlib's left-coset relation.
- `unramifiedTwistOrbitQuotientMap_mk` identifies this lift at a quotient
  representative.
- `unramifiedTwistOrbitQuotientMap_bijective` proves injectivity by the
  same stabilizer criterion and quotient equality, and proves
  surjectivity by a character representative.
- `unramifiedTwistOrbitQuotientHomeomorph` equips the resulting equivalence
  with continuity in both directions. Continuity forward follows by
  testing along the character quotient map. Continuity of the inverse
  follows by testing along the open quotient parameter map to the orbit;
  that composite is the continuous character quotient map.
- `unramifiedTwistOrbitQuotientHomeomorph_mk` and
  `unramifiedTwistOrbitQuotientHomeomorph_symm_map` give both representative
  identities.

These results require neither finiteness of `S` nor irreducibility or
admissibility of `π`. They do not select a representation for each orbit
class or assume that an unrelated orbit type has the desired topology.

## Comparing the two full stabilizers

For an irreducible admissible object `A`,
`smoothRepUnramifiedTwistStabilizer_eq` identifies
`smoothRepUnramifiedTwistStabilizer ν A.obj` with
`unramifiedTwistStabilizer ν (Quotient.mk _ A)`, the full stabilizer in the
canonical smooth dual. It unfolds equality of isomorphism classes in both
quotients. A smooth-object isomorphism lifts to the full subcategory of
irreducible admissible objects by `IrreducibleAdmissibleRep.isoMk`;
an isomorphism there maps back by its inclusion functor.

`finite_smoothRepUnramifiedTwistStabilizer` then transfers the existing
central-quotient theorem. Its explicit hypotheses are a normal subgroup
`C ≤ center H` and
`Finite (H ⧸ (commonNormKernel ν ⊔ C))`. It concludes finiteness of the
full smooth-object stabilizer for `A.obj`. It does not assume finiteness of
a representation family or of its orbit.

## Actual characters and presentation existence

The scalar section uses an arbitrary nonarchimedean local field `F : Type u`
with its field, valuation and topology structures, a group scheme `L`
over `Spec F`, a supplied topology and `NonarchimedeanGroup` structure on
`GroupScheme.rationalPoints L`, and:

- `hp : Continuous (rationalValuationImageProjection L)`;
- `hL : GroupScheme.IsConnectedReductive L`;
- a smooth complex representation `π` of those actual rational points.

It uses the full rational norm family
`νL ψ = (rationalNormCharacters L ψ).toMul`, with every rational character
as an index. Its rational scalars lie in the existing concrete field
`rationalUnramifiedFunctionField L hp hL`, the fraction field of the
evaluation-generated regular algebra. No substitute scalar field or free
function on the orbit is introduced.

`unramifiedTwistOrbitScalarPresentation_exists` assumes
`Finite (smoothRepUnramifiedTwistStabilizer νL π)` and an element `f` of
this field fixed by every subgroup translation automorphism. It obtains a
`Fintype` from finiteness and applies
`unramifiedInvariantScalarPresentation_exists`. The conclusion is
nonemptiness of the type of invariant regular numerator/denominator
presentations of exactly `f`, for this actual stabilizer.

This is a conditional descent theorem: fixedness is explicit. The imported
construction takes the finite product of the denominator's translates and
multiplies the original numerator by the complementary factors. It then
uses the fixedness of `f` and injectivity of the actual fraction-field
embedding to prove numerator invariance. No averaging or division by the
stabilizer order is needed.

## Values on the actual orbit

In namespace `UnramifiedInvariantScalarPresentation`, let `p` be such a
presentation for the actual stabilizer and fraction `f`. None of the
following declarations requires that stabilizer to be finite:

- `orbitRegularRegion` is the inverse image of `p.regularRegion` under the
  inverse quotient-to-orbit homeomorphism. Thus it consists exactly of the
  classes above which the invariant denominator is nonzero.
- `orbitValue` composes `p.value` with that inverse homeomorphism, restricted
  to this region.
- `orbitRegularRegion_map` says that the class of `π` twisted by `χ` lies
  in the region if and only if `p.denominator.val χ ≠ 0`.
- `orbitValue_map` gives the value there as
  `p.numerator.val χ / p.denominator.val χ`.
- `orbitRegularRegion_isOpen` and `orbitRegularRegion_dense` transport
  openness and density along the homeomorphism.
- `orbitRegularRegion_nonempty` maps a point of the known nonempty
  quotient regular region to the orbit.
- `continuous_orbitValue` composes the continuous quotient value with the
  continuous inverse homeomorphism on the appropriate subtypes.
- `orbitValue_eq` applies quotient presentation independence at the
  inverse image of an orbit point. Hence any two presentations of the
  same fraction agree at every point where both denominators are nonzero.
- `orbitRegularRegion_inter_dense` transports the quotient theorem that
  two such regions have dense intersection. The imported density proof
  uses the nonzero product denominator in the regular domain; it does not
  assert that arbitrary dense sets have dense intersection.

Together with openness of the individual regions, the last theorem gives a
dense open common region on which the values agree. The constructed region
depends on the chosen presentation and is not claimed maximal. Every
value is restricted to a subtype expressing regularity, so the
construction does not evaluate a fraction at a pole.

## Actual finite-index specialization

The last section takes `L` affine and locally of finite type, and equips
its rational points with the existing canonical
`rationalPointTopology F L.X`. The required `NonarchimedeanGroup`
structure is provided by `rationalPoints_nonarchimedeanGroup L`.
Let `T` be an affine commutative group scheme and `s : T.toGrp ⟶ L` a
central morphism. The displayed premise
`(RenardCartan.splitValuationImage s).FiniteIndex` is the existing
actual-image finite-index condition.

`finite_rationalSmoothRepUnramifiedTwistStabilizer` applies the stabilizer
comparison and the imported
`finite_rationalUnramifiedTwistStabilizer s hs hindex` to an irreducible
admissible `A`. This finiteness transfer itself requires neither `hp` nor
connected reductivity of `L`.

`rationalUnramifiedTwistOrbitScalarPresentation_exists` additionally takes
`hp`, `hL` and a fraction `f` fixed by every element of `A.obj`'s full twist
stabilizer. It installs the just-proved finiteness and applies the actual
presentation-existence theorem. Thus the generic finiteness premise is
supplied by the already proved central-image theorem, while its exact
finite-index hypothesis and scalar fixedness remain visible.

## Scope and remaining obligations

Arbitrary local-field characteristic is retained, as are independent
field and representation carrier universes. The actual scalar theorems
impose no splitness, quasisplitness, positive rank or characteristic-zero
condition. The more general orbit homeomorphism also keeps its norm-index
and group universes independent.

The final theorem does not construct a central morphism or prove its
finite-index premise. The scalar theorems do not prove stabilizer fixedness
for the scalar extracted from a standard intertwining composite. The
original integral operators, their convergence, rational continuation and
isomorphism naturality, generic induced irreducibility, opposite-parabolic
identification, parabolic independence, nonvanishing and positivity,
source-normalized global `j` and `mu`, measures and the main Plancherel
theorems remain separate obligations.

All topology and density assertions here concern the complex orbit with
the supplied coinduced topology. No density on the unitary locus,
unitary-orbit measure, algebraic quotient identification, or theorem about
all tempered inductions is asserted.
