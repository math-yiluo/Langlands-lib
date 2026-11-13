# Special coordinate formal modules over the actual division order

This module constructs the finite-coordinate special-module objects and their
order-linear isomorphism classes relative to a specified embedded unramified
integer subfield. It uses the actual division-algebra integer ring, formal
power-series actions, derivatives and scalar-kernel ranks. Its provenance is
derived from Drinfeld, *Coverings of p-adic symmetric regions* (1976), section
2 A, printed p.109 (PDF page 3), and the preceding formal-group infrastructure.
The cited original has SHA256
`7dd09e1967f46c29195ec87a400e145a17374368fc3b9dd0a782b5b7bfc44e2f`.

Drinfeld works with a central division algebra of invariant 1/d. He calls a
formal O_D-module special when it has dimension d and the maximal unramified
integer subring acts on its tangent space through d distinct characters at
every geometric point. In the next paragraph he chooses a special framing
module of height d²; the objects in his functor also have height d². Accordingly
this implementation records the special tangent condition and the height
condition separately, then forms a subtype satisfying both.

The construction here applies to any finite-dimensional central division
algebra D over a nonarchimedean local field K, with a supplied K-algebra
embedding ι : L → D of a field L. Set d = `CentralSimple.reducedDegree K D`.
The algebra K → D and its original central integral scalar inclusion are the
ones used in `DivisionOrder`. No Hasse invariant or existence of an unramified
subfield is established here. In particular this is a coordinate ingredient
for the moduli construction, with its explicit unramified-subfield condition,
rather than a construction of the full class of locally glued objects.

`SubfieldIntegerRing K D ι` is the integer ring of the actual restriction to L
of the canonical division valuation. Its O_K-algebra structure comes from the
published `localDivisionSubfieldBaseIntegerMap`. The algebra homomorphism
`subfieldIntegerInclusion` is the integral restriction of ι into
`IntegerRing K D`; its scalar compatibility follows from ι's K-linearity.
`IsUnramifiedSubfieldOfReducedDegree` requires all four actual conditions:
L is finite-dimensional over K; its restricted-valuation integer ring is
finite as an O_K-module; that integer algebra is etale over O_K; and
[L : K] = d. Thus no arbitrary ring or character-label set substitutes for
the embedded integer subring. The finite etale condition is the integral
unramified condition used by this interface. Equivalence with other
valuation-theoretic formulations and independence from the chosen subfield
are not asserted.

`SpecialModule K D ι R`, for a commutative O_K-algebra R, consists of:

- An actual formal O_K-module `ModuleLaw` with coordinate set `Fin d`.
- An actual `OrderAction` of `IntegerRing K D`, extending its original
  O_K-action.
- The preceding condition on the specified embedded field.
- The geometric distinct-character condition for the restriction of the
  actual order action along `subfieldIntegerInclusion`.

The last field uses `HasGeometricTangentCharacters` from `TangentCharacters`.
For every algebraically closed field κ in the fixed test universe and every
ring map R → κ, it requires d injectively indexed ring characters of the
embedded integer ring into κ and a κ-linear coordinate equivalence that
diagonalizes the actual differentiated action with these characters.
Its test universe is `max u v`, where K and D lie in `Type u` and R in
`Type v`; it is not a quantification over all universes simultaneously.
The coordinate tangent space has dimension d over every field, as recorded
by `tangent_finrank`.

`X.HasHeightSquared π` requires that π be irreducible in the actual O_K and
that `X.formalModule.HasPiHeight π q (d^2)` hold, with
q = `Nat.card` of the actual residue field of K. The latter is the affine
point-functor condition of `PiDivisible`: the image of π in R is nilpotent,
every actual point is annihilated by some π-power, multiplication by π
admits lifts along faithfully flat finitely presented algebra maps, and all
π-power kernels have finite projective representing coordinate algebras.
Their stalk ranks must be q^(n*d²) for every n. The module does not merely
attach the number d² to an otherwise unrestricted formal group.
`base_nilpotent`, `scalarPower_rank` and `scalar_height` expose these
consequences, the last giving the rank-based O_K-height of multiplication
by π. Comparison of these affine conditions with a general sheaf-theoretic
p-divisible-group definition remains outside this module.

`SpecialModule.Iso X Y` is the existing actual order-linear formal
isomorphism type. Its forward and reverse maps are formal O_K-module maps
that commute with every integer-order action, and their composites are the
identity formal maps. `Iso.refl`, `Iso.symm` and `Iso.trans` give the
equivalence-relation operations; composition uses the formal composition
associativity and inverse equations. `Iso.hasHeightSquared_iff` follows
from the actual scalar-kernel transport in `PiDivisible` and leaves the
irreducibility condition unchanged.

`isoSetoid` uses existence of such an isomorphism. `HeightSquaredModule π`
is the subtype of special coordinate modules satisfying the height condition;
`heightSquaredIsoSetoid` identifies two of these objects precisely when
there exists an actual order-linear isomorphism between them.
`HeightSquaredClass π` is its quotient. Proofs of height and of tangent
conditions are properties of the objects, not extra isomorphism data.

For an O_K-algebra map θ : R → S with R and S in the same universe,
`mapSameUniverse` maps the coefficients of the formal module and order
action. The unramified-subfield condition is unchanged. Every geometric
S-fibre is the R-fibre for the composite R → S → κ, which transports its
character decomposition. `HasHeightSquared.map` uses
`HasPiHeight.map` from `IsogenyBaseChange`: the scalar-kernel coordinate
algebras are extended by tensor product, stalk ranks pull back, affine
fppf lifts are preserved, and nilpotence and scalar-power torsion persist.
No flatness of θ is required.

`Iso.mapSameUniverse` extends both inverse maps.
`HeightSquaredModule.mapSameUniverse` extends the object with its actual
height certificate. `HeightSquaredClass.mapSameUniverse` descends this
operation to the quotient because extending an order-linear isomorphism
gives an order-linear isomorphism of the extended objects.

These are derived constructions on finite coordinates. The existence of the
chosen embedded unramified field, its relation to the invariant-1/d case and
the maximal-order characterization, arbitrary local coordinate gluing,
the framing object and its rational endomorphism algebra, Drinfeld's triples
and full group action, and representability remain further constructions
or theorem obligations. No representing or universal object is an input.
