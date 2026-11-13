# Isomorphisms and classes of Deligne's four sheaf data

This module constructs actual categories of graded lattice sheaves,
framed lattice sheaves and preliminary eta,T,u,r data, followed by their
isomorphism classes and the classes of admissible objects on each Nilp algebra.
It is derived infrastructure for the four-data definition in Drinfeld 1976,
Section 2 A, printed pp.109–110 (PDF pp.3–4), the final paragraph of
p.109 and conditions (a)–(c) at the opening of p.110. The registered source is
`drinfeld-1976-coverings-p-adic-symmetric-regions`, SHA256
`7dd09e1967f46c29195ec87a400e145a17374368fc3b9dd0a782b5b7bfc44e2f`.

The parameters are a commutative ring O, a positive integer d, an O-algebra
field F, a scheme S and a ring map from O to the actual global sections of S.
They use the common universe of the preceding sheaf constructions. In the
lattice-only constructions the base can be an arbitrary topological space X.
F need not be the fraction field of O. Admissible objects additionally require
that the image of pi in F is nonzero.

## Graded lattice morphisms

`latticeScalarFunctor` is actual restriction of scalars from O[Pi] to O.
`latticePi_naturality` proves that every coefficient-linear sheaf map
commutes with the distinguished Pi action, by sectionwise scalar linearity.

`LatticePiSheaf.Hom` consists of an O[Pi]-linear map of the total sheaves,
an O-linear map of each actual homogeneous component, and commutativity
with the actual homogeneous inclusions. Identity and composition give a
category. `totalFunctor` and `componentFunctor` retain the total sheaf and
each homogeneous component, respectively. Consequently an isomorphism in
this category induces genuine isomorphisms of all these sheaves.

`Hom.ext_total` proves that the component maps are determined by the total
map: compose with the target's monomorphic inclusion and use the two
inclusion squares. `Hom.pi_naturality` proves that the same component maps
commute with the degree-one operators. It composes with the inclusion of
degree i+1, uses the constructed total Pi naturality and both Pi-inclusion
squares, and cancels the monomorphism. No unrelated operator map is supplied.

## Framed morphisms

`FramedLatticePiSheaf.Hom` retains a lattice morphism and requires

    r_M ; rationalize(f_0) = r_N.

Here rationalization is the actual scalar-extension and sheafification
functor already constructed. This equation uses the full given frame from
the constant F^d sheaf to the rationalized degree-zero lattice.
The category identities and compositions follow the identity and
composition laws of that functor. `latticeFunctor` forgets the frame.
An isomorphism therefore retains both the actual grading and r.

## Morphisms of all four data

`SheafPreDatum.Hom` consists of a framed eta morphism, a degree-preserving
Pi-compatible structural-module morphism of T, and the square

    restrict(f_eta) ; u_E = u_D ; restrict(f_T).

The first restriction forgets O[Pi] to O. The second forgets the
structure-sheaf scalars using the given global O-map. Thus this square
uses the same total u as the preliminary data.

`structuralComponentInclusion_mono` proves that structural scalar restriction
preserves injectivity of each actual homogeneous inclusion, using the
subtype inclusions on sections. `Hom.uComponent_naturality` then proves
that the total square also preserves the given homogeneous restrictions
of u. Its proof composes with that target inclusion, rewrites the two
u-component squares, the eta inclusion square and the total u square,
then uses the T component-inclusion square and cancels the monomorphism.
No extra compatibility condition on independently chosen component maps
is needed.

The identity and composition squares define the category of preliminary
four-data objects. Its `etaFunctor` retains the framed lattice, and its
`tangentFunctor` retains the actual graded structural Pi sheaf.
`piZeroLocus_eq_of_iso` uses the latter functor and the existing invariance
under genuine graded isomorphisms to identify the actual zero loci.
Categorical isomorphisms supply inverse morphisms satisfying the same
conditions; invertibility is not replaced by a proposition on bare data.

## Classes on a scheme and on Nilp algebras

`SheafPreDatum.isoSetoid` relates two preliminary objects precisely when a
categorical isomorphism between them exists. Reflexivity, symmetry and
transitivity use the actual identity, inverse and composite isomorphisms.
`SheafPreDatum.IsoClass` is the quotient by that equivalence relation.
Its constructor `mk` and theorem `mk_eq_mk_iff` identify equality of classes
with existence of a genuine isomorphism.

`SheafDatum` is the subtype of preliminary data satisfying the existing
`Admissible` predicate. `SheafDatum.isoSetoid` uses the same isomorphism
relation on the underlying four data; its equivalence laws require no
chosen trivializations and ignore proofs of admissibility.
`SheafDatum.IsoClass` is its quotient, with the same constructor and exact
equality criterion. `toPreliminary` is the well-defined map that forgets
admissibility on classes and retains all four underlying data.

`NilpSheafIsoClass` specializes the latter quotient to S = Spec B and
the actual `nilpGlobalScalar` of each `FormalGroup.Nilp O pi` algebra B.
This is a construction of classes for each such algebra. Maps associated
to algebra homomorphisms, functorial base change and representability are
not constructed here.

The admissibility subtype retains the preceding determinant predicate's
documented scope: its normalization is stalkwise, and comparison with an
independently constructed exterior-power subsheaf equality remains unproved.
The module does not prove invariance of the entire admissibility predicate
under arbitrary isomorphisms, existence of admissible objects, or identification
with a separately defined Deligne moduli functor. The quotient is nevertheless
an actual equivalence-relation quotient on the subtype of objects satisfying
that predicate. A normalized PGL action, a representing formal scheme and its
generic fibre remain outside this unit.
