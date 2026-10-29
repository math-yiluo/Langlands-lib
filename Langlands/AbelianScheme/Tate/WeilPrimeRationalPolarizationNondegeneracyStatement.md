# Geometric-point nondegeneracy of rational prime-adic polarization pairings

`PrimeRationalPolarizationWeilNondegeneracyStatement` states
nondegeneracy of the existing rational prime-adic Weil pairing pulled
back in its second variable by an actual relative polarization.
It is a proposition definition and has no proof in this file.

The base is a quasi-separated scheme S, and A is an actual abelian
scheme over S. The inputs retain the chosen dual scheme, its geometry,
the inverse Poincare line bundle and its evaluation, and the explicit
tensor and Picard propositions used in their constructors.
The square and universal-base-change propositions enter the existing
`IsPolarization` predicate. That predicate requires `lam` to be an
isogeny and to have an ample Mumford presentation on every geometric
fibre after a possible extension of that fibre's field.

The test object is specifically `Over.mk s`, where
`s : Spec (CommRingCat.of K) ⟶ S` and K is algebraically closed.
The prime p is expressed by `Fact p.Prime`, and `(p : K) ≠ 0`
excludes the characteristic of the point field. It does not require
p to be invertible everywhere on S. The assertion concerns the actual
torsion points over this geometric point; it does not assert
nondegeneracy on arbitrary test schemes.

The map in the conclusion is exactly
`primeRationalWeilAlongHomBilinearMap`, with both inputs equal to
`GroupScheme.Tate.PrimeAdic.Rational A.toGrp (Over.mk s) p`.
This is Q_p tensor over Z_p with the actual integral prime-adic Tate
module. The output is
`TateTwist.Rational Γ((Spec (CommRingCat.of K)), ⊤) p`,
the rationalization of the constructed inverse limit of roots of
unity. The convention remains beta(lam(y))(x). No roots of unity,
twist basis, arbitrary pairing, or comparison isometry are supplied.

Mathlib's `LinearMap.Nondegenerate` means that both radicals vanish:
an x whose pairing with every y is zero must be zero, and a y whose
pairing with every x is zero must be zero. The target may be the
actual twist module; this predicate does not require a scalar-valued
form. It does not itself assert a linear equivalence with a dual,
finite-dimensionality, or perfectness of an integral pairing.

`RelativeFiniteWeilTransitionStatement` remains an explicit theorem
hypothesis needed to form the inverse-limit pairing.
No finite alternation or nondegeneracy proposition is assumed.

The provenance is derived from Edixhoven, van der Geer and Moonen,
*Abelian Varieties*, preliminary draft built 2012-02-08, registered as
`edixhoven-vandergeer-moonen-abelian-varieties-draft`, SHA256
`81e88e484e1e830286ffed93d4636c80e50a1c341ffe19cc198bd856be713b42`:

- Chapter X, Proposition (10.6) and Corollary (10.7), printed p.144,
  PDF p.148, show that an isogeny induces an isomorphism on the rational
  prime-adic Tate modules when the prime differs from the
  characteristic.
- Chapter XI, Definition (11.11) and its following discussion, printed
  pp.162–163, PDF pp.166–167, define the convention beta(y)(x) and
  its pullback by a polarization. The finite polarization pairing is
  perfect when its order is coprime to the degree of the polarization.
- Chapter XI, (11.23), printed p.168, PDF p.172, constructs the perfect
  integral pairing between the Tate modules of an abelian variety
  and its dual, with values in Z_p(1).

Over a field, rationalizing that unpulled perfect pairing and using
the rational invertibility of the polarization gives the proposed
nondegeneracy. The exact Lean target also requires comparison of
the relative Poincare-derived pairing evaluated at s with the
pairing on the geometric fibre, including dual and Tate-module
base change. Those identifications are part of the proof obligation;
the field literature is not claimed to have proved them for the
Library constructors. A separate proof task must establish this
exact target or publish and prove its needed prerequisites.

The statement adds no axiom and proves no nondegeneracy theorem.
It claims no integral perfectness for a nonprincipal polarization,
no assertion at the characteristic prime, and no adelic or full
rational nondegeneracy beyond this prime-adic target.
