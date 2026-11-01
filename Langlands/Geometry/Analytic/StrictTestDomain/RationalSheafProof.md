# The rational algebra presheaf is a sheaf

Author: Worker 74.

`Langlands.Analytic.StrictTestDomain.rationalPresheafIsSheaf.{u}` proves the
unchanged `RationalPresheafSheafStatement.{u}`. For every complete ultrametric
normed field K and presented strict affinoid base P, the actual
`RationalData.rationalPresheaf K P` is a Mathlib commutative K-algebra-valued
sheaf on `RationalData.finiteRationalTopology K P`. The theorem has no finite
gluing or sheaf hypothesis. The companion `rationalSheaf.{u}` proves the
existing conjunction `RationalSheafStatement.{u}`.

The analytic input is the independently published theorem
`Langlands.Analytic.StrictTestDomain.finiteRationalGluing.{u}`, imported from
`Langlands.Geometry.Analytic.StrictTestDomain.FiniteRationalGluingProof`.
It supplies a unique element of a rational target's actual closed-ideal Tate
quotient for every compatible tuple on a finite covering family, including an
empty family. Worker 135 authored this imported relative descent assembly; it
uses the published whole-spectrum theorem and actual comparison maps. The
present proof derives the categorical sheaf property from that theorem.

## Separation from finite gluing

The private conversion works with an explicit finite-gluing premise, discharged
by `finiteRationalGluing` in the closing theorem. For an inclusion `f : c → d`,
the constructed bounded restriction maps `d.algebra` to `c.algebra`.
`restriction_comp_apply` uses the published composition identity for these
actual maps. The rational category has subsingleton morphisms, so the two
composites from an intersection to a common target are equal.

The helper `eq_of_restrictions` proves separation on any finite covering family.
Restrictions of a target section form a compatible tuple by those composition
identities. Finite gluing gives a unique amalgam of that tuple. Two sections
with the same restrictions are both that amalgam and therefore equal.
This argument uses equality of quotient elements themselves.

## Every covering sieve

`rationalUnderlyingIsSheaf` proves the Type-valued sheaf condition for the
presheaf followed by `forget (CommAlgCat K)`. Start with any covering sieve S
on d and any compatible family x indexed by its arrows. By the definition of
the finite rational topology, choose a finite family `f i : D i → d` in S
whose actual loci cover d. Compatibility of x on the intersection arrows gives
exactly the finite-gluing overlap equations. The analytic theorem supplies
`a : d.algebra` restricting to `x (f i)` on every chosen member.

For an arbitrary arrow `g : e → d` in S, the family `e.inter (D i)` covers e.
Indeed, any point of e maps into d by g, hence belongs to some `D i`, and
therefore belongs to that intersection. The two sections `g.restriction a`
and `x g` have equal restrictions to these intersections: restriction
composition compares the first with the chosen-family equations for a, and
compatibility of x supplies the other equality. Applying the separation helper
to this intersection cover gives `g.restriction a = x g`. Thus a is an amalgam
on every arrow of S. Any other amalgam agrees on each chosen `f i`, and the
original finite-gluing uniqueness proves equality with a.

There is no nonemptiness premise on the finite family. If it is empty, the
analytic theorem supplies the unique element of the target quotient. The
intersection family is still a cover of each arrow source, and the same
separation argument applies to its empty tuple. Hence the proof also treats
empty covering sieves and families through actual quotient uniqueness.

## Passage to commutative algebras

The private `rationalPresheafIsSheaf_of_finiteGluing` first uses Mathlib's
`isSheaf_iff_isSheaf_of_type` to express the carrier-valued result in categorical
form. It then applies `Presheaf.isSheaf_iff_isSheaf_forget` to the forgetful
functor from commutative K-algebras to types.

Preservation of limits follows by identifying that forgetful functor with the
composite of the equivalence to commutative rings under K, the under-category
projection, and the commutative-ring carrier functor. Mathlib supplies the
required limits and reflection of isomorphisms. This gives the categorical
sheaf condition for the constructed algebra presheaf and its actual restriction
maps. The closing theorem applies this conversion to the imported analytic
proof; `rationalSheaf` pairs the two established assertions.

## Provenance and scope

The conversion is internal derived category theory. Its analytic setting is
Berkovich, *Non-archimedean analytic spaces*, Trieste lectures (2009), registered
as `berkovich-2009-trieste-analytic-spaces`, SHA256
`8cfe4f6f35d5e717ac67c5c8f5ef9ff9185f460bbe5f9a10aeacd84cddeeb2ca`.
Definition 2.2.1 and Exercise 2.2.2(ii)-(iii), printed/PDF p.9, give rational
domains and intersections; Fact 2.2.6(i), p.10, gives finite-cover Tate
acyclicity; Exercise 3.2.5(ii)-(iii), p.15, describes affinoid functions and the
structural sheaf. These passages were read directly. The proof uses the
published scalar descent theorem rather than assuming any of these analytic
conclusions as a new premise.

All field, finite-index and quotient carriers remain in the target's arbitrary
universe u. Zero and nonreduced quotients, empty numerator tuples and loci, and
trivial valuations retain the target's assumptions. The result concerns the
existing fixed-base finite rational site with unit radii and presented strict
affinoid tests. The full analytic G-topology, higher acyclicity and a locally
ringed space construction are outside its scope. The target pair and every
imported pair are unchanged.
