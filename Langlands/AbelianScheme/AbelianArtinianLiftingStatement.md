# Abelian-scheme lifts over elementary local Artinian extensions

`Langlands.AbelianScheme.AbelianArtinianLiftingStatement.{u}` concerns a
surjection \(\varphi\colon R'\to R\) of commutative local Artinian rings in
an arbitrary universe \(u\), with \(R'\) a \(\mathbf Q\)-algebra. It assumes
that the maximal ideal of \(R'\) annihilates \(I=\ker\varphi\), so \(I\)
is square-zero and the rings have a common residue field \(k\).

For every abelian scheme \(B\) over \(\operatorname{Spec} R\), the
proposition asserts existence of an abelian scheme \(B'\) over
\(\operatorname{Spec} R'\) and an isomorphism
\(B'\times_{\operatorname{Spec} R'}\operatorname{Spec} R\simeq B\) in the
category of abelian schemes over \(\operatorname{Spec} R\).
`AbelianScheme.baseChange` along `Spec.map (CommRingCat.ofHom φ)` supplies
this pullback. Restricting the isomorphism to the common special fibre
transports any marking on \(B_k\). This is the abelian-scheme step of
polarized deformation theory, before lifting a polarization or an
endomorphism action.

## Source comparison

In Kai-Wen Lan's *Arithmetic compactifications of PEL-type Shimura
varieties*, Harvard thesis revised 14 March 2021, Definition 2.2.1.1
(p. 142, PDF p. 170) gives the same kernel-annihilation condition for a
small surjection. Proposition 2.2.4.1 (pp. 152–154, PDF pp. 180–182)
proves formal smoothness of the marked abelian-scheme deformation functor.
In that setup one can mark \(B\) by the identity of \(B_k\). A lift of its
marked class then provides an abelian-scheme isomorphism over \(R\).
The retained source is `lan-2008-pel-thesis-revision-2021`, SHA-256
`a7a454f5d0735f4bf11f00a8afc14c361c5fc2cefd691d7466f7620ab4c3a079`.

Lan fixes the residue field using a finite extension of the residue
field of a finite-type point of the PEL base (p. 140, PDF p. 168).
The Lean proposition ranges over arbitrary characteristic-zero residue
fields and takes the rings and the abelian scheme as given. Formal
smoothness of \(k/\mathbf Q\) gives a coefficient-field section of
\(R'\twoheadrightarrow k\), whose composite with \(\varphi\) gives a
compatible section in \(R\).

Lan forms the scheme-lifting obstruction in
\(H^2(B_k,T_{B_k/k})\otimes_k I\) using smooth affine lifts. A proof by
this route for arbitrary \(k\) requires the obstruction calculation
on the product and its compatibility with the group-law automorphism
and the two axis restrictions in that scope. Once a smooth scheme lift
exists, smoothness lifts the identity section. Propositions 2.2.2.3 and
2.2.2.5 (pp. 144–147, PDF pp. 172–175) relate such a lift to a lift as an
abelian scheme.

The Library's `artinianH2PrimitiveInjectivity` concerns ideal cohomology
on an abelian scheme already defined over the thicker ring. The
scheme-lifting obstruction above is defined before such a scheme is
available. [Ideal-cohomology injectivity](../AlgebraicGeometry/Picard/ArtinianH2PrimitiveInjectivityProof.md)
