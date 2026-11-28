# Realizing a lifted Hodge summand by a marked abelian scheme

Let `A` be an abelian scheme over a commutative local Artinian rational
algebra `R`. Suppose `I` is a square-zero ideal killed by the maximal ideal.
For a supplied finite affine cover `U`, let `M` be a submodule of the actual
affine Čech–de Rham `H1`. The submodule and its quotient are finite free.
Its image in `H1 / I H1` equals the image of the first Hodge step.

`ArtinianHodgeSummandRealizationStatement` asks for an actual abelian scheme
`B` over `R`, an isomorphism from its actual reduction to the reduction of
`A`, and a finite affine cover `V` of `B` with a bijection of indices to `U`.
The covering opens on reduction correspond under the marking. The
corrected degree-one pullback along the marking is bijective and the
inverse image of `hodgeF1` for `B` is `M`.

Kai-Wen Lan, *Arithmetic compactifications of PEL-type Shimura varieties*,
revised 14 March 2021, Proposition 2.1.6.8, printed p. 136 (PDF p. 164),
classifies liftings by lifted projective summands in degree-one de Rham
homology. Dualizing the locally free Hodge sequence gives the
cohomological formulation here. The equation modulo `I H1` expresses the
same reduced summand once degree-one base change is identified. On a local
Artinian base, finite projective modules are finite free. The statement uses
the actual affine complexes, an actual marked abelian scheme, and the
existence direction of the correspondence for square-zero ideals killed by
the maximal ideal. The use of matching affine opens expresses the local
gluing model used in §2.1.3 and §2.1.6.

The retained source is `lan-2008-pel-thesis-revision-2021`, SHA-256
`a7a454f5d0735f4bf11f00a8afc14c361c5fc2cefd691d7466f7620ab4c3a079`.
