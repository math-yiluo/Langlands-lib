# The cotangent sheaf of an abelian scheme under translation

On the self-product \(A\times_S A\), the sheaf of differentials relative
to the second projection is the pullback of \(\Omega^1_{A/S}\) along the
first projection. Pulling it back along \(y\mapsto(e,y)\) therefore gives
the pullback to \(A\) of the cotangent sheaf at the identity. The
automorphism \((x,y)\mapsto(x+y,y)\) is over the second projection and
carries this section to the diagonal. The induced relative differential
map is an isomorphism by the comparison for open immersions, applied to
an isomorphism and the identity of the second factor. Pullback along the
diagonal gives \(\Omega^1_{A/S}\) itself by base change and the first
projection identity.

`relativeDifferentialsIsoPullbackCotangent` composes these isomorphisms on
actual sheaves of modules. This is the translation argument underlying the
identification of invariant one-forms with the cotangent module at the
identity in Kai-Wen Lan, *Arithmetic compactifications of PEL-type Shimura
varieties*, revised 14 March 2021, §2.1.6, printed p. 135. The retained
source is `lan-2008-pel-thesis-revision-2021`, SHA-256
`a7a454f5d0735f4bf11f00a8afc14c361c5fc2cefd691d7466f7620ab4c3a079`.

`exists_finiteFreeRelativeDifferentials` specializes to an abelian scheme
over the spectrum of a commutative local ring. Smoothness gives locally
finite free cotangent frames at the identity. Choose the frame on the open
containing the closed point. Every point specializes to the closed point,
so this open is the whole base. The proof carries the resulting free
sheaf isomorphism from the slice site to the whole scheme, pulls it back
to the abelian scheme, and uses `relativeDifferentialsIsoPullbackCotangent`.
It gives a finite free frame of the actual differential sheaf.
