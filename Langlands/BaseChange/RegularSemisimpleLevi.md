# A proper two-block Levi for a nonelliptic regular semisimple element

A monic factorization of the separable characteristic polynomial gives two
complementary invariant subspaces, the kernels of the two polynomial evaluations.
Cayley–Hamilton makes their sum the whole space, and coprimality makes the sum
direct. Each restriction has a separable characteristic polynomial because their
product is the original characteristic polynomial. Over the algebraic closure,
each root of a restriction's characteristic polynomial is an eigenvalue and
therefore a root of its annihilating factor. Separability makes the root multiset
have no repetitions, so the characteristic polynomial divides that factor. The
product identity and the degree sums give equality of each characteristic
polynomial with its factor.

Bases of the two kernels give the change-of-basis matrix and the two invertible
diagonal blocks in the Library's standard `twoBlock` coordinates. A monic
irreducible factor of a nonelliptic regular semisimple characteristic polynomial
makes the first block regular elliptic. The complementary block has positive
rank, has separable characteristic polynomial, and has characteristic polynomial
coprime to that of the first block. This is the algebraic step in parabolic descent
in Arthur–Clozel (1989), Chapter 1, Theorem 4.5, and Henniart–Lemaire (2011), I.6.6.
Taking a single irreducible factor and keeping the complementary factor together
permits induction with the two-block parabolics.
