# Finite locally free kernels and rank-based isogeny heights

Let f be a homomorphism between finite-coordinate formal O-modules over
a commutative O-algebra R. `Hom.kernelSetFunctor` is the underlying set
functor of the actual kernel on nilpotent formal points, on commutative
R-algebras in the universe of R.

`Hom.FiniteKernelModel f` consists of a commutative R-algebra C, finite
and projective as an R-module, and a natural family of bijections
between R-algebra maps C → A and actual points killed by f in A.
Thus the coordinate algebra must represent the constructed kernel
functor. `HasFiniteLocallyFreeKernel` asserts the existence of such a
representation; it does not choose or assume a universal object for the
moduli problem.

`FiniteKernelModel.coordinateIso` uses uniqueness of corepresenting
objects to identify any two such coordinate algebras. Their `rank`
functions are the ranks of the localized coordinate modules on Spec R.
`rank_eq` proves independence from the representation by the induced
R-linear equivalence and invariance of stalk ranks. Finite projectivity
implies finite presentation and flatness, so Mathlib's stalk-rank theorem
proves `isLocallyConstant_rank`.

`HasKernelRank f n` means that the actual kernel has constant rank n.
The equivalence `hasKernelRank_iff` allows this condition to be checked
on any finite kernel representation. The rank is unique when R is
nontrivial, by evaluation at a prime ideal. This nontriviality
hypothesis is necessary: the empty spectrum cannot distinguish
constant rank values.

`IsFppfLocallySurjective` states the explicit affine local-lifting
condition: every point over A lifts after an R-algebra map A → B
which is faithfully flat and finitely presented. `IsIsogeny` is the
conjunction of this condition and a finite locally free represented
kernel. This module uses the affine lifting formulation directly;
it does not construct the formal-point functors as fppf sheaf objects
or prove a comparison with a categorical sheaf epimorphism.

`HasHeight f q h` asserts the isogeny condition and constant kernel
rank q^h. It is a proposition derived from the actual kernel, with no
independent height field. For R nontrivial and q at least two,
`HasHeight.unique` follows from uniqueness of kernel rank and
injectivity of powers of q. With the p-divisible group normalization,
q is p; with the formal O-module normalization, q is the residue
cardinality. The predicates here do not assert that every isogeny has
power-of-q kernel rank or a globally constant height.

The source is Rapoport–Zink, *Period Spaces for p-divisible Groups*
(1996), Definition 2.6 and the following height paragraph, printed p.51.
It defines isogenies of p-divisible groups by fppf epimorphy and finite
locally free kernels, and defines height h when the kernel rank is
constant p^h. The present finite-coordinate formal-module interface is
derived from those conditions. No p-divisibility, scalar-isogeny
existence, quasi-isogeny height, height additivity, gluing, rigidity or
moduli representability theorem is asserted here.
