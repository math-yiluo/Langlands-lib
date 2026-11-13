# Scalar divisibility and finite height over a nilpotent base

This module gives an affine finite-coordinate condition for a formal
O-module over an O-algebra R on which a chosen element π is nilpotent.
Its intended arithmetic specialization takes O to be the integers of a
nonarchimedean local field and π to be a uniformizer. The definitions
themselves allow any commutative O and R. All test R-algebras and finite
kernel coordinate algebras are in the universe of R, as in `FiniteKernel`.

`IsPiPowerTorsion M π` means that every actual nilpotent formal point of M
over every test R-algebra is killed by some π-power. The exponent may
depend on both the algebra and the point. `IsPiDivisible M π` conjoins:

- nilpotence of the image of π in R;
- this pointwise π-power torsion condition;
- the affine fppf local-lifting condition for the actual scalar map [π];
- finite projective algebra corepresentations of the actual kernels of
  [πⁿ], for every nonnegative integer n.

The base nilpotence is explicit. Thus every test R-algebra also has
nilpotent image of π; this is the intended Nilp setting. The predicates
are imposed on the already constructed formal law and its evaluated
point functor, rather than on a supplied abstract divisible group.
In particular, each finite kernel representation must be naturally
equivalent to the actual point kernel.

`HasPiHeight M π q h` adds constant kernel ranks q^(n*h) for every n.
The ranks are the stalk ranks of the finite projective coordinate
modules, independently of the choice of representation. In the
arithmetic specialization q is the residue-field cardinality of O.
Consequently h is O-height; the p-height convention instead uses p as
the rank base for multiplication by p. The interface keeps q explicit
and does not assert that any arbitrary parameter is a residue cardinality.
No height is stored independently from these actual rank conditions.

The scalar laws are proved from the O-module structure on formal Hom.
`Hom.IsFppfLocallySurjective.comp` constructs successive lifts, composes
their faithfully flat finitely presented algebra maps, and uses
naturality of evaluation to check the lift equation. Iterating this
argument shows that an `IsPiDivisible` law has isogenies [πⁿ] for all n.
A `HasPiHeight` law gives those isogenies height n*h; in particular [π]
has height h. Height uniqueness assumes R nontrivial and q at least two
and uses uniqueness of the actual π-kernel rank.

Every O-linear isomorphism commutes with the scalar maps. Its actual
point equivalence preserves pointwise scalar-power torsion. Applying
the kernel and lifting transport constructions of `KernelTransport` to
these scalar squares proves `Iso.isPiDivisible_iff` and
`Iso.hasPiHeight_iff`. These statements allow the conditions to descend
through isomorphism classes of coordinate presentations.

The provenance is a derived affine formulation. Rapoport–Zink,
*Period Spaces for p-divisible Groups* (1996), printed p.51, Definition
2.6, the following height paragraph and the remarks after Proposition
2.7, supply the finite locally free kernel, fppf epimorphism,
rank-based height and multiplication-by-p isogeny conditions.
Drinfeld, *Coverings of p-adic Symmetric Regions* (1976), §1, printed
p.108, fixes q as the residue cardinality and a prime element π; §2 A,
printed p.109, uses height d² for the special formal O_D-modules in
the moduli problem. Here the formula q^(n*h) fixes the O-height
normalization explicitly.

This module neither constructs an example of a finite-height law nor
proves equivalence with a scheme-level or fppf-sheaf definition of a
π-divisible group. It does not prove that all scalar-power ranks follow
from the first rank condition, base-change preservation of finite
kernel representations, height additivity for general isogenies,
quasi-isogeny heights, local gluing, rigidity, or moduli representability.
