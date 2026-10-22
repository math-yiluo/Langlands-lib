# Normalized Jacquet modules and evaluation reciprocity

Author: Worker 8. This pair imports the independently published
`Langlands.Representation.Parabolic.LeviBridges` construction.

Fix a prime `p`, a finite extension `F : PadicField p`, a compatible
topological realization `T`, and an ordered positive block shape `B` of
rank `n`. Write `G = GL_n(F)`, `P = B.parabolic F.Carrier`,
`M = B.Levi F.Carrier`, and `N = B.unipotentRadical F.Carrier`.
These are actual matrix groups, their actual product Levi and radical.
The topology everywhere comes from `T.topology`. The field and the three
complex representation carriers have independent universes. The carriers
have no topology and need not be finite-dimensional.

## Constructions and normalization

For a `G`-representation `rho`, `leviCoinvariants B (rho.comp P.subtype)`
is the actual relation quotient by the span of `rho(u)v-v`, for `u` in `N`.
The Levi acts by `m[v] = [rho(s(m))v]`, using the constructed section
`s : M -> P`. No arbitrary quotient, functor or theorem field is input.

The normalized action in this pair is exactly

`twist (Jacquet.inverseHalfCharacter (T.leviModulus B)) (leviCoinvariants B (rho.comp P.subtype))`.

The full positive modulus is the published explicit block formula

`delta_B(m) = product_(i<j) |det m_i|_F^(n_j) / |det m_j|_F^(n_i)`.

The determinant norms have the residue normalization `q^(-valuation)`.
The character used on the Jacquet quotient is the complex image of the
inverse positive square root. Thus the normalized action on a class is
`m[v] = delta_B(m)^(-1/2) [rho(s(m))v]`.
`inverseHalf_leviModulus` identifies this character with the inverse of
the positive induction half. Its open kernel is a proved construction
property. Writing this twist on the product-Levi quotient reuses the
existing quotient and character constructions and defines no new functor.

The full block product is mathematically the absolute determinant of
conjugation on the upper radical Lie algebra: each rectangular block
`X_ij` transforms as `m_i X_ij m_j^(-1)` and contributes the displayed
factor. Its formal determinant or Haar-scaling identification remains a
separate proof obligation. The target specifies the explicit product and
does not assume an identification theorem as a hypothesis.

## Four assertions

`NormalizedJacquetSmoothnessClause` says that a smooth ambient
representation has a smooth normalized Jacquet representation of `M`.
`NormalizedJacquetAdmissibilityClause` strengthens the conclusion to
admissibility for admissible input. The imported admissibility convention
includes smoothness and finite-dimensional fixed spaces for all open
subgroups.

`NormalizedJacquetExactnessClause` starts with actual intertwiners
`i : rho -> sigma` and `q : sigma -> tau` in a short exact sequence of
smooth `G`-representations. It restricts each to `P`, applies the actual
`leviCoinvariantsMap`, and twists both sides by the same inverse
half-character using `twistIntertwining`. These are actual normalized Levi
intertwiners, with formulas `[v] -> [i(v)]` and `[v] -> [q(v)]`.
The conclusion is injectivity, equality of linear image and kernel, and
surjectivity of these specific maps. There is no finite-length,
admissibility or compact-exhaustion assumption.

`NormalizedFrobeniusClause` gives the complex linear equivalence

`Hom_G(rho, normalizedInd_P^G(sigma)) = Hom_M(normalizedJ_N(rho), sigma)`

for smooth `rho` and `sigma`. Its forward value is prescribed on every
quotient representative by `[v] -> f(v)(1)`. Induction uses the actual
smooth right-translation function space for the inflation of `sigma`,
twisted by the positive `T.parabolicHalfModulus B`. Thus the source
covariance and quotient normalization match, rather than leaving two
unrelated character parameters.

`Langlands.Parabolic.NormalizedJacquetStatement` is the conjunction of
these four proposition definitions. Their theorem proofs are separate.

## Original sources and scope

Bernstein--Zelevinsky, *Induced representations of reductive p-adic groups I*
(1977), Sections 1.8-1.9, printed pp.444-445 / PDF pp.5-6, constructs the
normalized smooth functors and states exactness and adjointness.
Sections 2.1-2.3, printed p.446 / PDF p.7, specializes them to reductive
parabolic triples, gives the ordered-block example for `GL_n`, and states
parabolic exactness, adjointness and preservation of admissibility.
The original passages were read. Their actual function and relation
quotient conventions are the ones spelled out above.

Casselman, *Introduction to admissible representations of p-adic groups*,
Chapter III, revision April 29, 2019, supplies complementary original
locators: Section 3, pp.3-4, describes the quotient and its universal
property (III.3.2), proves exactness (III.3.4), and introduces the inverse
half normalization immediately before evaluation reciprocity (III.3.5).
Theorem III.5.6, p.7, states admissibility of the Jacquet module under the
explicit field restriction immediately before III.5.5. The warning after
III.5.7 about an erroneous general-Noetherian-ring argument is respected:
all coefficients here are complex. Original pp.1-4 and 7-8 were read;
the retained earlier visual checks distinguish the half powers and
opposite-radical notation.

These assertions are documented specializations to actual `GL_n` blocks
over finite extensions of `Q_p`. They make no equal-characteristic or
general-reductive claim. The empty rank-zero block shape is allowed and
reduces to the trivial-group identity constructions.

Registered sources:

- `bernstein-zelevinsky-1977-induced-i`, SHA256
  `8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`,
  Sections 1.8-1.9, pp.444-445, and Sections 2.1-2.3, p.446.
- `casselman-2019-jacquet-module`, SHA256
  `377edac998669bc88da1224c4582a173854232f7fea5caf945d140ee92fde5c1`,
  Section 3, pp.3-4, and field restriction and III.5.6/III.5.7 warning, p.7.

## Dependencies and remaining obligations

The imported `Group.GL.BlockModulus` and `Representation.Induction.Definitions`
and the algebraic `Parabolic.LeviBridges` pair are published. The bridge's
intrinsic quotient and map laws are proved. This pair states exactness as
a conclusion; it does not assume that theorem.

Formal modulus identification, the four theorem proofs, normalized
refinement transitivity, twist and central-character compatibilities,
opposite-parabolic duality and the canonical pairing remain separate
obligations. In particular the ordinary Jacquet quotient of the smooth
dual is not asserted to be the dual of the same-parabolic quotient.
