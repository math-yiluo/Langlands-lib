# Deligne-torus points and the scalar-extended Shimura homomorphism

Author: Worker 57.

This module constructs the functor of points of the Deligne torus on
commutative real algebras, identifies its quadratic coordinates with the
actual scalar extension of the complex numbers, and extends the published
compatible complex algebra homomorphisms to natural homomorphisms into the
unitary-similitude functor. It also implements Kottwitz's inverse convention.

## Source and conventions

Kottwitz (1992), Section 1, printed p.654 (PDF p.2), specifies a real algebra
homomorphism `h₀ : ℂ → D ⊗ ℝ` compatible with the algebra involution and
complex conjugation. The involution twisted by `h₀(i)` must be positive.
Kottwitz then uses the inverse of the restriction of `h₀` to complex units
as the homomorphism from `Res_{ℂ/ℝ} Gₘ` into the real similitude group.
The source subsequently extends `h₀` by scalars to describe the reflex field.

The existing `AlgebraInvolution.ComplexHom` records the algebra map and
involution compatibility. The present construction needs precisely those
fields; positivity is not necessary to construct the map into similitudes.
The imported `Positivity` module supplies the positivity result for its
specific `kottwitzHom`. Kottwitz's inverse convention and the direct
extension of a `ComplexHom` are given separate definitions below.

Harris (1998), Erratum, printed pp.180–182 (PDF pp.4–6), replaces the
original Harris complex homomorphism by its complex conjugate. The
published `harrisArchimedeanHom` incorporates that correction, and
`kottwitzHom` is its precomposition with conjugation. This module reuses
those exact maps. In particular, `harrisDeligneHom` and
`kottwitzDeligneHom` are not asserted to be equal.

Both cited passages were read in the original. The quadratic presentation,
tensor equivalence and naturality proofs here are derived algebraic
constructions, rather than claims that these implementation details are
spelled out in either source.

## Quadratic and tensor models

For a commutative ring `S`, `DeligneTorus.Complexification S` is Mathlib's
`QuadraticAlgebra S (-1) 0`. Its elements are pairs `a + b i`, with
`i² = -1`. `map f` applies a ring homomorphism to both coordinates.
`Points S` is its actual group of units. `norm S` maps these units to `Sˣ`
using the quadratic norm `a² + b²`. The construction works for arbitrary
commutative rings, including rings with nilpotents; a field or reducedness
hypothesis is not introduced.

On commutative real algebras, `functor` bundles these groups and their
coefficient maps as `CommAlgCat ℝ ⥤ GrpCat`. The identity and composition
laws are proved on the unit coordinates. `norm_map` and `norm_natural`
prove compatibility of the norm with coefficient change. `inversion` is a
natural endomorphism of this group functor, using commutativity of its
point groups.

For a real algebra `S`, `complexMap S` sends `i` to the quadratic
generator. Its real and imaginary coordinates are the images under
`algebraMap ℝ S`; `norm_complexMap` identifies its norm with the image of
`Complex.normSq`.

`fromTensor S` sends `s ⊗ z` to `s • complexMap S z`.
`toTensor S` sends `a + b i` to `a ⊗ 1 + b ⊗ i`.
`tensorEquiv S` proves that these are inverse `S`-algebra maps:

`Complexification S ≃ₐ[S] S ⊗[ℝ] ℂ`.

The proof uses the tensor-product universal property in one direction and
extensionality on the quadratic generator in the other. The generator
relation follows from `i² = -1` and bilinearity.
`toTensor_natural` proves compatibility with the actual tensor coefficient
map. Thus both the objects and the arrows agree with the scalar-extension
unit functor defining restriction of scalars.

`realEquiv` composes this equivalence at `S = ℝ` with the tensor left-unit
equivalence. `realEquiv_complexMap` proves it inverts the included complex
scalars. `realPointsEquiv` is the resulting group equivalence with `ℂˣ`.

## The homomorphism into similitudes

For `h : AlgebraInvolution.ComplexHom σ`, `h.deligneAlgebraMap S` is the
`S`-algebra map

`a + b i ↦ a ⊗ 1 + b ⊗ h.hom i`.

Its construction verifies the generator relation using the multiplicativity
of `h.hom`. `deligneAlgebraMap_star` proves compatibility of quadratic
conjugation with `σ.baseChange S`. The proof expands the two coordinates
and applies `h.star_compatible` to `i`.

`h.delignePoints S` sends a quadratic unit `z` to the pair consisting of
its image under this algebra map and `norm S z`. Membership in the
similitude group follows from the quadratic identity
`z * star z = algebraMap S _ (norm z)`, transported by the algebra map.
This proves the multiplier equation; it is not an assumed field.
`delignePoints_multiplier` records the resulting exact norm multiplier.

`deligneAlgebraMap_natural` proves compatibility with coefficient change
by the displayed coordinate formula. Together with `norm_map`, it gives
`h.deligneHom`, a natural transformation from `DeligneTorus.functor` to
`σ.similitudeFunctor`. Its components are group homomorphisms.

`h.inverseDeligneHom` precomposes with `DeligneTorus.inversion`.
`inverseDeligneHom_multiplier` proves that its multiplier is the inverse
norm. `harrisDeligneHom` applies the direct construction to the corrected
Harris map. `kottwitzDeligneHom` applies the inverse construction to the
published `kottwitzHom`, exactly retaining Kottwitz's inverse-of-`h₀`
convention.

`deligneAlgebraMap_complexMap` proves that included complex scalars map
to `1 ⊗ h.hom z`. Consequently `delignePoints_real_underlying` and
`delignePoints_real_multiplier` recover both coordinates of the previously
published `h.toSimilitudes` on every complex unit, after identifying
`ℝ ⊗[ℝ] A` with `A` on the underlying unit coordinate. The underlying-unit
identification is explicit; the two differently typed similitude groups
are not equated by notation.

## Scope and provenance

This is a construction of group functors and a natural transformation on
all commutative real algebras. It does not construct an affine scheme
representing the Deligne torus, prove the torus axioms, or construct the
Shimura varieties. Those geometric steps remain required in the host task.
The construction also does not supply a global algebra's archimedean
splitting, new positivity or Hodge axioms, a moduli functor, or level schemes.

Formal dependencies are the published `Unitary.Positivity`,
`Unitary.Domain`, `Unitary.Similitude`, and `Unitary.Involution` modules,
and Mathlib's quadratic-algebra, complex-lift, tensor-product and units
APIs. No new axiom or unfinished proof is introduced.

Sources:

- Kottwitz, *On the lambda-adic representations associated to some simple
  Shimura varieties* (1992), Section 1, p.654 (PDF p.2).
  Source ID `kottwitz-1992-lambda-adic-simple-shimura`, SHA-256
  `749af5541a59187e6f9d1089dec9a0e591a2059173da739c7384ff3a7d0dd799`.
- Harris, *The local Langlands conjecture for GL(n) over a p-adic field,
  n < p* (1998), Erratum, pp.180–182 (PDF pp.4–6).
  Source ID `harris-1998-local-langlands`, SHA-256
  `7934239ea37d0b91f741ae70c2ac157fe5d619cda4dd992ac24e39ae460c375b`.
