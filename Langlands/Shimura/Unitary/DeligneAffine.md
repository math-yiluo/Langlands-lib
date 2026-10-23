# Affine realization of the Deligne-to-similitude map

Author: Worker 57.

This module constructs a real algebra map from the explicit similitude
coordinate algebra to the Deligne-torus coordinate algebra, then applies
`Spec` to obtain an actual morphism of affine real schemes. Its effect on
the represented points is proved to be the previously constructed natural
homomorphism into similitudes. It treats the direct and inverse conventions
separately and specializes both to the concrete Harris archimedean algebra.

## Source and derivation

Kottwitz (1992), Section 1, printed p.654 (PDF p.2), specifies a compatible
real algebra homomorphism `h₀ : ℂ → D ⊗ ℝ` and takes the inverse of its
restriction to complex units to define the map from `Res_{ℂ/ℝ} Gₘ` to the
real similitude group. The existing `ComplexHom.deligneHom` and
`inverseDeligneHom` implement the direct and inverse natural maps on all
commutative real algebras. The present module realizes these maps on the
spectra of the explicit representing coordinate algebras.

Harris (1998), Erratum, printed pp.180–182 (PDF pp.4–6), corrects the earlier
complex homomorphism to its conjugate convention. The imported
`harrisArchimedeanHom` retains that correction, and `kottwitzHom` is its
precomposition with conjugation, as documented in `Positivity` and
`Deligne`. The final two scheme maps reuse these exact definitions. No
equality between the direct Harris and inverse Kottwitz maps is asserted.
Both original passages were read.

The implementation is a derived construction using the representing
algebras. The cohomomorphism is the classifying map of the image of a
universal point. Its naturality proof identifies every specialization,
and the contravariant spectrum functor gives the scheme morphism. These
coordinate details are not attributed to the originals.

## Inversion on the source

`DeligneTorus.point_id` identifies specialization by the identity algebra
map with the universal quadratic unit.
`inversionComorphism` classifies the inverse of that universal unit.
`point_inversionComorphism` proves that precomposing a point's algebra map
with it inverts the point. The proof uses naturality of specialization,
the classifying-map inverse equation, and preservation of inverses by a
monoid homomorphism. `inversionComorphism_comp` proves that applying this
algebra map twice gives the identity, using injectivity of the representing
equivalence. `inversionSchemeMap` is its actual spectrum morphism.

## The target and direct map

Let `A` be a real algebra with an algebra involution `σ`, a finite real
basis `b : Module.Basis ι ℝ A`, and a compatible complex homomorphism
`h : ComplexHom σ`. The basis index `ι` is a finite type in `Type 0`.
The algebra `A` may live in an arbitrary universe. This makes both
coordinate algebras and their spectra small, while the pointwise results
below allow test algebras in arbitrary universes.

`AlgebraInvolution.similitudeScheme b` is the spectrum of the actual
`σ.similitudeCoordinateRing b` from `SimilitudeCoordinates`.
`similitudeStructureMap b` is induced by its real algebra map. The
representing coordinate algebra already has a proved finite-presentation
instance and a natural equivalence with the existing similitude functor.

`h.delignePoints_map` exposes the naturality of `h.delignePoints` for two
arbitrary test-algebra universes. Its proof checks the underlying unit
using `deligneAlgebraMap_natural`, and the multiplier using `norm_map`.

`h.deligneComorphism b` is

`σ.similitudeHom b (h.delignePoints B universalPoint)`,

where `B` is `DeligneTorus.CoordinateRing`. Thus its type is

`σ.similitudeCoordinateRing b →ₐ[ℝ] B`.

For every `f : B →ₐ[ℝ] S`, `deligneComorphism_point` proves

`σ.similitudePoint b (f.comp (h.deligneComorphism b)) = h.delignePoints S (point f)`.

The proof first uses naturality of the similitude point map, then its
inverse equation with the classifying map, then `delignePoints_map`.
`deligneComorphism_classify` specializes this equality to `f = classify z`,
so every actual quadratic unit `z` is sent to `h.delignePoints S z`.

`h.deligneSchemeMap b` applies `Spec.map` to the underlying ring map.
Its source is `DeligneTorus.scheme` and its target is
`σ.similitudeScheme b`. `deligneSchemeMap_over` proves that composing with
the target's structural morphism gives the source's structural morphism.
The proof uses contravariant functoriality of `Spec` and the fact that the
constructed algebra map commutes with real scalars.

## The inverse convention

`h.inverseDeligneComorphism b` composes the direct cohomomorphism with
`DeligneTorus.inversionComorphism` on the output side.
`inverseDeligneComorphism_point` and `inverseDeligneComorphism_classify`
prove that it sends a point `z` to `h.delignePoints S z⁻¹`. This is exactly
the pointwise convention of the earlier `inverseDeligneHom`.

`inverseDeligneSchemeMap b` is its spectrum morphism.
`inverseDeligneSchemeMap_eq` proves that it is the direct scheme map
precomposed with `inversionSchemeMap`. The order follows from the
contravariance of `Spec`. `inverseDeligneSchemeMap_over` independently
checks compatibility with the real structural morphisms.

## Concrete archimedean specialization and scope

For finite `I`, `harrisArchimedeanBasis n I` chooses an actual finite real
basis of the real algebra `I → Matrix (Fin n) (Fin n) ℂ`, using Mathlib's
finite-dimensional and free-module instances. This is a coordinate choice;
no output scheme or existence theorem is assumed as an input field.

`harrisDeligneSchemeMap` applies the direct construction to the corrected
`harrisArchimedeanHom`. `kottwitzDeligneSchemeMap` applies the inverse
construction to `kottwitzHom`. Their common target coordinate presentation
uses the same chosen basis and the existing
`harrisArchimedeanInvolution n I distinguished`.

The maps realize the existing natural homomorphisms of group-valued point
functors; this module does not package the spectra as group objects in
schemes or prove their smoothness or reductivity. It also does not construct
a complex splitting of the Deligne torus, a global number-field algebra's
archimedean splitting, or any Shimura variety. The PEL moduli, canonical
models, actual scheme levels, and coefficient descent remain required
subsequent work.

Formal dependencies are the unchanged `DeligneCoordinates`, `Deligne`,
and `SimilitudeCoordinates` modules, Mathlib's spectrum functor, and its
finite-dimensional matrix algebra infrastructure. No new axiom or
unfinished proof is introduced.

Sources:

- Kottwitz, *On the lambda-adic representations associated to some simple
  Shimura varieties* (1992), Section 1, p.654 (PDF p.2).
  Source ID `kottwitz-1992-lambda-adic-simple-shimura`, SHA-256
  `749af5541a59187e6f9d1089dec9a0e591a2059173da739c7384ff3a7d0dd799`.
- Harris, *The local Langlands conjecture for GL(n) over a p-adic field,
  n < p* (1998), Erratum, pp.180–182 (PDF pp.4–6).
  Source ID `harris-1998-local-langlands`, SHA-256
  `7934239ea37d0b91f741ae70c2ac157fe5d619cda4dd992ac24e39ae460c375b`.
