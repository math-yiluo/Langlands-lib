# Deligne and unitary-similitude group schemes

Author: Worker 57.

This module constructs the Deligne source and the unitary-similitude target as
actual group schemes over `Spec ℝ`. Their underlying schemes and structural
maps are the explicit spectra from `DeligneAffine`. Both the direct and
inverse-convention morphisms acquire group-scheme homomorphism structures,
and their effects on affine points are proved to be the existing natural
scalar-extension homomorphisms.

## Sources and derived construction

Kottwitz (1992), Section 1, printed p.654 (PDF p.2), uses an
involution-compatible real algebra homomorphism `h₀` from `ℂ` and defines the
Shimura homomorphism from `Res_{ℂ/ℝ} Gₘ` by taking its inverse on complex
units. The imported `Deligne` constructions extend these direct and inverse
maps to every commutative real algebra. Harris (1998), Erratum, printed
pp.180–182 (PDF pp.4–6), corrects the earlier Harris homomorphism by complex
conjugation. The final concrete definitions reuse exactly the corrected
`harrisArchimedeanHom` and the `kottwitzHom` convention of `Positivity`.
They do not identify the two conventions.

These original passages were read for the point-functor and affine-map
constructions reused here. The current group-object packaging is derived:
`GroupScheme.Corepresented` transports a corepresented group functor to a
cogroup on its algebra and then applies Mathlib's product-preserving
`algSpec` functor. Both corepresentations are already constructed by explicit
polynomial quotient algebras and proved natural equivalences. Thus no output
group scheme or representability hypothesis is supplied by the user of this
module. The generic adapter's hypotheses are discharged by those actual
coordinate constructions.

## Deligne source

`DeligneTorus.commFunctor` lifts the existing quadratic-unit functor to
commutative groups. On objects it is the unit group of
`QuadraticAlgebra S (-1) 0`; on arrows it is the same coefficient-change map
as `DeligneTorus.functor`. The identity and composition laws follow from
those of that existing functor.

`DeligneTorus.groupScheme` uses `corepresentableBy` and its explicit algebra
`ℝ[a,b,c,d]/(ac-bd-1, ad+bc)`. It therefore has actual multiplication,
identity and inverse scheme morphisms satisfying the group-object laws.
`commGroupScheme` equips the same object with its commutativity certificate;
`commGroupScheme_toGrp` proves that forgetting that certificate recovers
`groupScheme`.

`groupScheme_scheme` and `groupScheme_structureMap` identify the underlying
scheme and real structural map with `DeligneTorus.scheme` and
`DeligneTorus.structureMap`. `affinePointsEquiv S` is a multiplicative
bijection from morphisms over `Spec ℝ` from `Spec S` to this group scheme
to the actual quadratic unit group `Points S`. Its `affinePointsEquiv_map`
formula sends a spectrum morphism of `f` to the already constructed `point f`.
The imported natural tensor comparison identifies these units with the units
of `S ⊗[ℝ] ℂ`.

`inversionGroupSchemeMap` realizes the natural inversion transformation as a
group-scheme homomorphism. This uses commutativity of the source point groups.
Its underlying scheme morphism is exactly `inversionSchemeMap`, as proved by
`inversionGroupSchemeMap_hom`.

## Similitude target and homomorphisms

Let `A` be a real algebra, `σ` an algebra involution, and
`b : Module.Basis κ ℝ A` a finite real basis. In this module, `A`, `κ` and
all test algebras lie in `Type 0`; the preceding pointwise algebra modules
retain their more general universe scopes. `similitudeGroupScheme b σ`
applies the adapter to `σ.similitudeFunctor` and the explicit
`σ.similitudeCorepresentableBy b`. Its underlying scheme is
`σ.similitudeScheme b`, and its structural morphism is
`σ.similitudeStructureMap b`, by the corresponding `_scheme` and
`_structureMap` theorems.

`similitudeAffinePointsEquiv` gives a group isomorphism on each affine real
test scheme with `(σ.baseChange S).similitudes`. These points are the existing
pairs of an actual unit of `S ⊗[ℝ] A` and a scalar unit satisfying the
involution-similitude equation; no alternate point group is introduced.

Given `h : ComplexHom σ`, `h.deligneGroupSchemeMap b` applies the adapter to
`h.deligneHom`. `deligneGroupSchemeMap_hom` proves that its underlying scheme
morphism is exactly `h.deligneSchemeMap b`. The equality is definitional:
both constructions classify the image of the universal Deligne point and
apply `Spec` to that algebra homomorphism.

`h.inverseDeligneGroupSchemeMap b` instead uses `h.inverseDeligneHom`.
`inverseDeligneGroupSchemeMap_hom` identifies its underlying scheme morphism
with `h.inverseDeligneSchemeMap b`. Here the proof first uses injectivity of
the similitude classification equivalence. It applies
`inverseDeligneComorphism_point` to the identity algebra map to show that
both coordinate maps classify the image of the inverse universal point.
Applying `Spec` then gives the required equality.

`deligneGroupSchemeMap_affinePoints` and
`inverseDeligneGroupSchemeMap_affinePoints` prove the pointwise formulas for
an arbitrary morphism from `Spec S` over the real base. Under the source and
target group isomorphisms, postcomposition with the direct map gives
`h.delignePoints S z`, and postcomposition with the inverse-convention map
gives `h.delignePoints S z⁻¹`. These follow from the generic adapter's proved
naturality and point-recovery equation.

## Concrete specialization and scope

For finite `I` with a distinguished element, `harrisDeligneGroupSchemeMap`
and `kottwitzDeligneGroupSchemeMap` use the actual real algebra
`I → Matrix (Fin n) (Fin n) ℂ`, its signature involution, and the chosen
finite basis `harrisArchimedeanBasis`. The Harris map uses the corrected
direct convention; the Kottwitz map uses the inverse convention. Their
`_hom` theorems identify their underlying scheme morphisms with the two
previous concrete affine maps.

The module constructs group objects and group homomorphisms on the actual
representing schemes. It does not prove smoothness, reductivity or complex
splitting, and does not identify a global number-field algebra with this
archimedean matrix model. The PEL moduli construction, canonical models,
scheme levels and coefficient descent remain subsequent obligations.

Sources:

- Kottwitz, *On the lambda-adic representations associated to some simple
  Shimura varieties* (1992), Section 1, p.654 (PDF p.2). Source ID
  `kottwitz-1992-lambda-adic-simple-shimura`, SHA-256
  `749af5541a59187e6f9d1089dec9a0e591a2059173da739c7384ff3a7d0dd799`.
- Harris, *The local Langlands conjecture for GL(n) over a p-adic field,
  n < p* (1998), Erratum, pp.180–182 (PDF pp.4–6). Source ID
  `harris-1998-local-langlands`, SHA-256
  `7934239ea37d0b91f741ae70c2ac157fe5d619cda4dd992ac24e39ae460c375b`.
