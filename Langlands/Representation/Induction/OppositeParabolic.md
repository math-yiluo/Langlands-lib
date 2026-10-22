# Normalized induction from opposite block parabolics

Author: Worker 15. The implementation adapts Worker 23's published upper
parabolic wrapper; Worker 19 specified the consumer interface and normalization.

This module constructs smooth induction from the actual lower block parabolic
`B.oppositeParabolic F` using its published projection
`B.oppositeLeviProjection F` to the same product Levi `B.Levi F` as the upper
parabolic. For a p-adic realization `T`, the character is the inverse of the
upper positive half modulus. The stable consumer API is
`T.normalizedOppositeParabolicInduced B σ` in
`Langlands.Representation.Induction.OppositeParabolic`.

## Construction and normalization

Write `Pbar = B.oppositeParabolic F.Carrier`, `M = B.Levi F.Carrier`, and
`m(p) = B.oppositeLeviProjection F.Carrier p`. For the upper block modulus
`δ_P = T.leviModulus B`, the normalizing scalar is

```
χ(m) = (T.leviHalfModulus B m)⁻¹ = sqrt(δ_P(m))⁻¹.
```

The square root is the canonical positive square root, embedded in the complex
numbers. `T.oppositeLeviHalfCharacter B` packages this character with its proved
open kernel. `oppositeLeviHalfCharacter_toMonoidHom` identifies its underlying
homomorphism with `(T.leviHalfModulus B)⁻¹`. The open-kernel proof reuses
`Jacquet.isOpen_ker_inverseHalfCharacter` and `T.isOpen_ker_leviModulus B`.

`T.oppositeParabolicHalfModulus B` is `χ ∘ m`. Its evaluation, restriction to
the common block-diagonal section, triviality on the opposite unipotent radical,
and open kernel are proved in `oppositeParabolicHalfModulus_apply`,
`oppositeParabolicHalfModulus_section`,
`oppositeParabolicHalfModulus_unipotent`, and
`isOpen_ker_oppositeParabolicHalfModulus`. The last proof takes the preimage of
the open Levi kernel under `T.oppositeBlockLeviProjection B`.

The inducing representation is the actual representation
`twist (T.oppositeParabolicHalfModulus B) (σ.comp m)`. Its induced carrier is
`Induction.SmoothFunctions Pbar` of this representation: covariant functions
`G → V`, each fixed by one open subgroup under right translation. The inherited
module operations and action come from the published smooth part of coinduction.
The following formulas are proved:

```
f(p g) = sqrt(δ_P(m(p)))⁻¹ • σ(m(p))(f(g)),
(g · f)(x) = f(x g).
```

They are `normalizedOppositeParabolicInduced_covariant` and
`normalizedOppositeParabolicInduced_apply`. The covariance proof uses the
function's defining equality and `Jacquet.inverseHalfCharacter_apply`; the
action formula is definitional. `isSmooth_normalizedOppositeParabolicInduced`
reuses the proved smoothness of smooth induction, hence its uniform open
stabilizers. No topology on `V` or smoothness assumption on `σ` is needed to
construct this smooth part.

## Maps, functors, and universes

`T.normalizedOppositeParabolicInducedMap B f` sends an actual Levi intertwiner
`f : σ.IntertwiningMap τ` to postcomposition on induced functions. Inflation and
scalar twisting give the intertwiner of inducing representations; the published
`smoothInducedMap` gives its induced map. The specialized lemmas with suffixes
`_apply`, `_id`, and `_comp` prove evaluation, preservation of identities, and
preservation of composition. Extensional equality reduces the generic laws to
pointwise reflexivity; the p-adic laws specialize them.

`T.normalizedOppositeParabolicInductionFunctor B` packages these constructions
as a functor between the existing canonical smooth categories:

```
SmoothRep.{0, uF, uV} ℂ (B.Levi F.Carrier) ⥤
  SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier).
```

Here `F : PadicField.{uF} p` with prime `p` is arbitrary, and `V : Type uV`
has its own independent universe. Maps also allow independent target and
composite carrier universes `uW` and `uX`. The induced function space lies in
`Type (max uF uV)`. The selected topology is precisely `T.topology`; all group
and Levi topologies are the published ones induced from it. The topological
ring instance is obtained from `T`'s valuation and local-field structure.

`F.canonicalNormalizedOppositeParabolicInduced B σ` and
`F.canonicalNormalizedOppositeParabolicInductionFunctor B` use the published
canonical topological realization of every algebraic p-adic field.

## Generic layer and compact variant

The generic construction works over any topological commutative ring `F`,
with a supplied smooth character `χ` of the actual Levi. In the namespace
`Langlands.GeneralLinear.BlockShape`, its names are
`inflateOppositeCharacter`, `oppositeInducingRepresentation`,
`normalizedOppositeInducedOf`, `oppositeInducingMap`,
`normalizedOppositeInducedOfMap`, and `normalizedOppositeInductionFunctorOf`.
The covariance, right-translation, smoothness, map evaluation, identity, and
composition lemmas have the corresponding names. Character inflation has open
kernel by continuity of `B.oppositeLeviProjectionContinuous F`.

The pair also includes `normalizedOppositeCompactInducedOf`, its smoothness
proof and `normalizedOppositeCompactInclusionOf`. These use the published
compact induction submodule, whose functions have compact projected nonzero
support in `Pbar \ G`, and its inclusion into smooth induction. The p-adic
specializations are `normalizedOppositeParabolicCompactInduced` and
`normalizedOppositeParabolicCompactInclusion`. Equality of the compact and
smooth variants is not proved here.

## Derived provenance and source correspondence

This is a derived construction, not a new representation-theoretic theorem.
Its implementation follows `Induction/Parabolic`, replacing the upper subgroup
and projection by `Group/GL/OppositeBlocks` and `Group/GL/PadicOppositeBlocks`.
It composes the accepted constructions in `Group/GL/BlockModulus`,
`Jacquet/PositiveCharacter`, `Twist/Definitions`, `Induction/Definitions`, and
`Category/Basic`. The lower subgroup and its common embedded Levi stay explicit
throughout; no conjugation or transport to an upper parabolic is performed.

Bernstein--Zelevinsky (1977), section 1.8(a), printed page 444 / PDF page 5,
defines normalized induction using covariance, a uniform open right stabilizer,
and right translation, and defines its compactly supported subspace. This pair
specializes that construction to the trivial character on the opposite radical.
The source uses the Haar module of conjugation on that radical. The wrapper uses
the inverse of the explicit upper determinant modulus; its interpretation as the
opposite Haar module requires the separate Haar-modulus comparison, just as in
the published upper wrapper. That comparison is neither assumed nor proved here.

Silberger (1979), Corollary 4.5.11, printed pages 189--190 / PDF pages 195--196,
and Theorem 4.5.18, printed page 193 / PDF page 199, motivate the downstream
support and summand interfaces requested by Worker 19. Those results are not
asserted in this pair. The cited original pages were read; their roles here are
the function-space convention and downstream motivation, respectively.

Registered sources:

- `bernstein-zelevinsky-1977-induced-i`, SHA256
  `8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`,
  section 1.8(a), printed page 444 / PDF page 5.
- `silberger-1979-harmonic-analysis`, SHA256
  `b9432812bb48ce0bcd3975144baa6b3cca99bcaaf0d33d785ce68e94e02854fc`,
  Corollary 4.5.11, printed pages 189--190 / PDF pages 195--196, and
  Theorem 4.5.18, printed page 193 / PDF page 199 (motivation only).

The contribution proves intrinsic construction obligations only. Admissibility,
finite length, irreducibility, adjunction, Weyl transport, and support or
classification theorems remain separate obligations.
