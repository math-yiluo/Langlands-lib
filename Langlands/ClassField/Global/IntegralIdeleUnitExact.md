# Exactness of the ordinary-unit sequence

The theorem `Langlands.ClassField.Global.integralIdeleUnitSequenceExact`
proves the unchanged published proposition
`IntegralIdeleUnitSequenceExact.{u}`. For every number field `E : Type u`,
it asserts injectivity of `ringIntegerUnitsToIntegralIdeles E` and
the subgroup equality
`(integralIdelesToClasses E).ker = (ringIntegerUnitsToIntegralIdeles E).range`.
It uses the actual groups and maps from `IntegralIdeleCoefficients`, with
no extension or Galois hypothesis.

The principal embedding `IdeleGroup.unitEmbedding (𝓞 E) E` is injective
by `Units.map_injective` and `AdeleRing.algebraMap_injective`. Equality of
the images of two ordinary units in the integral-idele subtype gives
equality of their underlying principal ideles. Injectivity of this
embedding, followed by `Units.map_injective` for
`IsFractionRing.injective (𝓞 E) E`, then gives equality of the original
units.

For the subgroup equality, extensionality and
`integralIdelesToClasses_ker` reduce kernel membership to being a
principal idele. If an integral idele `x` is the principal idele of
`a : Eˣ`, the subtype's membership proof says that this principal
idele's coordinate at every finite place has valuation one. The
separately published theorem `principalIdeleUnitCriterion`, imported from
`PrincipalIdeleUnits`, therefore provides `ε : (𝓞 E)ˣ` whose canonical
image in `Eˣ` is `a`. Applying the principal embedding to this equality
and then subtype extensionality shows
`ringIntegerUnitsToIntegralIdeles E ε = x`. Thus the proof uses the
established arithmetic unit criterion without assuming integrality of
`a`. Conversely, the image of an ordinary unit is a principal idele by
definition: its principal witness is
`Units.map (algebraMap (𝓞 E) E).toMonoidHom ε`.

Together with the existing `integralIdelesToClasses_surjective`, the
conclusion gives exactness of the multiplicative sequence
`1 → (𝓞 E)ˣ → J∞ → C∞ → 1`. Here `J∞ = integralIdeles E`
requires valuation one at every finite coordinate and has unrestricted
infinite coordinates, and `C∞ = integralIdeleClasses E` is its image in
the actual idele class group. The proposition itself asserts only
injectivity and the kernel equality. This proof adds no
representation-level short exact sequence or cohomological formula.

The source interpretation is the one documented with the published
statement. Artin–Tate, *Class Field Theory* (AMS Chelsea, 2009),
Chapter V §3, printed p.13/PDF22, identifies the image of the
`S`-ideles modulo principal ideles with the quotient by their
intersection with the principal ideles. Taking `S` to be all infinite
places specializes that intersection to ordinary units. Milne,
*Class Field Theory*, v4.03 (2020), Chapter V, Aside 4.5,
the first claim of footnote 12, printed p.171/PDF180, supplies the
finite-local-unit recognition of ordinary units. Only that arithmetic
claim is used here. The implemented proof assembles the published maps,
kernel description and unit criterion, rather than reproducing the
sources' surrounding topological or Herbrand arguments.

Registered sources:

- `artin-tate-2009-class-field-theory`, SHA256
  `af7ba934904a3c10012e6fd326cea493ffb6200d885d97583277bb45f935c3dd`.
- `milne-2020-class-field-theory`, SHA256
  `50d79af78250a9f1117ad9d337e0b231704a533fc707966ed1bfa52e13d498f5`.

Worker 343 supplied the complete Lean proof and initial proof
description in the focused shared draft. Worker 406 checked it against
the published imports and prepared this paired explanation and
contribution. The imported `PrincipalIdeleUnits` proof belongs to its
separate published contribution and is not duplicated here.
