# Ordinary units inside integral ideles

`Langlands.ClassField.Global.IntegralIdeleUnitSequenceExact.{u}` states,
for every number field `E : Type u`, that the actual homomorphism
`ringIntegerUnitsToIntegralIdeles E` is injective and that its range is
the kernel of `integralIdelesToClasses E`.

These maps are imported unchanged from `IntegralIdeleCoefficients`.
The first maps a unit of the ring of integers into its principal idele.
Its target `integralIdeles E` consists of ideles with valuation one at
every finite coordinate, with unrestricted infinite coordinates. The
second map sends such an idele to its class in the image subgroup
`integralIdeleClasses E` of the actual idele class group. Thus the
kernel assertion identifies integral principal ideles with ordinary
global units. No extension, Galois, cyclicity, or integrality assumption
on a separately chosen field element is imposed.

Surjectivity onto `integralIdeleClasses E` is already proved as
`integralIdelesToClasses_surjective` in the imported module. Together
with that theorem, the present proposition expresses exactness of
`1 → (𝓞 E)ˣ → J∞ → C∞ → 1`. The proposition itself asserts only
injectivity and the kernel equality; this file does not prove them or
construct a representation-level short exact sequence.

The source is Artin–Tate, *Class Field Theory* (2009), Chapter V §3,
printed page 13/PDF page 22. The passage identifies `J_S Kˣ/Kˣ`
with `J_S/(J_S ∩ Kˣ)` and identifies the intersection with the
`S`-unit group. Specialize to `K = k = E` and to the set of all
infinite places. Milne, *Class Field Theory*, v4.03 (2020),
Chapter V, Aside 4.5 and the first claim of footnote 12, printed
page 171/PDF page 180, explicitly identifies the diagonal elements
that are units in every finite completion with the units of the
global ring of integers. This gives exactly the kernel identification
for the published maps; their injectivity comes from the diagonal
embedding and the inclusion of the ring of integers in its field.
No topological or cohomological conclusion from either passage is
included here.

Registered sources:

- `artin-tate-2009-class-field-theory`, SHA256
  `af7ba934904a3c10012e6fd326cea493ffb6200d885d97583277bb45f935c3dd`.
- `milne-2020-class-field-theory`, SHA256
  `50d79af78250a9f1117ad9d337e0b231704a533fc707966ed1bfa52e13d498f5`.

This interface follows Worker 230's proposed statement for the actual
coefficient diagram. Its later proof can reuse
`PrincipalIdeleUnitCriterion`; the present statement does not assume
that criterion or the desired exactness.
