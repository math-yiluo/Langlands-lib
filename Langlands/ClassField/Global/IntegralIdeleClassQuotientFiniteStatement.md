# Finiteness of the quotient by integral idele classes

`Langlands.ClassField.Global.IntegralIdeleClassQuotientFinite.{u}` asserts
that `IntegralIdeleClassQuotient E` is finite for every number field
`E : Type u`, with no restriction on `u`.

The imported quotient is the actual double quotient `C_E / C∞`, where
`C_E` is `NumberField.IdeleClassGroup (𝓞 E) E` and `C∞` is the image
of `integralIdeles E` in `C_E`. The latter subgroup consists of actual
ideles whose coordinate at every finite place has valuation one.
The infinite coordinates are unrestricted. Finiteness means finiteness
of the underlying group as a type, not finite generation or finiteness
of selected cohomology groups. There is no field extension or Galois
hypothesis.

The source is Artin and Tate, *Class Field Theory* (2009), Chapter V §3,
printed p.13 (PDF p.22), registered as
`artin-tate-2009-class-field-theory`, SHA256
`af7ba934904a3c10012e6fd326cea493ffb6200d885d97583277bb45f935c3dd`.
The page deduces finiteness of `J/(J_S K×)` from finiteness of the class
number. Specialize its global field to the number field `E` and take `S`
to be all infinite places. This is a nonempty finite set for a number
field. One can take the trivial extension `K = k = E`, so the assertion
requires no extension data. The subgroup `J_S` is exactly our
`integralIdeles E`. Quotienting first by the principal ideles and then
by the image of `J_S` gives the double quotient in this statement.
This reformulation of the source's quotient is the derived provenance
of the Lean proposition.

This file states the arithmetic finiteness result without proving it.
It does not construct a class-group isomorphism, establish a Herbrand
quotient, or prove the parent first-inequality statement. A proof may
identify this quotient with the actual ideal class group of `𝓞 E` and
use its finiteness.
