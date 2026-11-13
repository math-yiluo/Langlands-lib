# Lifting smooth factorizations along a nilpotent ideal

`Langlands.CommutativeAlgebra.Popescu.NilpotentLiftingStatement` (universe `u`): for
commutative rings `R`, `Λ` in `Type u` with `Λ` an `R`-algebra and an ideal `I` of `R`,
if `I` is nilpotent, `Λ` is flat over `R`, and
`HasSmoothFactorizations (R ⧸ I) (Λ ⧸ I.map (algebraMap R Λ))` holds, then
`HasSmoothFactorizations R Λ` holds.

## Source

Stacks Project, *Smoothing Ring Maps* (`smoothing.pdf` in
`stacks-artin-axioms-approximation-2026-11-06`), Proposition 5.3 (Tag 07CM, printed
p. 15): "Let R → Λ be a ring map. Let I ⊂ R be an ideal. Assume that (1) I is
nilpotent, (2) Λ/IΛ is a filtered colimit of smooth R/I-algebras, and (3) R → Λ is
flat. Then Λ is a filtered colimit of smooth R-algebras."

## Encoding

- (1) is `IsNilpotent I` (some power of `I` is the zero ideal); (3) is
  `Module.Flat R Λ`.
- `IΛ` is `I.map (algebraMap R Λ)`; `Λ / IΛ` is an `R / I`-algebra through Mathlib's
  instance `Ideal.Quotient.algebraQuotientMapQuotient`.
- "Filtered colimit of smooth algebras" (hypothesis (2) and the conclusion) is used in
  its mapping form `HasSmoothFactorizations` (Stacks, Algebra, Lemma 10.127.4; see
  `Langlands/CommutativeAlgebra/Popescu/Basic.md`); the proof of 5.3 itself works with
  this form ("We have to find a factorization A → B → Λ with B smooth over R, see
  Algebra, Lemma 127.4").
