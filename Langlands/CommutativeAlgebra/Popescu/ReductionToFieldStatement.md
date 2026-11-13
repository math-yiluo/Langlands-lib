# Reduction of Popescu's theorem to a base field

`Langlands.CommutativeAlgebra.Popescu.PopescuReductionToFieldStatement` (universe `u`):
if `PopescuFieldCaseStatement.{u}` holds, then for all Noetherian commutative rings
`R`, `Λ` in `Type u` with an `R`-algebra structure on `Λ` such that `RegularAlgebra R Λ`
holds, `HasSmoothFactorizations R Λ` holds.

## Source

Stacks Project, *Smoothing Ring Maps* (`smoothing.pdf` in
`stacks-artin-axioms-approximation-2026-11-06`), Lemma 8.4 (Tag 07F5, printed p. 21):
"If for every Situation 8.1 where R is a field PT holds, then PT holds in general."
Situation 8.1 (Tag 07F2, p. 20): "R → Λ is a regular ring map of Noetherian rings", and
"we say PT holds for R → Λ if Λ is a filtered colimit of smooth R-algebras".

## Encoding

- The hypothesis "for every Situation 8.1 where R is a field PT holds" is
  `PopescuFieldCaseStatement.{u}` (field `k`, Noetherian `Λ`, `RegularAlgebra k Λ`,
  conclusion `HasSmoothFactorizations k Λ`), in the same universe `u`.
- The conclusion "PT holds in general" quantifies over all Noetherian `R`, `Λ` with
  `RegularAlgebra R Λ` (the Library predicate for a regular ring map).
- PT is used in its mapping form `HasSmoothFactorizations` (Stacks, Algebra,
  Lemma 10.127.4; see `Langlands/CommutativeAlgebra/Popescu/Basic.md`), which quantifies
  over finitely presented sources. Over a Noetherian base finite type and finite
  presentation agree, so this gives the finite-type form of
  `Langlands.CommutativeAlgebra.PopescuFactorizationStatement`.
