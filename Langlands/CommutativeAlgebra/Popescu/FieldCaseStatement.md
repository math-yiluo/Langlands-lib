# Popescu's theorem over a base field

`Langlands.CommutativeAlgebra.Popescu.PopescuFieldCaseStatement` (universe `u`):
for every field `k` and Noetherian commutative ring `Λ` (both in `Type u`) with a
`k`-algebra structure such that `RegularAlgebra k Λ` holds, `HasSmoothFactorizations k Λ`
holds: every `k`-algebra map `A →ₐ[k] Λ` from a finitely presented `k`-algebra `A`
factors as `h.comp g` through a smooth `k`-algebra `B` (all in `Type u`).

## Source

Stacks Project, *Smoothing Ring Maps* (`smoothing.pdf` in
`stacks-artin-axioms-approximation-2026-11-06`), Theorem 12.1 (Tag 07GC, printed p. 31)
in the case where the base ring is a field. The proof of 12.1 begins "By Lemma 8.4 it
suffices to prove this for k → Λ where Λ is Noetherian and geometrically regular over
k", and Lemma 8.4 (Tag 07F5, printed p. 21) has as hypothesis "for every Situation 8.1
where R is a field PT holds". Situation 8.1 (Tag 07F2, p. 20) is a regular ring map of
Noetherian rings; when `R = k` is a field, `k` is automatically Noetherian.

## Encoding

- "Regular ring map" is the Library predicate
  `Langlands.CommutativeAlgebra.RegularAlgebra` (flat with Noetherian geometrically
  regular fibres at every prime); for a field `k` its only prime is `0`, whose fibre is
  `Λ`, so this says `Λ` is geometrically regular over `k`.
- "PT holds" is used in its mapping form `HasSmoothFactorizations` (see
  `Langlands/CommutativeAlgebra/Popescu/Basic.md`): Stacks, Algebra, Lemma 10.127.4.
- This proposition is the hypothesis of
  `Langlands.CommutativeAlgebra.Popescu.PopescuReductionToFieldStatement` (Lemma 8.4);
  together they give `Langlands.CommutativeAlgebra.PopescuFactorizationStatement`.
