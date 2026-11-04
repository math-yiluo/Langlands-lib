# Proof of the actual relative model Hom colimit comparison

This proof reuses the complete draft by Worker 105. Its source context is
Brian Conrad, *Weil and Grothendieck approaches to adelic points*
(December 31, 2011), printed pp. 5–6, Theorem 3.4(1). Conrad states the
Hom-colimit bijection for finitely presented models over a directed ring
system. The present cofiltered affine-base formulation and its weaker
individual hypotheses are derived from the published `modelMorphismDescent`
theorem.

The theorem `modelHomColimitComparison` proves the complete target
`ModelHomColimitComparison` without changing its definitions or hypotheses.
It uses `modelMorphismDescent` to obtain factorization and eventual equality
for actual relative morphisms over the supplied limit base.

For injectivity, apply Mathlib's
`Functor.CoconeTypes.descColimitType_injective_iff_of_isFiltered` to the
actual `homCoconeTypes`. The opposite of the cofiltered base category is
filtered. Given two level representatives with equal images under actual
base change, the eventual equality clause of `modelMorphismDescent` supplies
a common base level and two restriction arrows. Taking their opposites
provides precisely the witness required by the filtered quotient criterion.
This uses only quasi-compactness of the source and local finite type of the
target.

For surjectivity, the factorization clause supplies a level relative
morphism whose `toLimit` equals the requested actual limit morphism. Its
class under `homColimitι` is a preimage under the canonical comparison,
because `homColimitMap_ι` is its defining component formula. This uses
quasi-compactness and quasi-separatedness of the source and local finite
presentation of the target.

Local finite presentation implies local finite type, so the latter
hypotheses give both injectivity and surjectivity. Finally, Mathlib's
`Functor.CoconeTypes.isColimit_iff` converts that bijectivity into existence
of an `IsColimit` witness for the corresponding actual categorical cocone
`homCocone`. No alternate comparison map or assumed colimit structure is
introduced. The proof is a quotient and universal-property adapter for the
previous descent theorem; it makes no claim about initial models, property
descent, spectral realizations or topology.
