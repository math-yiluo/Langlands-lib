# Reduction of the cyclic norm lemma to field extensions

`Langlands.BaseChange.CyclicNormLemmaFieldReductionStatement.{u,v}` is the
internal implication from `FieldCyclicNormLemmaStatement.{u,v}` to the Library
proposition `CyclicNormLemmaStatement.{u,v}`. The premise consists of all three
clauses of that proposition with the larger algebra required to be a field, in
the same universe `v`. The theorem `cyclicNormLemma_of_field` proves the
implication. The field premise remains to be established.

The proof follows the reduction in Henniart–Lemaire, §I.2.2. It uses
`CyclicAlgebraStructure.exists_coordinates` to write the cyclic algebra as `r`
copies of the field `L = E ⧸ m.asIdeal`, with `l = r*d` and `τ` the automorphism
induced by `σ^r`. The coordinate ring maps applied entrywise give the maps
`q_i : GL_n(E) → GL_n(L)` for each exponent `i`. For `0 ≤ i < r` they are jointly
injective, and any tuple of invertible matrices lifts by lifting its matrices
and their inverses entry by entry.

For `δ ∈ GL_n(E)`, put `P_i = q_0(cyclicNorm σ i δ)` and `y = P_r`. Splitting
the published norm product into successive blocks of length `r` shows that
`q_0(cyclicNorm σ l δ) = cyclicNorm τ d y`. The one-step conjugation identity for
the norm and `σ^l = 1` then give `q_i(cyclicNorm σ l δ) = P_i⁻¹ * cyclicNorm τ d y * P_i`.
For (1a) a field conjugator `b` lifts by using `P_i⁻¹ * b` in coordinate `i`.
For (1b) the two associations are transported by `q_0` and field uniqueness
supplies the conjugator over `F`.

For (2) applying `q_0` to the original norm conjugacy gives conjugate norms of
`y` and `y'`. A field twisted conjugator `x₀` lifts to the tuple with coordinates
`P_i⁻¹ * x₀ * P'_i`. At the wraparound, the field twisted-conjugacy equation
says exactly that applying `τ` to `x₀` supplies the continuation at index `r`.
The recurrence `P_(i+1) = P_i * q_i δ` then proves the twisted-conjugacy
equation in every coordinate.

## Source

Henniart and Lemaire, *Changement de base et induction automorphe pour GL_n en
caractéristique non nulle*, Mém. SMF 124 (2011), §§I.2.1–I.2.2, printed
pp. 10–12, PDF pp. 18–20. Source ID
`provided-a0a5445aba86b871bcd83f08813de3234fddb463ff9bb3c9dfd60d2d2fcdae61`.
