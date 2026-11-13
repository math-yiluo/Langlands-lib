# Field extensions in characteristic zero have smooth factorizations

`Langlands.CommutativeAlgebra.Popescu.CharZeroFieldFactorizationStatement` (universe `u`):
for fields `K`, `L : Type u` with `L` a `K`-algebra and `K` of characteristic zero,
`HasSmoothFactorizations K L`. That is, every `K`-algebra map `A → L` with `A` finitely
presented over `K` factors through a smooth `K`-algebra.

## Source

Stacks Project, Chapter 10 *Commutative Algebra* (`stacks-commutative-algebra-chapter-ed88ff78`,
full chapter PDF, version ed88ff78):

- Proposition 10.158.9 (Tag 0322, printed p. 434): "Let K/k be a field extension. If the
  characteristic of k is zero then (1) K is separable over k, …".
- Lemma 10.158.11 (Tag 07BV, printed p. 434): "Let K/k be a field extension. … If K/k
  is separable, then K is a filtered colimit of smooth algebras over k."
- Lemma 10.127.4 (Tag 07C3, printed p. 312): `Λ` is a filtered colimit of elements of a
  set `E` of finitely presented `R`-algebras if and only if every `R`-algebra map
  `A → Λ` with `A` of finite presentation over `R` factors as `A → B → Λ` with `B ∈ E`.

## Encoding

- "Filtered colimit of smooth algebras" is stated in its equivalent mapping form
  (Lemma 10.127.4 with `E` the smooth `K`-algebras), which is `HasSmoothFactorizations`
  (see `Langlands/CommutativeAlgebra/Popescu/Basic.md`).
- Separability is not a hypothesis: by Proposition 10.158.9 every extension of a field
  of characteristic zero is separable. `[CharZero K]` encodes the characteristic.
- The smoothing chapter uses this in the proof of Lemma 10.3 (Tag 07FE) through
  "Algebra, Lemma 158.11". All rings are in one universe `u`.
