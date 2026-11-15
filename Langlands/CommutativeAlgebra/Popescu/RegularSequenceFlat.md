# Proof: a regular system of parameters mapping to a regular sequence gives flatness

`Langlands.CommutativeAlgebra.Popescu.regularSequenceFlat` (lines 202–207) has type exactly
`Langlands.CommutativeAlgebra.Popescu.RegularSequenceFlatStatement.{u}`. It imports the
unchanged statement module `Langlands.CommutativeAlgebra.Popescu.RegularSequenceFlatStatement`.

Let `R`, `S : Type u` be Noetherian local rings and `R → S` a local homomorphism. Let
`x : List R` be a weakly regular sequence of `R` with `Ideal.ofList x = 𝔪_R`, whose image
`x.map (algebraMap R S)` is weakly regular on `S`. Then `S` is flat over `R`. This is Stacks
Lemma 10.128.2 (Tag 07DY, `stacks-commutative-algebra-chapter-ed88ff78`, printed p. 319).

The proof adds no hypotheses. Its axioms are `propext`, `Classical.choice` and `Quot.sound`.

## The local flatness criterion used

The local criterion of flatness is not reproved here. Each application uses the published
Library theorem `Langlands.Algebra.idealLocalFlatnessCriterion`, which proves
`Langlands.Algebra.IdealLocalFlatnessCriterionStatement` (Stacks Lemma 10.99.10, Tag 00ML), with
module `M = S`. Its hypotheses for an ideal `I ≠ ⊤` of `R` are:

- `S` is finite over itself;
- the tensor inclusion `I ⊗[R] S → R ⊗[R] S` is injective;
- `(R ⧸ I) ⊗[R] S` is flat over `R ⧸ I`.

It concludes that `S` is flat over `R`.

## Helper declarations

All helpers are in the namespace `Langlands.CommutativeAlgebra.Popescu.RegularSequenceFlat`.

- `span_singleton_rTensor_injective` (lines 31–61). For any commutative `R`-algebra `S` and
  `a : R` such that `algebraMap R S a` is a nonzerodivisor on `S`, the map
  `(Ideal.span {a}).subtype.rTensor S` is injective. The proof works with `g = ⟨a, _⟩` in
  the ideal `(a)`. Induction on tensors shows that every element of `(a) ⊗[R] S` equals
  `g ⊗ s` for some `s`: a generator `(r a) ⊗ s` equals `g ⊗ (r • s)` by `smul_tmul`. If
  `g ⊗ s` maps to zero, then applying `TensorProduct.lid R S` gives `a • s = 0`. Since
  `a • s = algebraMap R S a • s`, regularity gives `s = 0`. This replaces the remark after
  Stacks Lemma 10.99.10, in the tensor-injectivity form used here. Regularity of `a` on `R`
  itself is not needed.
- `isWeaklyRegular_quotSMulTop_iff` (lines 69–81). Let `A` be a commutative ring and
  `J = Ideal.span {s}`. Then weak regularity of `rs` on the `A`-module `QuotSMulTop s A`
  (that is, `A ⧸ s • ⊤`) is equivalent to weak regularity of `rs.map (Ideal.Quotient.mk J)`
  on the ring `A ⧸ J`. The proof identifies `s • ⊤ = J` using
  `Submodule.ideal_span_singleton_smul` and `Ideal.mul_top`, takes the induced additive
  equivalence `Submodule.quotEquivOfEq`, and applies Mathlib's
  `AddEquiv.isWeaklyRegular_congr`. The scalar compatibility for each pair `(r, mk r)` holds
  by `rfl` on representatives.
- `flat_of_maximalIdeal_eq_bot` (lines 90–110) is the base case. If `𝔪_R = ⊥`, every
  element of `𝔪_R ⊗[R] S` is zero, by induction on tensors, so the inclusion into
  `R ⊗[R] S` is injective. The quotient `R ⧸ 𝔪_R` is a field (`Ideal.Quotient.field`), so
  `(R ⧸ 𝔪_R) ⊗[R] S` is free and hence flat over it. The criterion with `I = 𝔪_R` then
  gives flatness of `S`.
- `flat_of_flat_quotient` (lines 112–126) is the induction step. Let `a ∈ 𝔪_R` be such that
  `algebraMap R S a` is a nonzerodivisor on `S`, and suppose
  `S ⧸ (Ideal.span {a}).map (algebraMap R S)` is flat over `R ⧸ Ideal.span {a}`. This uses
  Mathlib's algebra `Ideal.Quotient.algebraQuotientMapQuotient`. Then `S` is flat over `R`.
  Mathlib's `(R ⧸ I)`-algebra equivalence
  `Algebra.TensorProduct.quotIdealMapEquivQuotTensor S I : S ⧸ I S ≃ₐ[R ⧸ I] (R ⧸ I) ⊗[R] S`,
  with `Module.Flat.of_linearEquiv`, transfers the flatness hypothesis to
  `(R ⧸ I) ⊗[R] S`. Injectivity comes from `span_singleton_rTensor_injective`, and
  `I = (a) ≠ ⊤` because `a ∈ 𝔪_R`.

## Induction

`flat_of_length n` (lines 130–198) proves, by induction on `n`, the statement's conclusion
for all `R`, `S : Type u` (with all the statement's instances) and all `x` of length `n`.
Quantifying over the rings lets the induction hypothesis apply to the quotient rings.

- **Length 0.** Here `x = []`, so `𝔪_R = Ideal.ofList [] = ⊥`. Conclude by
  `flat_of_maximalIdeal_eq_bot`.
- **Length `n + 1`.** Here `x = a :: xs`. Since `a ∈ Ideal.ofList x = 𝔪_R`, the ideals
  `(a)` and `(a)S` are proper. The latter lies in `𝔪_R S ⊆ 𝔪_S` by
  `IsLocalRing.map_maximalIdeal_le`. Put `R' = R ⧸ (a)` and `S' = S ⧸ (a)S`. Then:
  - `R'` and `S'` are nontrivial, local (`IsLocalRing.of_surjective'`) and Noetherian
    (`Ideal.Quotient.isNoetherianRing`).
  - `R' → S'` is local. If the image of `mk r` is a unit, then `mk (algebraMap R S r)` is a
    unit of `S'`. The quotient map from the local ring `S` is local
    (`IsLocalHom.of_surjective`), and so is `R → S`. Hence `r` is a unit, and so is `mk r`.
  - `Ideal.ofList (xs.map mk) = 𝔪_{R'}`. This follows from `Ideal.map_ofList`,
    `IsLocalRing.map_maximalIdeal_of_surjective`, `Ideal.ofList_cons`, `Ideal.map_sup` and
    `Ideal.map_quotient_self`.
  - `xs.map mk` is weakly regular on `R'`. Mathlib's `isWeaklyRegular_cons_iff` turns the
    hypothesis on `R` into weak regularity of `xs` on `QuotSMulTop a R`; apply
    `isWeaklyRegular_quotSMulTop_iff` with `J = (a)`.
  - `(xs.map mk).map (algebraMap R' S')` is weakly regular on `S'`. `isWeaklyRegular_cons_iff`
    on `S` gives regularity of `algebraMap R S a` on `S` and weak regularity of
    `xs.map (algebraMap R S)` on `QuotSMulTop (algebraMap R S a) S`. Apply
    `isWeaklyRegular_quotSMulTop_iff` with `J = (a)S = Ideal.span {algebraMap R S a}`
    (`Ideal.map_span`). Rewrite the list with `List.map_map`: both composites send `r` to
    the class of `algebraMap R S r`, definitionally.

  The induction hypothesis gives `Module.Flat R' S'`, and `flat_of_flat_quotient` concludes
  `Module.Flat R S`.

The main theorem applies `flat_of_length x.length` with `rfl` for the length.

## Comparison with the source proof

Stacks proves the lemma by descending from `S/(x₁, …, x_d)S`, which is flat over the field
`R/(x₁, …, x_d)`. At each step, `x_i` is a nonzerodivisor on `S/(x₁, …, x_{i-1})S`, and the
local criterion (Lemma 10.99.10 and the remarks following it) gives flatness of
`S/(x₁, …, x_{i-1})S` over `R/(x₁, …, x_{i-1})`. The Lean proof runs the same chain of
applications as a structural induction from the front of the list. It quotients by one element
at a time, and the induction hypothesis already covers all the later quotients. The rings
`R/(x₁)/(x₂)…` arising this way are iterated quotients rather than the source's
`R/(x₁, …, x_i)`, which they are isomorphic to; the Lean proof never needs this
identification.

The criterion is applied in its ideal form (00ML), with `I = (x_i)` in the current quotient
ring. Tor-vanishing is stated, as in the Library statement, as injectivity of
`I ⊗ S → S`, and proved directly from the nonzerodivisor hypothesis on the current quotient
of `S`. Every step uses the weak regularity of the image sequence on `S`.

The weak regularity of `x` on `R` is passed down the induction but never used. Each step
discards the regularity of the head element on the current quotient of `R`; in the Lean
proof this is the `-` pattern at line 177. The base case ignores what remains. In the source,
regularity on `R` enters through the remark after Lemma 10.99.10 (printed p. 235). That remark
assumes `x` is a nonzerodivisor in `R` and identifies `Tor₁(M, R/(x)) = 0` with `x` being a
nonzerodivisor on `M`. Here Tor-vanishing is the injectivity of `(x) ⊗ S → S`, and
`span_singleton_rTensor_injective` derives it from regularity on `S` alone. Proving a theorem
from fewer hypotheses than the statement allows is harmless: the theorem still has exactly
the statement's type.
