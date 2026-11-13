# Essentially smooth algebras and truncated local rings

Module `Langlands.CommutativeAlgebra.Popescu.EssentiallySmooth` contains three definitions
used by the statements of Section 11 ("Inseparable residue fields") of the Stacks Project
chapter *Smoothing Ring Maps* (`smoothing.pdf` in the source folder
`stacks-artin-axioms-approximation-2026-11-06`). All three are in the namespace
`Langlands.CommutativeAlgebra.Popescu`, and all rings are in one universe `u`.

## `EssentiallySmooth R S`

For commutative rings `R`, `S` and an `R`-algebra `S`, `EssentiallySmooth R S` holds when
there are

- a commutative ring `T` with an `R`-algebra structure and a `T`-algebra structure on `S`
  such that `R → T → S` is a scalar tower (the composite `R → T → S` is the given algebra
  map `R → S`),
- a submonoid `M` of `T`,

such that `T` is a smooth `R`-algebra (`Algebra.Smooth R T`, which in Mathlib includes
finite presentation) and `S` is the localization of `T` at `M` (`IsLocalization M S`).
In words: `S` is a localization of a smooth `R`-algebra.

**Provenance.** The chapter uses "essentially smooth" without defining it. In Lemma 11.2
(Tag 07FH, printed p. 27) it asks for a factorization
`k[y₁, …, y_m]_p/pⁿ → D → Λ_q/qⁿΛ_q` "where the first arrow is essentially smooth", and
the proof ends: "Finally, we conclude that it is étale by Algebra, Lemma 143.7. Since an
étale ring map is certainly essentially smooth we win." The proof of Lemma 11.4
(Tag 07FJ, step (25), printed p. 31) uses it as follows: "D′ is essentially smooth over
the local Artinian ring k[y₁, …, y_m]_p/pⁿ… Hence D′[t₁, …, t_d] is a filtered colimit of
smooth R_p/pⁿR_p-algebras". The definition chosen here is the smooth analogue of Stacks
Project, Chapter 10 *Commutative Algebra*, version ed88ff78
(`stacks-commutative-algebra-chapter-ed88ff78`), Definition 10.54.1 (Tag 00QM, printed
p. 126): "Let R → S be a ring map. (1) We say that R → S is essentially of finite type if
S is the localization of an R-algebra of finite type." With it, the colimit claim of
step (25) holds: a localization `M⁻¹T` is the filtered colimit of the smooth algebras
`T_g`, `g ∈ M`.

## `localTruncation q n`

For a commutative ring `Λ`, a prime ideal `q` of `Λ` and `n : ℕ`, `localTruncation q n` is
the quotient ring `Λ_q ⧸ 𝔪ⁿ`, where `Λ_q = Localization.AtPrime q` and
`𝔪 = IsLocalRing.maximalIdeal Λ_q`. It is an `abbrev`, so the quotient ring structure and
the algebra structures of `Λ_q ⧸ 𝔪ⁿ` apply to it directly.

**Provenance.** This is the ring `Λ_q/qⁿΛ_q` of Lemmas 11.2, 11.3 and 11.4. The maximal
ideal of `Λ_q` is `qΛ_q`, so `𝔪ⁿ = qⁿΛ_q`. The definition is notation and makes no
mathematical claim.

## `toLocalTruncation q n`

For `Λ`, `q` and `n` as above, `toLocalTruncation q n : Λ →+* localTruncation q n` is the
composite of `algebraMap Λ Λ_q` and the quotient map `Ideal.Quotient.mk (𝔪ⁿ)`. It sends
`x ∈ Λ` to the class of `x/1` modulo `qⁿΛ_q`.

**Provenance.** This is the canonical map `Λ → Λ_q/qⁿΛ_q` of Lemmas 11.2–11.4. Lemma 11.3
uses it in "λ^q is in D′" for an element `λ ∈ Λ`. The statements of Lemmas 11.2 and 11.3
also use it, applied to `k[y₁, …, y_m]` and the prime `p`, for the map
`k[y₁, …, y_m] → k[y₁, …, y_m]_p/pⁿ`. The definition is notation and makes no
mathematical claim.
