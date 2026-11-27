# Locally embeddable unitary tori with a prescribed norm

Module: `Langlands.Algebra.CentralSimple.NumberFieldUnitaryNormTorusStatement`.

`Langlands.CentralSimple.NumberFieldUnitaryNormTorusStatement.{u}` is a proposition; this
module states it and does not prove it.

## The statement

The data and the hypothesis are those of
`Langlands.CentralSimple.NumberFieldUnitaryNormStatement`: a number field `F`, a separable
quadratic extension `E/F`, a finite-dimensional central simple `E`-algebra `B` that is an
`F`-algebra through `E`, an `F`-linear involution `τ : FirstKindInvolution F B` acting on `E`
by `SU3Root.conjugation F E`, the nontrivial automorphism of `E/F`, and `z ∈ Eˣ` such that at
every place `v` of `F`, with `K_v = Global.placeCompletion F v`, some unit `x` of
`K_v ⊗[F] B` satisfies `x ∈ unitaryPoints τ K_v` (that is, `x τ_{K_v}(x) = 1`) and
`relativeNorm F E B K_v x = z ⊗ 1` in `E ⊗[F] K_v`.

The conclusion asserts the existence of:

1. a field `P` in the universe of `F`, with an `E`-algebra and an `F`-algebra structure
   forming a scalar tower `F → E → P`, finite-dimensional over `E` with
   `Module.finrank E B = Module.finrank E P ^ 2`, so that `[P : E]` is the degree `n` of `B`;
2. an `F`-linear involution `σ : FirstKindInvolution F P` acting on `E` by the nontrivial
   automorphism of `E/F` (on the commutative ring `P`, this is an `F`-algebra automorphism of
   order at most two);
3. an element `x ∈ P` with `x σ(x) = 1` and field norm `Algebra.norm E x = z`;
4. at every place `v` of `F`, an injective `K_v`-algebra homomorphism
   `φ_v : K_v ⊗[F] P → K_v ⊗[F] B` with `φ_v (1 ⊗ e) = 1 ⊗ e` for `e ∈ E` and
   `φ_v (σ_{K_v} y) = τ_{K_v} (φ_v y)`, where `σ_{K_v}` and `τ_{K_v}` are
   `σ.baseChange K_v` and `τ.baseChange K_v`.

Item 4 is word for word the local hypothesis of
`Langlands.CentralSimple.NumberFieldUnitaryEmbeddingStatement`, and items 1 and 2 are its
other hypotheses on `P` and `σ`. In the language of algebraic groups, `P` and `σ` define the
maximal torus `{p ∈ Pˣ : p σ(p) = 1}` of the unitary group of `(B, τ)` locally everywhere, and
`x` is a rational point of this torus whose norm is `z`.

## Provenance (derived)

This is the construction step in the proof of the unitary norm theorem in Platonov and
Rapinchuk, *Algebraic Groups and Number Theory* (1994), §6.7, proof of Theorem 6.28, printed
pp. 363–366 (PDF pp. 373–376), source `platonov-rapinchuk-1994-algebraic-groups-number-theory`.
There `P = L[t]/(f)` for a monic polynomial `f` over `L = E` of degree `n` that approximates
the characteristic polynomials of regular local solutions at a finite set of places, with
coefficients satisfying the symmetry conditions (6.44) and constant term `(-1)ⁿ z`; `x` is
the class of `t`, `σ` acts on `L` by `τ` and sends `x` to `x⁻¹`, and so `x σ(x) = 1` and
`N_{P/L}(x) = z`. The text then states
(p. 366): "for all `v` in `V^K` there exist embeddings `θ_v : P ⊗_K K_v → A ⊗_K K_v` as
algebras with involution", using the unitary version of Krasner's lemma (p. 364) at the
finitely many chosen places and Lemma 6.26 (p. 365) at the others. That `P` is a field, as the
Lean statement requires, comes from the two auxiliary places `v₁`, `v₂` chosen on p. 365: the
fixed algebra `P^σ` is a field of degree `n` over `K` because it is an unramified field
extension of degree `n` at `v₁`, and it is totally split at `v₂`, where `L` stays a field, so
`P = P^σ ⊗_K L` is a field (p. 366).

For odd degree, Steps 1 and 2 of §5.6 of Kneser, *Lectures on Galois Cohomology of Classical
Groups* (1969), printed pp. 79–81 (PDF pp. 85–87), source
`kneser-1969-galois-cohomology-classical-groups`, give the analogous construction of a
commutative separable `L`-algebra `L[X]/(f)` of degree `n` with involution and a unitary
element of norm `z`, with embeddings of algebras with involution at the places of the finite
set. There the polynomial is only required to be separable, so the algebra need not be a
field. Lemma 1 of §5.7 there (stated on printed p. 83, proved on pp. 86–87) gives embeddings of
algebras with involution at all places outside a finite set, in every degree.

The source's hypothesis `N_{L/K}(z) = 1` is not included, as in
`NumberFieldUnitaryNormStatement`: it follows from the local hypothesis at any one place.
