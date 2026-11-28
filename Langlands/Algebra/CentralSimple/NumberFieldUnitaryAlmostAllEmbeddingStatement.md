# Local embeddings of fields with involution at almost all places

Module: `Langlands.Algebra.CentralSimple.NumberFieldUnitaryAlmostAllEmbeddingStatement`.

`Langlands.CentralSimple.NumberFieldUnitaryAlmostAllEmbeddingStatement.{u}` is a proposition;
this module states it and does not prove it.

## The statement

The data are those of `Langlands.CentralSimple.NumberFieldUnitaryNormStatement` without the
element `z`: a number field `F`, a separable quadratic extension `E/F`, a finite-dimensional
central simple `E`-algebra `B` that is an `F`-algebra through `E`, and an involution
`τ : FirstKindInvolution F B` (an `F`-linear anti-automorphism of order two) acting on `E` by
`SU3Root.conjugation F E`, the nontrivial automorphism of `E/F`. Write `n` for the degree of
`B`, so that `Module.finrank E B = n ^ 2`.

The conclusion asserts a finite set `S : Finset (Global.Place F)` of places of `F` such that
for every place `v ∉ S`, with `K_v = Global.placeCompletion F v` the actual completion, and for
every field `P` in the universe of `F` with

1. an `E`-algebra and an `F`-algebra structure forming a scalar tower `F → E → P`, finite
   dimensional over `E`, with `Module.finrank E B = Module.finrank E P ^ 2` (so `[P : E] = n`),
2. an involution `σ : FirstKindInvolution F P` acting on `E` by the nontrivial automorphism of
   `E/F`,

there is an injective `K_v`-algebra homomorphism `φ : K_v ⊗[F] P → K_v ⊗[F] B` with
`φ (1 ⊗ e) = 1 ⊗ e` for `e ∈ E` and `φ (σ_{K_v} y) = τ_{K_v} (φ y)` for all `y`, where
`σ_{K_v}` and `τ_{K_v}` are `σ.baseChange K_v` and `τ.baseChange K_v`. The set `S` depends
only on `F`, `E`, `B` and `τ`, not on `P` or `σ`.

The conclusion for one `v` is word for word the local hypothesis of
`Langlands.CentralSimple.NumberFieldUnitaryEmbeddingStatement` and the local clause of the
conclusion of `Langlands.CentralSimple.NumberFieldUnitaryNormTorusStatement`. The statement
does not require `S` to contain the archimedean places.

## Provenance (derived)

This is Lemma 6.26 of Platonov and Rapinchuk, *Algebraic Groups and Number Theory* (1994),
§6.7, printed p. 365 (PDF p. 375), source
`platonov-rapinchuk-1994-algebraic-groups-number-theory`: "There exists a finite subset `S₀`
of `V^K` containing `V_∞^K` such that, for `v ∉ S₀`, any `n`-dimensional commutative
semisimple `L ⊗_K K_v`-algebra `B_v` with involution, whose restriction to `L` is `τ`, can be
embedded in `A ⊗_K K_v` as the algebra with involution." (There `K` is the number field, `L`
the quadratic extension and `A` the algebra, here `F`, `E` and `B`.) The same assertion is
Lemma 1 of §5.7 of Kneser, *Lectures on Galois Cohomology of Classical Groups* (1969), stated
on printed p. 83 (PDF p. 89) and proved on printed pp. 86–87 (PDF pp. 92–93), source
`kneser-1969-galois-cohomology-classical-groups`, for commutative separable algebras with
involution of dimension `n` over `L K_v`.

The Lean statement asserts the source's conclusion only for the algebras `K_v ⊗[F] P` coming
from a global field `P` of degree `n` over `E` with an involution `σ` as above. Such an
algebra is commutative and semisimple, free of rank `n` over `E ⊗[F] K_v`, and `σ_{K_v}`
restricts on `E ⊗[F] K_v` to the extension of the nontrivial automorphism, so the Lean
statement is a special case of the source's. An embedding "as the algebra with involution"
that is the identity on `L` is written as an injective `K_v`-algebra homomorphism that is the
identity on `E` and intertwines the involutions. The source's requirement that `S₀` contain
the archimedean places is not part of the Lean statement: a finite set with the stated property
remains one after the archimedean places are added.

The proofs in the sources: at split places `B ⊗_F K_v` is a product `A₁ × A₂` exchanged by
`τ`, with `A₁` a matrix algebra outside a finite set, and an algebra with involution embeds
through the regular representation of its first factor; at nonsplit places outside a finite
set `τ` is the adjoint involution of a unimodular Hermitian form, and the algebra with
involution embeds because a suitably scaled trace form is a unimodular Hermitian form of the
same dimension (Kneser), or because the special unitary group is quasi-split there
(Platonov–Rapinchuk, using Proposition 6.19).
