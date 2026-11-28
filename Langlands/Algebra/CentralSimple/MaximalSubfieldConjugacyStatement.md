# Conjugacy and self-centralization of maximal subfields after scalar extension

Module: `Langlands.Algebra.CentralSimple.MaximalSubfieldConjugacyStatement`.

`Langlands.CentralSimple.MaximalSubfieldConjugacyStatement.{u}` is a proposition; this module
states it and does not prove it.

## The statement

It quantifies over fields `F`, `E`, `P`, `K` and a ring `B`, all in one universe `u`, with:

* `E` a finite separable extension of `F` (`FiniteDimensional F E`,
  `Algebra.IsSeparable F E`);
* `B` a finite-dimensional central simple `E`-algebra (`FiniteDimensional E B`,
  `Algebra.IsCentral E B`, `IsSimpleRing B`) that is an `F`-algebra through `E`
  (`IsScalarTower F E B`);
* `P` a finite separable field extension of `E` (`FiniteDimensional E P`,
  `Algebra.IsSeparable E P`) that is an `F`-algebra through `E` (`IsScalarTower F E P`);
* `K` an arbitrary field extension of `F` (`Algebra F K`).

Assume `Module.finrank E B = Module.finrank E P ^ 2`, and let
`f g : K ⊗[F] P →ₐ[K] K ⊗[F] B` be injective `K`-algebra homomorphisms with
`f (1 ⊗ e) = 1 ⊗ e` and `g (1 ⊗ e) = 1 ⊗ e` for every `e ∈ E` (the images of `E` in `P` and
in `B`). The conclusion is the conjunction of:

1. (Skolem–Noether) there is a unit `u` of `K ⊗[F] B` with `g y = u * f y * u⁻¹` for every
   `y ∈ K ⊗[F] P`;
2. (self-centralization) every `x ∈ K ⊗[F] B` with `x * f y = f y * x` for all `y` lies in
   the range of `f`.

For `K = F` this is the classical statement for a maximal subfield of a central simple
algebra (after the identifications `F ⊗[F] P ≃ P` and `F ⊗[F] B ≃ B`). For a completion
`K = F_v` of a global field it is the local statement used for embedding problems of fields
with involution.

## Source and derivation

G. Prasad and A. S. Rapinchuk, *Local-global principles for embedding of fields with
involution into simple algebras with involution*, Comment. Math. Helv. 85 (2010), cited in its
arXiv version 0806.0596v5 (source `prasad-rapinchuk-2010-embedding-fields-involution`), §3,
p. 10. In the proof of Proposition 3.1 the authors use "the 'Skolem-Noether Theorem' for
commutative étale subalgebras of dimension `n`" (citing Kneser, Hilfssatz 3.5) and the fact
that "`ε(E)` is its own centralizer in `A`". Footnote 1 on p. 10 proves the conjugacy: if `A`
is a central simple `L`-algebra of dimension `n²` and `E` a commutative étale `L`-algebra of
dimension `n`, any two `L`-embeddings `ι₁, ι₂ : E ↪ A` satisfy `ι₂(x) = g⁻¹ ι₁(x) g` for
some `g ∈ A×`.

The present statement is derived from these two facts over a field `L`. Since `E/F` is finite
separable, `R = K ⊗[F] E` is a finite product of fields `R_j`, each containing `E`. Then
`K ⊗[F] B ≃ R ⊗[E] B` is the product of the central simple `R_j`-algebras `R_j ⊗[E] B` of
degree `n = [P : E]`, and `K ⊗[F] P ≃ R ⊗[E] P` is the product of the commutative étale
`R_j`-algebras `R_j ⊗[E] P` of dimension `n`, `P/E` being separable. A `K`-algebra
homomorphism that is the identity on `E` is `R`-linear, so `f` and `g` are products of
injective `R_j`-algebra homomorphisms `R_j ⊗[E] P → R_j ⊗[E] B`. The field case on each factor
gives the conjugating units and the self-centralization factorwise; their product is a unit
`u` as in assertion 1, and assertion 2 follows componentwise.
