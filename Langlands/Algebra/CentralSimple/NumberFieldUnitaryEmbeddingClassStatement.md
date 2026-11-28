# Global fixed-field twists with everywhere local unitary solutions

Module: `Langlands.Algebra.CentralSimple.NumberFieldUnitaryEmbeddingClassStatement`.

`Langlands.CentralSimple.NumberFieldUnitaryEmbeddingClassStatement.{u}` is a proposition; this
module states it and does not prove it.

## The statement

It quantifies over the data of `NumberFieldUnitaryEmbeddingStatement` (module
`Langlands.Algebra.CentralSimple.NumberFieldUnitaryEmbeddingStatement`): a number field `F`,
a separable quadratic extension `E/F`, a finite-dimensional central simple `E`-algebra `B`
that is an `F`-algebra through `E`, a field `P` that is a finite-dimensional `E`-algebra and
an `F`-algebra through `E`, all in one universe `u`, and `F`-linear involutions
`τ : FirstKindInvolution F B` and `σ : FirstKindInvolution F P` acting on `E` by
`SU3Root.conjugation F E`, with `Module.finrank E B = Module.finrank E P ^ 2`. It further
takes:

* an `E`-algebra homomorphism `ε : P →ₐ[E] B`;
* a unit `g` of `B` with `τ g = g` and `τ (ε p) = g * ε (σ p) * g⁻¹` for all `p ∈ P`, so that
  `p ↦ ε p` intertwines `σ` with the involution `x ↦ g⁻¹ τ(x) g`.

Write `K_v = Global.placeCompletion F v`, `ε_v = id ⊗ ε : K_v ⊗[F] P → K_v ⊗[F] B`
(`Algebra.TensorProduct.map (AlgHom.id K_v K_v) (ε.restrictScalars F)`), and `σ_v`, `τ_v`
for `σ.baseChange K_v`, `τ.baseChange K_v`. The hypothesis is that at every place `v` of `F`
there are a unit `a_v` of `K_v ⊗[F] P` with `σ_v a_v = a_v` and a unit `h_v` of
`K_v ⊗[F] B` with

```text
(1 ⊗ g) * ε_v(a_v) = h_v * τ_v(h_v).
```

The conclusion is that there is `a ∈ P` with `a ≠ 0` and `σ a = a` such that at every place
`v` there is a unit `h` of `K_v ⊗[F] B` with `1 ⊗ (g * ε a) = h * τ_v(h)`.

So a family of local solutions `a_v` of the twisted norm equation can be replaced by one
global `σ`-fixed element `a`, keeping local solvability at every place. The statement does not
ask for a global solution `h ∈ Bˣ` of `g ε(a) = h τ(h)`; that is the content of Landherr's
theorem (`NumberFieldLandherrStatement`).

## Source

G. Prasad and A. S. Rapinchuk, *Local-global principles for embedding of fields with
involution into simple algebras with involution*, Comment. Math. Helv. 85 (2010), cited in its
arXiv version 0806.0596v5 (source `prasad-rapinchuk-2010-embedding-fields-involution`).

The equation is condition (iii) of Theorem 3.2, p. 11: with `θ = τ ∘ Int g`, `τ(g) = g`, and
`ε(σ(x)) = θ(ε(x))` as in Proposition 3.1, p. 10, an embedding `(E, σ) ↪ (A, τ)` of algebras
with involution exists if and only if "`gε(b) = τ(h)h` for some `b ∈ F×` and `h ∈ A×`", where
`F = E^σ`. (The source's `L`, `K`, `A`, `E`, `F` are `E`, `F`, `B`, `P`, `P^σ` here; replacing
`h` by `τ(h)` turns `τ(h)h` into `h τ(h)`.) In the proof of Theorem 4.1, pp. 13–14, local
embeddings give local solutions `(a_v, h_v)` of this equation at every place (equation (9)).

The statement is a consequence of Theorem 4.1 of the same paper (assertion (i) of Theorem A,
p. 2) for number fields. Under its hypotheses, the computation proving (iii) ⇒ (i) in
Theorem 3.2, which uses only identities in the ring, turns the local solutions into injective
homomorphisms `y ↦ τ_v(h_v) ε_v(y) τ_v(h_v)⁻¹` from `K_v ⊗[F] P` to `K_v ⊗[F] B` that are the
identity on `E` and intertwine `σ_v` and `τ_v`. Theorem 4.1 then gives a global embedding of
`(P, σ)` into `(B, τ)`; by the Skolem–Noether theorem it is a conjugate of `ε`, and
Theorem 3.2, (i) ⇒ (iii), gives a nonzero `σ`-fixed `a ∈ P` with `g ε(a) = h τ(h)` for a unit
`h` of `B`, an equation that then holds at every place.

## Remark on proofs

The proof of Theorem 4.1 in the source uses the Hasse principle for `SU(A, τ)` (Lemma 4.3,
pp. 16–17), which Platonov and Rapinchuk deduce from Landherr's theorem and the unitary norm
theorem. The following argument establishes the present statement without it.

1. Replacing `a_v` by `a_v p σ_v(p)` with `p` a unit of `K_v ⊗[F] P` replaces `h_v` by
   `τ_v(ε_v(p)) h_v`, so local solvability depends only on the class of `a_v` modulo such
   norms.
2. Outside a finite set `S` of places one may take `a_v = 1`: at a place split in `E`,
   `K_v ⊗[F] B` is a product `B₁ × B₁^op` on which `τ_v` is the exchange involution, and every
   `τ_v`-symmetric unit has the form `h τ_v(h)` (the source, p. 14 and footnote 2). At a
   finite place, a symmetric unit `y` has the form `h τ_v(h)` if and only if its reduced norm
   is a norm from `E ⊗[F] K_v` (Platonov and Rapinchuk, *Algebraic Groups and Number Theory*,
   1994, source `platonov-rapinchuk-1994-algebraic-groups-number-theory`, Remark on printed
   p. 363, PDF p. 373); at a finite place unramified in `E` at which `Nrd(g)` is a unit, it is
   a norm of a unit.
3. Taking reduced norms in `(1 ⊗ g) ε_v(a_v) = h_v τ_v(h_v)` shows that the norm of `a_v` from
   `K_v ⊗[F] P` to `E ⊗[F] K_v`, times `Nrd(g) ∈ F×`, is a norm from `E ⊗[F] K_v`.
4. With `F' = P^σ`, so that `P ≃ F' ⊗[F] E`, the norm-residue symbol of `P/F'` at a place `w`
   of `F'` above `v` is the norm-residue symbol of `E/F` at `v` composed with the norm from
   `F'_w` to `K_v`. By step 3 the product over all `w` of the symbols of the components of the
   `a_v` is the product over all `v` of the symbols of `E/F` at `Nrd(g)`, which is trivial by
   global reciprocity. Global class field theory for the quadratic extension `P/F'` then gives
   `a ∈ F'×` in the class of `a_v` at every place.
