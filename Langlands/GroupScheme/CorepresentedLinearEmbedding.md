# Closed linear embeddings of corepresented group schemes over a field

Author: Worker 254.

This helper module proves the closed embedding theorem for the Library's
corepresented affine group schemes, `Langlands.GroupScheme.Corepresented.groupScheme F e`.
The proof follows Milne's Theorem 4.9 and Corollary 4.10. The final transfer to
an arbitrary affine group scheme is in
[`AffineLinearEmbeddingCorepresentedProof`](AffineLinearEmbeddingCorepresentedProof.md).

## Setting

`R : CommRingCat`, `F : CommAlgCat R ⥤ GrpCat` is a group-valued functor on
commutative `R`-algebras, and `e : (F ⋙ forget GrpCat).CorepresentableBy B` is
an actual corepresentation by an algebra `B`. All algebras, groups and schemes
live in one universe `u`. The group scheme `Corepresented.groupScheme F e` is
`Spec B` with the group law constructed from `F`, as in
[`Corepresented`](Corepresented.md).

## Source and provenance

The source is J. S. Milne, *Algebraic Groups: The Theory of Group Schemes of
Finite Type over a Field* (2017), source ID `milne-2017-algebraic-groups`,
SHA256 `899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`:
Theorem 4.9 and Corollary 4.10, printed p. 87 (PDF p. 103). It uses Proposition
4.7, printed p. 86 (PDF p. 102), through
[`ComoduleMatrixCoefficients`](ComoduleMatrixCoefficients.md).

Milne takes the Hopf algebra `O(G)` as given. Here the comultiplication and
counit of `B` are constructed from the group law of `F` by the Yoneda argument,
and their axioms are proved from the group axioms. The helper definitions below
are internal constructions for this proof, in the namespace
`Langlands.GroupScheme.Corepresented.LinearEmbedding`.

## The coalgebra structure of `B`

- `pt e f = e.homEquiv f` is the point classified by an algebra map
  `f : B ⟶ S`. `cls e x = e.homEquiv.symm x` is the classifying map of a point.
  `pt_comp` and `cls_map` restate naturality of the corepresentation.
- `sq B` is `B ⊗[R] B` as an object of `CommAlgCat R`. `inl B` and `inr B` are
  `b ↦ b ⊗ 1` and `b ↦ 1 ⊗ b`. `pair f g : B ⊗ B ⟶ S` is Mathlib's
  `Algebra.TensorProduct.lift f g` (`x ⊗ y ↦ f x * g y`).
- `comul e = cls e (pt e (inl B) * pt e (inr B)) : B ⟶ B ⊗ B` is the
  comultiplication. `pt_mul` proves `pt f * pt g = pt (comul e ≫ pair f g)`,
  so the group law is convolution. The proof: `pt (comul ≫ pair f g)` is
  `F(pair f g)` applied to `pt inl * pt inr`; `F(pair f g)` is a group
  homomorphism; and `inl ≫ pair f g = f`, `inr ≫ pair f g = g`. `cls_mul` is
  the same identity for classifying maps.
- `counit e = cls e 1 : B ⟶ R`, with `unitMap S` the structure map
  `R → S`. `cls_one` proves `cls e 1 = counit e ≫ unitMap S`, because `F`
  sends the identity point over `R` to the identity point over `S`.
- `comulL e` and `counitL e` are these algebra maps as `R`-linear maps.

Then the axioms of
[`ComoduleMatrixCoefficients`](ComoduleMatrixCoefficients.md) are proved:

- `rightCounit`: from `pt (𝟙 B) * 1 = pt (𝟙 B)`, `comul ≫ pair 𝟙 (counit ≫ unitMap B)` is the
  identity. On pure tensors this pair map is `p ⊗ q ↦ ε(q) • p`, which is
  `rid ∘ (id ⊗ ε)`.
- `leftCounit`: the same from `1 * pt (𝟙 B) = pt (𝟙 B)`.
- `coassoc`: let `i₁, i₂, i₃ : B ⟶ (B ⊗ B) ⊗ B` be the three factor inclusions.
  Associativity `(pt i₁ * pt i₂) * pt i₃ = pt i₁ * (pt i₂ * pt i₃)` and
  injectivity of `pt` give an equality of algebra maps
  `comul ≫ pair (comul ≫ pair i₁ i₂) i₃ = comul ≫ pair i₁ (comul ≫ pair i₂ i₃)`.
  Tensor inductions (`pair_i₁_i₂`, `pair_i₂_i₃`, `i₁_mul_assoc_symm`) identify the
  first pair map with `Δ ⊗ id` and the second with `assoc⁻¹ ∘ (id ⊗ Δ)`. This
  gives `assoc ∘ (Δ ⊗ id) ∘ Δ = (id ⊗ Δ) ∘ Δ`.

## The representation

Assume `a : Matrix n n B` satisfies `Δ (a i j) = Σ_l a i l ⊗ a l j` and
`ε (a i j) = 1 i j`.

- `coeffHom e a hmul hone S : F.obj S →* Matrix n n S` sends `x` to the matrix
  `(cls e x)(a i j)`. It preserves `1` by `cls_one` and the counit identity. It
  preserves products by `cls_mul`, the multiplicativity identity and
  `Matrix.mul_apply`.
- `toGL e a hmul hone : F ⟶ GeneralLinear.functor n R` composes this with
  `MonoidHom.toHomUnits`. A monoid homomorphism from a group lands in the units,
  so every point gives an invertible matrix. Naturality follows from `cls_map`.
- `isClosedSubgroup_toGL`: suppose `s ⊆ B` generates `B` as an `R`-algebra and lies in
  the `R`-span of the entries of `a`. Then
  `IsClosedSubgroup (groupSchemeMap e (GeneralLinear.corepresentableBy n R) (toGL …))`.
  By `Corepresented.groupSchemeMap_hom`, the underlying scheme morphism is
  `Spec.map` of the classifying map `GeneralLinear.classify g` of the matrix
  `g = toGL(pt (𝟙 B))`. The entries of `g` are the `a i j`. `classify_entry`
  puts each `a i j` in the range of `classify g`. Hence the range contains their
  span, then `s`, then `Algebra.adjoin R s = ⊤`. Thus `classify g` is
  surjective, and `IsClosedImmersion.spec_of_surjective` concludes.

## Main theorem

`Corepresented.exists_isClosedSubgroup k e` states: for a field `k : Type u`, a
group-valued functor `F` on `CommAlgCat (CommRingCat.of k)`, a corepresentation
`e` by `B`, and `[Algebra.FiniteType (CommRingCat.of k) B]`, there exist `N : ℕ`
and an actual group-scheme homomorphism
`ρ : groupScheme F e ⟶ GeneralLinear.groupScheme (Fin N) (CommRingCat.of k)` with
`IsClosedSubgroup ρ`.

Proof: choose a finite generating set `s` from `Algebra.FiniteType`, and apply
`Comodule.exists_matrix` to `comulL e`, `counitL e` and `s`, using `coassoc`,
`leftCounit` and `rightCounit`. This gives `N` and `a`. Then take
`ρ = groupSchemeMap e _ (toGL e a …)` and apply `isClosedSubgroup_toGL`.

No smoothness, reducedness, connectedness or perfectness of `k` is assumed. The
module adds no axioms.
