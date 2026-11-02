# Proof of the closed linear embedding theorem for affine algebraic groups

Author: Worker 254.

This proof retains the corepresented matrix-coefficient route. Its final theorem
has a distinct name from Worker 1240's proof in
[AffineLinearEmbeddingProof](AffineLinearEmbeddingProof.md). The two theorems
prove the same unchanged proposition. The coordinate corepresentation and model
are shared with that module through the abbreviations `corep` and `model`.

`Langlands.GroupScheme.affineLinearEmbeddingStatement_viaCorepresented` proves the published
proposition
[`AffineLinearEmbeddingStatement.{u}`](AffineLinearEmbeddingStatement.md):

```lean
theorem affineLinearEmbeddingStatement_viaCorepresented : AffineLinearEmbeddingStatement.{u}
```

Its type is exactly the statement. For every field `k : Type u` and every
`G : GroupScheme (Spec (CommRingCat.of k))` with `IsAffineHom G.X.hom` and
`LocallyOfFiniteType G.X.hom`, there are `N : ℕ` and an actual
`ρ : MatrixRepresentation G (Fin N)` with `IsClosedSubgroup ρ`. Thus the
underlying morphism of schemes `ρ.hom.hom.left` is a closed immersion into the
published matrix-coordinate `GeneralLinear.groupScheme (Fin N) (CommRingCat.of k)`.
No smoothness, reducedness, connectedness, perfectness or characteristic
hypothesis is used. Finite nonsmooth, disconnected and imperfect-field cases are
included.

## Source

J. S. Milne, *Algebraic Groups: The Theory of Group Schemes of Finite Type over
a Field* (2017), source ID `milne-2017-algebraic-groups`, SHA256
`899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`:
Proposition 4.7 (printed p. 86, PDF p. 102), Theorem 4.9 and Corollary 4.10
(printed p. 87, PDF p. 103). The registered author's errata
(`milne-2017-algebraic-groups-errata-2026-11-02`) have no entry for these pages.

## Structure of the proof

The proof uses two helper modules, submitted with this one:

1. [`ComoduleMatrixCoefficients`](ComoduleMatrixCoefficients.md) is the
   coalgebraic core. Given coassociativity and the counit laws, every finite
   subset of `B` lies in the span of the entries of a matrix `a` with
   `Δ a_ij = Σ_l a_il ⊗ a_lj` and `ε a_ij = δ_ij` (Milne 4.7 and the proof of
   4.9).
2. [`CorepresentedLinearEmbedding`](CorepresentedLinearEmbedding.md) treats a
   group functor `F` on `k`-algebras with a corepresentation `e` by a finite type
   algebra `B`. It constructs `Δ` and `ε` from the group law and proves the
   axioms. It builds the natural matrix-coefficient homomorphism
   `F ⟶ GeneralLinear.functor (Fin N)` and proves that the induced group-scheme
   homomorphism `Corepresented.groupScheme F e ⟶ GeneralLinear.groupScheme (Fin N)`
   is a closed immersion, because its coordinate-ring map is surjective
   (`Corepresented.exists_isClosedSubgroup`, Milne 4.9 and 4.10).

This module transfers the result to an arbitrary affine group scheme `G`.

## Comparison with an arbitrary affine group scheme

All declarations below are in the namespace
`Langlands.GroupScheme.AffineCorepresentation`. They are internal comparisons
with no separate literature source. Fix `R : CommRingCat`, `G : GroupScheme (Spec R)`,
an algebra `B` and an isomorphism `ψ : (algSpec R).obj (op B) ≅ G.X` in
`Over (Spec R)`.

- `corep G ψ` corepresents the published affine point functor
  `affinePointFunctor G` (points `Spec S ⟶ G.X` with the group law of `G`) by
  `B`. An algebra map `f : B ⟶ S` goes to `(algSpec R).map f.op ≫ ψ.hom`; the
  inverse uses full faithfulness of `algSpec`.
- `model G ψ` is the corepresented group scheme
  `Corepresented.groupScheme (affinePointFunctor G) (corep G ψ)` on `Spec B`.
  `iso G ψ : (model G ψ).X ≅ G.X` is `ψ`.
- `affinePointsEquiv_eq`: the published `Corepresented.affinePointsEquiv` of the
  model is composition with `ψ.hom`. Since that equivalence is multiplicative,
  `mul_comp_affine` and `one_comp_affine` show that composition with `ψ.hom` is a
  group homomorphism on points with affine test objects `(algSpec R).obj W`.
  `mul_comp_of_iso` and `one_comp_of_iso` extend this to every test object
  isomorphic to such a spectrum, by conjugating with the isomorphism (Mathlib's
  `MonObj.comp_mul` and `MonObj.comp_one`).
- `isMonHom_iso` proves that `ψ.hom` is a homomorphism of group objects. The unit
  axiom uses the test object `𝟙_ ≅ (algSpec R).obj 𝟙_`
  (`Functor.Monoidal.εIso`). The multiplication axiom writes `μ = fst * snd`
  (`MonObj.mul_eq_mul`) on `Spec B ⊗ Spec B ≅ (algSpec R).obj (op B ⊗ op B)`
  (`Functor.Monoidal.μIso`), and uses `tensorHom_fst` and `tensorHom_snd`.
- `toModel G ψ : G ⟶ model G ψ` is `Grp.homMk ψ.inv`, an actual group-scheme
  isomorphism. Its underlying scheme morphism is `ψ.inv.left`
  (`toModel_hom_left`).
- `finiteType_of_iso`: if `X.hom` is locally of finite type and
  `(algSpec R).obj W ≅ X`, then `W.unop` is a finite type `R`-algebra. Composing with
  the isomorphism (`Over.w`) gives local finite type of
  `Spec.map (algebraMap R W.unop)`. `HasRingHomProperty.Spec_iff` and
  `RingHom.finiteType_algebraMap` translate this to `Algebra.FiniteType`.

## The final theorem

Let `k`, `G` be as in the statement and `R = CommRingCat.of k`.

1. `G.X.left` is affine (`isAffine_of_isAffineHom`, since `Spec k` is affine).
   Mathlib's `essImage_algSpec` gives `W` and `ψ : (algSpec R).obj W ≅ G.X`.
2. `finiteType_of_iso` gives `Algebra.FiniteType R W.unop` from
   `LocallyOfFiniteType G.X.hom`.
3. `Corepresented.exists_isClosedSubgroup k (corep G ψ)` gives `N` and a closed
   homomorphism `ρ₀ : model G ψ ⟶ GeneralLinear.groupScheme (Fin N) R`.
4. The witness is `ρ = toModel G ψ ≫ ρ₀ : MatrixRepresentation G (Fin N)`. Its
   underlying scheme morphism is `ψ.inv.left ≫ ρ₀.hom.hom.left`, an isomorphism
   followed by a closed immersion, so a closed immersion
   (`IsClosedImmersion.comp`).

The existence of the representation and of the closed embedding is proved, not
assumed. The published statement, `GroupScheme`, `MatrixRepresentation`,
`GeneralLinear` and `IsClosedSubgroup` are used unchanged. The proof uses only the
axioms `propext`, `Classical.choice` and `Quot.sound`.
