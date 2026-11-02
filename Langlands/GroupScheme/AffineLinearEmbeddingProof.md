# Closed linear embeddings of affine algebraic groups over fields: proof

Author: Worker 1240.

An independently accepted corepresented matrix-coefficient proof by Worker 254
is retained in
[AffineLinearEmbeddingCorepresentedProof](AffineLinearEmbeddingCorepresentedProof.md)
as `affineLinearEmbeddingStatement_viaCorepresented`. Both proofs use the same
coordinate corepresentation and model defined below.

The theorem `Langlands.GroupScheme.affineLinearEmbeddingStatement.{u}` has type
exactly `Langlands.GroupScheme.AffineLinearEmbeddingStatement.{u}`, imported
unchanged from [`AffineLinearEmbeddingStatement`](AffineLinearEmbeddingStatement.md).
For every field `k : Type u` and every
`G : GroupScheme (Spec (CommRingCat.of k))` whose structure morphism `G.X.hom` is
affine (`IsAffineHom`) and locally of finite type (`LocallyOfFiniteType`), it
produces `N : ℕ` and `ρ : MatrixRepresentation G (Fin N)` such that
`IsClosedSubgroup ρ`. That is, the underlying morphism of schemes `ρ.hom.hom.left`
is a closed immersion. The proof adds no hypothesis on `k` or `G`. It uses only
the axioms `propext`, `Classical.choice` and `Quot.sound`.

## Module structure

- [`AffineLinearEmbedding/Comodule`](AffineLinearEmbedding/Comodule.md):
  linear algebra over a field. Every finite subset of a coalgebra lies in the
  span of the entries of a matrix `M` with
  `comul (M i j) = ∑ l, M i l ⊗ M l j` and `counit (M i j) = δᵢⱼ`
  (`exists_matrix_coefficients`).
- [`AffineLinearEmbedding/Coordinate`](AffineLinearEmbedding/Coordinate.md): for
  a group functor `F` corepresented by `B`, the bialgebra structure on `B` from the
  group law (`bialgebra`). It also gives the homomorphism
  `toGLHom : Corepresented.groupScheme F e ⟶ GeneralLinear.groupScheme (Fin N) R`
  attached to such a matrix. This is a closed immersion when the entries generate
  `B` (`isClosedSubgroup_toGLHom`).
- This module: the comparison of `G` with the affine group scheme built from
  its coordinate algebra, and the final assembly.

## Comparison with a corepresented model

The declarations below live in `Langlands.GroupScheme.AffineLinearEmbedding`. Fix
`R : CommRingCat`, `G : GroupScheme (Spec R)`, `B : CommAlgCat R` and an
isomorphism `j : (algSpec R).obj (op B) ≅ G.X` in `Over (Spec R)`. Here
`algSpec R` is Mathlib's relative spectrum functor `(CommAlgCat R)ᵒᵖ ⥤ Over (Spec R)`.

- `corepresentableBy G j` corepresents the set-valued algebra-point functor
  `G.affinePointFunctor ⋙ forget GrpCat` by `B`. The Library's
  `G.affinePointFunctor` sends `A` to the group of morphisms
  `(algSpec R).obj (op A) ⟶ G.X`. The bijection sends `f : B ⟶ A` to
  `(algSpec R).map f.op ≫ j.hom`. Its inverse sends `x` to the preimage of
  `x ≫ j.inv` under the fully faithful functor `algSpec R`
  (`algSpec.fullyFaithful`). Naturality is functoriality of `algSpec R`.
- `model G j` is `Corepresented.groupScheme G.affinePointFunctor (corepresentableBy G j)`.
  This is the Library's affine group scheme with underlying object
  `(algSpec R).obj (op B)`. Its group structure is built from the corepresentation.
- `comp_hom`: for `T : Over (Spec R)` and `x : T ⟶ (model G j).X`,
  `x ≫ j.hom = (algΓAlgSpecAdjunction R).unit.app T ≫ Corepresented.pointsEquiv … T x`.
  Here `Corepresented.pointsEquiv … T x` is the point of `G.affinePointFunctor` over
  the relative global sections of `T`. The proof unfolds
  `Corepresented.pointsEquiv_apply`. The right side becomes `unit ≫ (algSpec R).map y ≫ j.hom`,
  where `y` is the adjoint transpose of `x`. Then `Adjunction.homEquiv_unit`
  identifies `unit ≫ (algSpec R).map y` with `x`.
- `pointsMulEquiv G j T : (T ⟶ (model G j).X) ≃* (T ⟶ G.X)` is `x ↦ x ≫ j.hom`, with
  inverse `y ↦ y ≫ j.inv`. Multiplicativity: by `comp_hom` both sides are
  precompositions with the unit. `Corepresented.pointsEquiv` is a group
  isomorphism (`map_mul`). Precomposition preserves the pointwise product of
  morphisms into a group object (`MonObj.comp_mul`).
- `modelIso G j : model G j ≅ G` is an isomorphism of group objects in
  `Over (Spec R)`. The maps `pointsMulEquiv` form a natural isomorphism between the
  group-valued Yoneda functors of `model G j` and `G`. Naturality is associativity
  of composition. Mathlib's `yonedaGrpFullyFaithful` says that the group-valued
  Yoneda embedding of `Grp (Over (Spec R))` is fully faithful. Its `preimageIso`
  gives `modelIso`.

## Proof of `affineLinearEmbeddingStatement`

Fix `k`, `G`, `hAff : IsAffineHom G.X.hom` and `hLFT : LocallyOfFiniteType G.X.hom`,
and write `R = CommRingCat.of k`.

1. *Affine coordinate algebra.* The base `Spec R` is affine and `G.X.hom` is
   affine, so `G.X.left` is affine (`isAffine_of_isAffineHom`). Mathlib's
   `essImage_algSpec` gives `B : CommAlgCat R` and an isomorphism
   `j : (algSpec R).obj (op B) ≅ G.X`.
2. *Finite type.* By `Over.w`, the structure morphism of `(algSpec R).obj (op B)`
   equals `j.hom.left ≫ G.X.hom`. The first factor is an isomorphism, so this
   composite is locally of finite type. `HasRingHomProperty.Spec_iff` and
   `RingHom.finiteType_algebraMap` translate this into `Algebra.FiniteType R B`.
   Choose a finite set `s : Finset B` with `Algebra.adjoin R s = ⊤`.
3. *Matrix coefficients.* Let `e = corepresentableBy G j`. Equip `B` with the
   coalgebra `(bialgebra e).toCoalgebra` from `Coordinate`, and `R` with the field
   structure of `k`. Apply `exists_matrix_coefficients` to `s`. This gives
   `N`, `M`, `hcomul`, `hcounit`, and `s ⊆ span (entries of M)`. The coalgebra
   maps of `(bialgebra e).toCoalgebra` are definitionally the linear maps
   underlying `comul e` and `counit e`. So `hcomul` and `hcounit` are exactly the
   hypotheses of `toGLHom`.
4. *Generation.* The span of the entries lies in the subalgebra they generate
   (`Algebra.span_le_adjoin`). Hence `s` lies in that subalgebra, and
   `Algebra.adjoin_le` together with `Algebra.adjoin R s = ⊤` shows that the
   entries of `M` generate `B`.
5. *The representation.* Put
   `ρ = (modelIso G j).inv ≫ toGLHom e M hcomul hcounit`, a morphism
   `G ⟶ GeneralLinear.groupScheme (Fin N) R`, that is, a
   `MatrixRepresentation G (Fin N)`.
6. *Closed immersion.* The underlying scheme morphism of `ρ` is the composite
   `(modelIso G j).inv.hom.hom.left ≫ (toGLHom e M hcomul hcounit).hom.hom.left`.
   The first factor is an isomorphism, the image of an isomorphism under the
   forgetful functors. The second is a closed immersion by
   `isClosedSubgroup_toGLHom` and step 4. Closed immersions contain
   isomorphisms and are closed under composition, so instance search proves
   `IsClosedImmersion` of the composite.

## Relation to the literature

The statement is J. S. Milne, *Algebraic Groups* (2017), Theorem 4.9 and
Corollary 4.10 (printed p. 87), as explained in the statement's Markdown. The
proof follows Milne's route. Take a finite-dimensional subcomodule of the
regular comodule `O(G)` that contains algebra generators (Proposition 4.7, here
`exists_matrix_coefficients`). Its matrix coefficients give a homomorphism to
`GL_N`. The induced map of coordinate rings is surjective because of the counit
identity `e_j = ∑ᵢ ε(eᵢ) a_{ij}`. The author's errata in the literature
collection (`J. S. Milne - Errata for Algebraic Groups (2017), HTML snapshot
2026-11-02.html`) list no correction for printed pp. 86–87.

The formal route differs from Milne in three ways. First, the comultiplication
and counit of `O(G)` are defined from the group law on algebra points, through the
corepresentation by `B`. Second, `G` is replaced by the isomorphic model
`Corepresented.groupScheme`, on which homomorphisms to `GL_N` come from natural
transformations of point functors (`Corepresented.groupSchemeMap`). Third,
`modelIso` transports the result back to `G`.
