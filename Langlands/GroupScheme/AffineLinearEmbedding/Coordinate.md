# The coordinate bialgebra of a corepresented group functor and its matrix embeddings

Author: Worker 1240.

This helper module serves the closed linear embedding theorem
`Langlands.GroupScheme.affineLinearEmbeddingStatement`
([`AffineLinearEmbeddingProof`](../AffineLinearEmbeddingProof.md)). Its input is the
data used by the Library's [`Corepresented`](../Corepresented.md) construction: a
commutative ring `R : CommRingCat`, a group-valued functor
`F : CommAlgCat R ⥤ GrpCat`, an algebra `B : CommAlgCat R` and a corepresentation
`e : (F ⋙ forget GrpCat).CorepresentableBy B`. Thus `e.homEquiv` is a natural
bijection `(B ⟶ A) ≃ F.obj A`.

The module does two things.

1. It makes `B` into an `R`-bialgebra. The comultiplication and the counit come
   from the group law of `F`, not from Mathlib's Hopf algebra structure on global
   sections.
2. It shows that a matrix `M` over `B` with matrix-coefficient identities gives a
   homomorphism `Corepresented.groupScheme F e ⟶ GeneralLinear.groupScheme (Fin N) R`.
   This homomorphism is a closed immersion when the entries of `M` generate `B`.

All declarations live in the namespace `Langlands.GroupScheme.AffineLinearEmbedding`.
`includeLeft`, `includeRight` and `productMap` are the Mathlib maps
`Algebra.TensorProduct.includeLeft`, `includeRight` and `productMap`.

## Points classified by algebra maps

- `pt e f : F.obj A` is the point `e.homEquiv (CommAlgCat.ofHom f)` classified by an
  algebra map `f : B →ₐ[R] A`.
- `pt_injective`: `pt e f = pt e g` implies `f = g`.
- `pt_homEquiv_symm`: `pt e (e.homEquiv.symm x).hom = x`.
- `pt_comp`: `pt e (g.comp f) = F.map (CommAlgCat.ofHom g) (pt e f)`. This is the
  naturality `e.homEquiv_comp`.

## Comultiplication and counit

- `comul e : B →ₐ[R] B ⊗[R] B` is the algebra map classifying the product
  `pt e includeLeft * pt e includeRight` in the group `F.obj (B ⊗[R] B)`
  (`pt_comul`).
- `counit e : B →ₐ[R] R` is the algebra map classifying the identity element of
  `F.obj R`.

Since every `F.map` is a group homomorphism, these maps compute the group law:

- `pt_comp_comul`: if `l : B ⊗[R] B →ₐ[R] A` satisfies `l.comp includeLeft = f` and
  `l.comp includeRight = g`, then `pt e (l.comp (comul e)) = pt e f * pt e g`.
- `pt_productMap_comp_comul`: in particular
  `pt e ((productMap f g).comp (comul e)) = pt e f * pt e g`.
- `pt_comp_counit`: `pt e (g.comp (counit e)) = 1` for every `g : R →ₐ[R] A`.
- `homEquiv_symm_mul`: the algebra map classifying `x * y` is
  `(productMap fₓ f_y).comp (comul e)`, where `fₓ`, `f_y` classify `x`, `y`.
- `homEquiv_symm_one`: the algebra map classifying `1 : F.obj A` is
  `(Algebra.ofId R A).comp (counit e)`.
- `homEquiv_symm_map`: the algebra map classifying `F.map g x` is
  `g.hom.comp fₓ`.

### Coalgebra axioms

Each axiom is an equality of algebra maps out of `B`. By `pt_injective` it
suffices to compare the classified points. Each proof expresses both sides with
`pt_comp_comul` and `pt_comp_counit` and then uses a group law.

- `comul_coassoc`: the algebra-map form of coassociativity,
  `assoc ∘ (comul ⊗ id) ∘ comul = (id ⊗ comul) ∘ comul` as maps
  `B → B ⊗ (B ⊗ B)`. Both sides classify a product of the three points given by
  the three inclusions of `B` into `B ⊗[R] (B ⊗[R] B)`. They agree by
  `mul_assoc`.
- `comul_rTensor_counit`: `(counit ⊗ id) ∘ comul = (Algebra.TensorProduct.lid R B).symm`,
  by `one_mul`.
- `comul_lTensor_counit`: `(id ⊗ counit) ∘ comul = (Algebra.TensorProduct.rid R R B).symm`,
  by `mul_one`.

`bialgebra e : Bialgebra R B` is Mathlib's `Bialgebra.ofAlgHom` applied to these
maps and proofs. In particular `(bialgebra e).toCoalgebra` is a coalgebra on `B`
whose comultiplication and counit are the linear maps underlying `comul e` and
`counit e`. Group inverses are not used, and no antipode is constructed.

## Matrix homomorphisms into the general linear group

Fix `M : Matrix (Fin N) (Fin N) B` with

- `hcomul : ∀ i j, comul e (M i j) = ∑ l, M i l ⊗ₜ[R] M l j`;
- `hcounit : ∀ i j, counit e (M i j) = (1 : Matrix (Fin N) (Fin N) R) i j`.

The following declarations use these assumptions.

- `matrixHom e M hcomul hcounit A : F.obj A →* Matrix (Fin N) (Fin N) A` sends `x` to
  `M.map fₓ`, the entries of `M` evaluated at the algebra map `fₓ` classifying `x`.
  It is multiplicative by `homEquiv_symm_mul` and `hcomul`. It sends `1` to `1` by
  `homEquiv_symm_one` and `hcounit`. `matrixHom_apply` unfolds it.
- `toGL e M hcomul hcounit : F ⟶ GeneralLinear.functor (Fin N) R` has components
  `(matrixHom …).toHomUnits`. A monoid homomorphism out of a group lands in the
  units. Naturality follows from `homEquiv_symm_map`.
- `toGLHom e M hcomul hcounit :
  Corepresented.groupScheme F e ⟶ GeneralLinear.groupScheme (Fin N) R` is the Library's
  `Corepresented.groupSchemeMap` applied to `toGL` and the corepresentation
  `GeneralLinear.corepresentableBy (Fin N) R`.

### `isClosedSubgroup_toGLHom`

If `Algebra.adjoin R (Set.range fun p : Fin N × Fin N => M p.1 p.2) = ⊤`, then
`IsClosedSubgroup (toGLHom e M hcomul hcounit)`, i.e. the underlying morphism of
schemes is a closed immersion.

Proof. By `Corepresented.groupSchemeMap_hom` and
`GeneralLinear.corepresentableBy_homEquiv_symm`, the underlying morphism is,
definitionally, `Spec.map` of `GeneralLinear.classify g`. Here `g` is the
invertible matrix that `toGL` assigns to the universal point
`e.homEquiv (𝟙 B)`. Its entries are `g i j = M i j`. By `GeneralLinear.classify_entry`,
each `M i j` lies in the range of `classify g`. So the subalgebra generated by the
entries, which is all of `B`, lies in that range, and `classify g` is surjective.
Mathlib's `IsClosedImmersion.spec_of_surjective` concludes.

## Relation to the literature

J. S. Milne, *Algebraic Groups* (2017), §4.d, printed p. 87, proof of Theorem 4.9:
a finite-dimensional subcomodule `V` of `O(G)` with basis `(eᵢ)` and
`Δ(e_j) = ∑ᵢ eᵢ ⊗ a_{ij}` gives a representation `G → GL_V`. The image of
`O(GL_V) → O(G)` contains the `a_{ij}`. If `V` contains algebra generators, this
map is surjective and `G → GL_V` is a closed immersion. Here the bialgebra
structure is derived directly from the corepresented group functor. The
representation is the natural transformation `toGL` on algebra points. The
closed immersion comes from surjectivity of the classifying algebra map, as in
Milne.
