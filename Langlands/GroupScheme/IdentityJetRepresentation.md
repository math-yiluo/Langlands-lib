# The conjugation representation on a finite free identity jet

This internal module constructs the representation `ρ_n` of SGA 3, Exposé XVI,
Proposition 3.1 for a separated group whose order-`n` identity jet is
finite free. It is a step toward
`JetConjugationRepresentationStatement`. The construction works
in the general setting described below.

## Setting

Let `R` be a commutative ring, `G` a group scheme over `Spec R` with separated
structure morphism, and `n` a natural number. Suppose the jet
`IdentityJet.scheme G n` is identified with `Spec P` for an `R`-algebra `P` by
an isomorphism `e` compatible with the maps to `Spec R` (hypothesis `he`).
Later `P` is assumed free with a basis `b` indexed by `Fin m`. Test schemes
`specOver A` are spectra of `R`-algebras (Library module
`Langlands.AlgebraicGeometry.AffinePointGluing`).

## Jet points over affine schemes

- `GeneralLinear.pointOfMatrix` is the point of `GL_m` over `specOver A` with
  a given invertible matrix. It inverts the Library's `GeneralLinear.matrixOf`.
  The lemmas record that it is injective, multiplicative, preserves `1`, and
  is natural in `A`.
- `jetPoint χ` is the jet point over `specOver B` classified by an `R`-algebra
  map `χ : P → B`. Its underlying map is `Spec χ ≫ e.inv ≫ inclusion`.
  `isJetPoint_jetPoint`, `specMapOver_comp_jetPoint` (naturality in `B`) and
  `jetPoint_injective` (from monicity of the jet inclusion and full
  faithfulness of `Spec`) hold.
- `exists_jetPoint`: every jet point over `specOver B` is a `jetPoint χ`. The
  factorization through the jet, composed with `e.hom`, is `Spec` of a ring
  map. It is an `R`-algebra map by `he`. `jetAlgHom` chooses `χ`.

## The conjugation automorphism

Let `g` be a point of `G` over `specOver A`.

- `conjBeta g : P →ₐ[R] A ⊗[R] P` classifies the conjugate of the universal
  jet point (classified by `includeRight`) by the restriction of `g` along
  `includeLeft`. The conjugate is a jet point by `IsJetPoint.conj` of
  `Langlands.GroupScheme.IdentityJetConjugation`.
- `conj_jetPoint` (key lemma): for any `R`-algebra map
  `ψ : A ⊗[R] P → B`, conjugating `jetPoint (ψ ∘ includeRight)` by the
  restriction of `g` along `ψ ∘ includeLeft` gives
  `jetPoint (ψ ∘ conjBeta g)`. The proof uses naturality of jet points and
  the fact that restriction of points is multiplicative.
- `conjAlg g` is the `A`-algebra endomorphism of `A ⊗[R] P` extending
  `conjBeta g`. The key lemma gives `conjBeta_one`, `conjBeta_mul`,
  `conjAlg_one`, `conjAlg_mul` (`conjAlg (g * h) = conjAlg h ∘ conjAlg g`) and
  the naturality `conjBeta_specMapOver` along `A → A'`.
- `centralizesJet_iff_conjBeta`: `g` centralizes the jet
  (`IdentityJet.CentralizesJet`) exactly when `conjBeta g = includeRight`. For
  the converse, a jet point on a refinement is checked on affine points
  (`over_hom_ext`). There it is some `jetPoint χ`, and the refinement is
  `Spec` of some `φ` (`exists_specMapOver`). The key lemma applies with
  `ψ = lift φ χ`.

## Matrices and the representation

- `conjMatrix g` is the matrix of `conjAlg g⁻¹` in the basis
  `Algebra.TensorProduct.basis A b`. The inverse turns the anti-homomorphism
  `conjAlg` into a homomorphism: `conjMatrix_mul`, `conjMatrix_one`.
  `conjMatrix_eq_one_iff` says the matrix is `1` exactly when `g` centralizes
  the jet. `conjMatrix_specMapOver` gives naturality in `A`, via
  `basis_repr_map`.
- `conjGL g` is the corresponding invertible matrix.
  `exists_conjugationMorphism` glues the points `pointOfMatrix (conjGL g)` to
  a morphism `G.X ⟶ GL_m.X` over `Spec R` (Library `exists_over_hom`).
- `exists_jetRepresentation`: if `P` has a basis `b` indexed by `Fin m`,
  there is `ρ : MatrixRepresentation G (Fin m)` such that for every test
  scheme `U` and every point `g`, `g ≫ ρ.hom.hom = 1` exactly when
  `CentralizesJet G n g`. The morphism is multiplicative on all test schemes,
  because this can be checked on affine points. The Library's `homOfPoints`
  then makes it a group-scheme homomorphism. The kernel statement for
  arbitrary `U` reduces to affine points by `over_hom_ext` and
  `centralizesJet_of_affine`.

This module adds no geometric input beyond the Library's identity jets,
affine point gluing and general linear group scheme.

## The jet conjugation representation from locally free jets

`jetConjugationRepresentation_of` proves `JetConjugationRepresentationStatement`
from `IdentityJetLocallyFreeStatement`, taken as a hypothesis. The
hypothesis gives an open immersion `i : Spec R ⟶ S` with image containing
`s` and contained in `W`. It also gives an `R`-algebra `P`, an isomorphism
`e` over `Spec R` from the order-`n` jet of `G_i` to `Spec P`, and a basis
`b` of `P` indexed by `Fin m`. The base change `G_i` is separated, since its
structure morphism is a pullback of `G.X.hom`. `exists_jetRepresentation`
applied to `G_i`, `e` and `b` gives the required representation. Its base
`Spec (CommRingCat.of R)` is definitionally `Spec R`.
