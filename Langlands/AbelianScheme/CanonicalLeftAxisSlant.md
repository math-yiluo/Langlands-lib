# The left-axis slant formula for an abelian variety

This module specializes
[AllSeqLeftAxisSlant](../AlgebraicGeometry/Modules/CechResolution/AllSeqLeftAxisSlant.md) to an
abelian scheme `A` over `Spec K`, `K` a field, in the namespace
`Langlands.AbelianScheme.CanonicalCreationContraction`. All cohomology is actual
structure-sheaf cohomology `structureCohomology X n = (relativeCohomology X.hom n).obj 𝒪_X`. The
section algebras are the local instance `sectionsAlgebra` (from `secHom`) of
[CanonicalCreationContraction](CanonicalCreationContraction.md).

## Definitions

- `leftAxis A : A.X ⟶ A.X ⨯ A.X` is the morphism `prod.lift (toUnit A.X ≫ η[A.X]) (𝟙 A.X)`,
  i.e. `a ↦ (0, a)`, where `η[A.X]` is the unit of the group object.
  - `leftAxis_left_fst`: `(leftAxis A).left ≫ prod.fst.left = A.X.hom ≫ η[A.X].left`.
  - `leftAxis_left_snd`: `(leftAxis A).left ≫ prod.snd.left = 𝟙`.
- `creationProd A n` is the actual creation map `H¹(A ⨯ A) → Hⁿ(A ⨯ A) → Hⁿ⁺¹(A ⨯ A)`. It is
  `AllSeq.creationCanonical` on the simple product cover `mixedCover A` of the fixed finite
  affine cover of `A`. This is the same cover on which `slant A ell n` is defined.

## Theorem

`slant_creationProd_pull_fst`: for every actual dual `ell : H¹(A) →ₗ[K] K`, every
`x ∈ H¹(A)`, every `n` and every `e ∈ Hⁿ⁺¹(A ⨯ A)`:

`slant A ell (n + 1) (creationProd A (n + 1) (p₁^* x) e) = ell x • (leftAxis A)^* e`.

Here `p₁^* = pullStructure A prod.fst 1`, and `(leftAxis A)^* = AllSeq.unitCohomologyPullbackLinear`
along `leftAxis A`. Both are actual cohomology pullbacks followed by the unit comparison.

The proof applies `AllSeq.slantByH1Dual_creation_pull_left` with:

- the product `A.X ⨯ A.X` (`isPullback_prod A`) and the fixed cover (`cover A`, `cover_top A`,
  `cover_affine A`, `mixedCover_top A`, `mixedCover_affine A`);
- the rational point `η[A.X]` and the axis `leftAxis A`;
- surjectivity of `secHom A.X.hom ⊤`, which is the Library lemma `surjective_secHom_top` for the
  smooth, proper, geometrically connected structure morphism.

The statement covers every input degree `n + 1 ≥ 1`. It does not treat input degree `0`. It
does not claim the creation–contraction relations, generation of cohomology by `H¹`, or the
exterior/coproduct comparison.

## Provenance

The module is derived and internal. It introduces no external theorem. It instantiates the
general formula with the abelian scheme's unit point, product projections and chosen affine
cover. Its import closure contains none of the six excluded Picard or dual-scheme statements
named by Task 6105. Through `DegreeTwoComparisonAssembly` it contains the statement modules
`FieldH2PrimitiveInjectivityStatement` and `FieldH2ExteriorCoproductComparisonStatement`, but
no proof of either.
