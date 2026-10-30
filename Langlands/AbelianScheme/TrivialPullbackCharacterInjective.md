# Injectivity of the normalized character from descent of isomorphisms

Author: Worker 934. This module proves
`Langlands.AbelianScheme.TrivialPullbackCharacterInjectiveStatement`
as `Langlands.AbelianScheme.trivialPullbackCharacterInjective`. It first derives
the statement from `Langlands.Scheme.Modules.UnitCocycleDescentUniquenessStatement`,
using the factorization lemmas of `KernelPairFactorization`. It then applies this
to the published proof `Langlands.Scheme.Modules.unitCocycleDescentUniqueness`.

## From characters to kernel-translation scalars

`kernelTranslationScalar_eq_of_character_eq`. Let `α` and `β` be trivializations of
the `f_T`-pullbacks of two modules on `T ×_S B` with equal intrinsic characters.
Then for every `W : Over T.left` and every kernel point `k` over
`(Over.map T.hom).obj W`, the published `kernelTranslationScalar`s of `α` and `β`
at `(kernelCharacterParameter W, k)` agree.

The proof applies `characterHomEquiv` to get equal homomorphisms
`intrinsicKernelCharacterHom`. It evaluates both at the base-changed point
`(baseChangePointsEquiv …).symm k`, using `intrinsicKernelCharacterHom_points`,
which gives equal descended units `kernelTranslationUnit`. It finally applies
`relativeUnitsPullback_kernelTranslationUnit` to return to scalars.

`equalCompositeScalar_eq_of_character_eq`. With the same hypothesis, the comparison
scalars `structureAutScalar (equalCompositeUnitAut f_T a b h _)` of `α` and `β`
agree on every pair `a b : U ⟶ T ×_S A` with `a ≫ f_T = b ≫ f_T`. By
`structureAutScalar_equalCompositeUnitAut_eq`, both are pullbacks along
`pairSection a` of kernel-translation scalars at the same parameter and kernel
point, and those agree by the previous lemma.

## The injectivity theorem

`trivialPullbackCharacterInjective_of_uniqueness (hU)` proves
`TrivialPullbackCharacterInjectiveStatement` for every base `S`, every isogeny
`f` and every `T`, from the uniqueness statement `hU`.

The proof goes through the following steps:

1. Two classes are represented by actual line bundles `L` and `K` with chosen
   trivializations `α` and `β` of their `f_T`-pullbacks. These exist by
   `HasTrivialHomPullback`.
2. The published `trivialHomPullbackCharacter_eq` identifies the class
   characters with `intrinsicKernelCharacter f α` and
   `intrinsicKernelCharacter f β`, so these two are equal.
3. `f_T` is affine, flat and surjective by `isFinite_homFamilySpaceMap`,
   `flat_homFamilySpaceMap` and `surjective_homFamilySpaceMap`.
4. The comparison scalars agree on all pairs by
   `equalCompositeScalar_eq_of_character_eq`, so `hU` gives an isomorphism
   `L ≅ K` of line bundles.
5. `ObjectProperty.isoMk` and `Quotient.sound` turn this isomorphism into
   equality of classes.

`trivialPullbackCharacterInjective` is the unconditional theorem. It applies
`trivialPullbackCharacterInjective_of_uniqueness` to the published theorem
`unitCocycleDescentUniqueness`
(module `Langlands.AlgebraicGeometry.Modules.UnitCocycleDescentUniquenessProof`).
That theorem proves the uniqueness half of descent for line bundles along affine
flat surjections (Stacks Project, Descent, Proposition 5.2, tag 023T).
