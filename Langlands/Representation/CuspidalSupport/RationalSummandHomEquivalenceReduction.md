# Renard VI.4.1: the Theorem follows from the Proposition

Worker 1637. Source: David Renard, *Représentations des groupes réductifs p-adiques*, French version dated 9 July 2026, registered as `renard-2026-representations-groupes-reductifs-padiques`, SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`. Locators: VI.4.1, the Proposition and the Theorem with its proof, printed pp.149–151 / PDF pp.155–157; A.VIII.2, printed pp.266–267 / PDF pp.272–273. These pages were read for this unit.

## What the module proves

This module deduces the Theorem of VI.4.1 from its Proposition. It does not prove either of them unconditionally.

- `rationalSummandBlock_abelian`: the actual inertia block `RationalInertiaBlock G π` has an abelian structure whose additive structure is the full-subcategory one, `Preadditive.fullSubcategory`.
- `projective_of_isRationalInertiaSmallProgenerator`: the lifting condition of `IsRationalInertiaSmallProgenerator` (every block map `P ⟶ Z` lifts through every block epimorphism `Y ⟶ Z`) is Mathlib's `Projective P` in the block.
- `homSmallProgenerator_of_isRationalInertiaSmallProgenerator`: if `IsRationalInertiaSmallProgenerator G π X` holds, then X lies in the block, the block has coproducts indexed by `Type (max uF uV)`, and the block object P = ⟨X, hmem⟩ satisfies Renard's `Langlands.Renard.HomSmallProgenerator.{max uF uV}` (A.VIII.2) for the inherited abelian structure.
- `isEquivalence_preadditiveCoyonedaObj_of_isRationalInertiaSmallProgenerator`: under the same hypothesis, X lies in the block and `preadditiveCoyonedaObj P`, from the block to `ModuleCat (End P)ᵐᵒᵖ`, is an equivalence. Here G is any affine group scheme locally of finite type over a nonarchimedean local field, π is any smooth representation and X is any smooth representation at carrier universe `max uF uV`.
- `rationalSummandHomEquivalence_of_smallProgenerator`: `RationalSummandSmallProgeneratorStatement.{uF, uV}` implies `RationalSummandHomEquivalenceStatement.{uF, uV}`. The two statements have the same quantifiers, premises and universes, so no premise is added.

## Proof

Unpacking `IsRationalInertiaSmallProgenerator G π X` gives membership `hmem`, the lifting condition, faithfulness of `preadditiveCoyonedaInt P`, coproducts `HasColimitsOfShape (Discrete I)` for every `I : Type (max uF uV)`, and preservation of these coproducts by `preadditiveCoyonedaInt P`. The coproduct clause is literally `HasCoproducts.{max uF uV}` of the block.

The lifting condition is the `factors` field of Mathlib's `Projective`. The published `Langlands.Renard.homProjectiveComparison` turns `Projective P` into Renard's `HomProjective P`, the exactness of the integer Hom functor, in any abelian category. Faithfulness is `HomGenerator P` by definition, and coproduct preservation is `HomPreservesCoproducts.{max uF uV} P` by definition. Together they form `HomSmallProgenerator.{max uF uV} P`. The published `Langlands.Renard.preadditiveCoyonedaObj_isEquivalence_of_homSmallProgenerator` (the proof of A.VIII.2) then gives the equivalence.

The block's Hom groups live in `Type (max uF uV)`, which is also the coproduct index universe, as A.VIII.2 requires.

The statement-level theorem introduces the binders of `RationalSummandHomEquivalenceStatement`, restores the instances that the statement provides by `haveI` (affineness from `hG.isAffineHom` and local finite type from `hG.smooth`), applies the Proposition to the same data and then applies the objectwise result. The compact induction in the Theorem is literally `rationalNormKernelSummandInduction G ρ`.

## Abelian structure and the import constraint

The abelian structure is Mathlib's abelian structure on a full subcategory closed under kernels, cokernels and finite products. The block's Serre-class and finite-product closure instances are those of the published `rationalInertiaBlockProperty_isSerreClass` and `rationalInertiaBlockProperty_isClosedUnderFiniteProducts`. Both come from `SmoothRep.irreducibleSubquotientsProperty_isSerreClass` and `SmoothRep.irreducibleSubquotientsProperty_isClosedUnderFiniteProducts`, which are restated here as local instances. The module `RationalInertiaPresentations` that contains the published instances cannot be imported together with `RationalSummandSmallProgeneratorStatement`: both declare an unnamed local topology instance whose generated name is `Langlands.CuspidalSupport.instTopologicalSpaceRationalPoints_2`, so a joint import fails with a duplicate-declaration error. `rationalSummandBlock_abelian` records, by `rfl`, that the resulting abelian structure has the full-subcategory additive structure. So `preadditiveCoyonedaObj` in the target, which uses that additive structure, is the functor to which A.VIII.2 applies.

## Provenance

This is an internal derived unit. Renard proves the Theorem from the Proposition through the functors F_Π and G_Π and presentations by direct sums of V_Π and of R (printed pp.150–151). The implemented route instead applies the published proof of A.VIII.2, which shows directly that the Hom functor of a small progenerator in an abelian category with coproducts is faithful, full and essentially surjective. The quasi-inverse M ↦ M ⊗_R V_Π is not identified, and the target does not ask for it.
