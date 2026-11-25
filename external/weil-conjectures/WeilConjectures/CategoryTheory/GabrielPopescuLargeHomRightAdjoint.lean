/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.Algebra.Category.ModuleCat.Ulift
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
import Mathlib.CategoryTheory.Preadditive.Yoneda.Limits
import WeilConjectures.CategoryTheory.DerivedLargeCoproductsTransfer
import WeilConjectures.CategoryTheory.LargeHomSolutionSet

/-! Adjoint existence for the universe-enlarged Hom functor. -/

@[expose] public section

universe w uA vA vH

open CategoryTheory.Limits

namespace CategoryTheory

/-- The fixed Hom functor of any object, with its values lifted to the larger
module universe, has a left adjoint when the derived category has coproducts
of the required size. No separator, full faithfulness or exactness is asserted.

Source: Stacks Project, Lemma 19.14.1 (Tag 0F5S), second proof, the
large-coproduct extension step of node new-stage3-gabriel-popescu-abelian-core.

(auxiliary; not a blueprint node)

Proof in words: first construct coproducts of the displayed size in A. For a
family X_i, take the coproduct K of X_i[0] in the derived category and put
P = H^0(K). For an injective I concentrated in degree zero, maps K -> I[0]
are naturally Hom_A(H^0(K), I), because I[0] is K-injective. The derived
coproduct property identifies this with the product of Hom_A(X_i, I).
For arbitrary Y choose an exact sequence 0 -> Y -> I^0 -> I^1 with both
I^j injective. Left exactness of Hom_A(P,-) and of the product of Hom_A(X_i,-)
identifies their kernels, so the same natural identification holds for Y.
Thus P, with the maps induced by the coproduct injections, is the coproduct.
Transfer these coproducts along the ShrinkHoms equivalence.

Write S = End(G)^op in ShrinkHoms A. For a large S-module M use the canonical
free presentation: the free module on its underlying set surjects onto M,
and the free module on the underlying set of its kernel maps into it.
Replace a free module on a set J by the coproduct of J copies of G. A matrix
with finite-support columns induces the corresponding morphism between these
coproducts using the S-action by precomposition. Take its cokernel. Mapping
this cokernel to X is exactly the kernel of the two Hom maps, hence naturally
Hom_S(M, Hom(G,X)). Lifting Hom(G,X) does not change this identification.
The natural representing property defines the action on module morphisms
uniquely and gives a left adjoint. Compose with the inverse ShrinkHoms
equivalence to obtain the asserted right-adjoint property in A. This argument
uses only coproducts and cokernels; it does not require G to be a separator.
-/
theorem gabriel_popescu_large_hom_isRightAdjoint
    {A : Type uA} [Category.{vA} A] [Abelian A]
    [IsGrothendieckAbelian.{w} A] [HasDerivedCategory.{w} A]
    [HasCoproducts.{max w vA vH} (DerivedCategory A)]
    (G : ShrinkHoms A) :
    ((ShrinkHoms.equivalence.{w} A).functor ⋙ preadditiveCoyonedaObj G ⋙
      ModuleCat.uliftFunctor.{vH, w} (End G)ᵐᵒᵖ).IsRightAdjoint := by
  have : HasCoproducts.{max w vA vH} A :=
    derived_large_coproducts_transfer.{w, uA, vA, vH}
  have : HasCoproducts.{max w vH} A := hasCoproducts_shrink.{max w vH, vA}
  have : HasCoproducts.{max w vH} (ShrinkHoms A) := fun _ =>
    Adjunction.hasColimitsOfShape_of_equivalence (ShrinkHoms.equivalence.{w} A).inverse
  rw [Functor.isRightAdjoint_comp_iff_right]
  apply isRightAdjoint_of_preservesLimits_of_solutionSetCondition
  exact large_hom_solutionSetCondition G

end CategoryTheory
