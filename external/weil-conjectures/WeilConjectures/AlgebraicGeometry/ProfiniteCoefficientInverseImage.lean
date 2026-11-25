/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
import Mathlib.CategoryTheory.Sites.PreservesLimits
import WeilConjectures.AlgebraicGeometry.ProEtaleFiniteConstantRepresentable
import WeilConjectures.AlgebraicGeometry.ProfiniteLocallyConstantAdjunction
import WeilConjectures.AlgebraicGeometry.ProfiniteTestObjectFunctor
import WeilConjectures.CategoryTheory.SheafPullbackForgetComparison
import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheaf

/-!
# Inverse image of profinite coefficient rings

Source: Stacks Project, Tags 098T (2), 097N, 04D3 and 01YW
(auxiliary; not a blueprint node).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

/-- Naturality of the constant-section adjunct. Source: Stacks, Tags 098T (2) and 04D3
(auxiliary; not a blueprint node).
Proof: the presheaf constant-section maps commute with every ring homomorphism.
Sheafification and the inverse-image adjunction preserve this equality by naturality.
This is the finite-level naturality used in the node's final proof step. -/
theorem proEtaleConstantInverseImageMap_naturality {X Y : Scheme.{u}} (f : X ⟶ Y)
    {A B : CommRingCat.{u + 1}} (a : A ⟶ B) :
    (proEtaleSheafInverseImage f CommRingCat.{u + 1}).map
        ((constantSheaf (ProEt.topology Y) CommRingCat.{u + 1}).map a) ≫
      proEtaleConstantInverseImageMap f CommRingCat.{u + 1} B =
    proEtaleConstantInverseImageMap f CommRingCat.{u + 1} A ≫
      (constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).map a := by
  let L := proEtaleSheafInverseImage f CommRingCat.{u + 1}
  let adj := proEtaleSheafAdjunction f CommRingCat.{u + 1}
  change L.map _ ≫ (adj.homEquiv _ _).symm _ =
    (adj.homEquiv _ _).symm _ ≫ _
  rw [← adj.homEquiv_naturality_left_symm, ← adj.homEquiv_naturality_right_symm]
  congr 1
  apply ((sheafificationAdjunction (ProEt.topology Y) CommRingCat.{u + 1}).homEquiv
    ((Functor.const Y.ProEtᵒᵖ).obj A) _).injective
  change ((sheafificationAdjunction (ProEt.topology Y) CommRingCat.{u + 1}).homEquiv _ _)
    ((presheafToSheaf (ProEt.topology Y) CommRingCat.{u + 1}).map
      ((Functor.const Y.ProEtᵒᵖ).map a) ≫ _) = _
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right]
  simp only [proEtaleConstantDirectImageMap, Equiv.apply_symm_apply]
  apply NatTrans.ext
  funext U
  exact congrArg (fun t ↦ t.app ((proEtaleBaseChange f).op.obj U))
    ((toSheafification (ProEt.topology X) CommRingCat.{u + 1}).naturality
      ((Functor.const X.ProEtᵒᵖ).map a))

/-- The canonical comparison on constant coefficient rings, as a natural transformation.
Source: Stacks, Tags 098T (2) and 04D3
(auxiliary; not a blueprint node). -/
noncomputable def proEtaleConstantComparison {X Y : Scheme.{u}} (f : X ⟶ Y) :
    constantSheaf (ProEt.topology Y) CommRingCat.{u + 1} ⋙
        proEtaleSheafInverseImage f CommRingCat.{u + 1} ⟶
      constantSheaf (ProEt.topology X) CommRingCat.{u + 1} where
  app A := proEtaleConstantInverseImageMap f CommRingCat.{u + 1} A
  naturality _ _ a := proEtaleConstantInverseImageMap_naturality f a

/-- The identity comparison of inverse images, obtained as the mate of base change by
an identity. Source: Stacks, Tags 098T (2) and 04D3
(auxiliary; not a blueprint node). -/
noncomputable def proEtaleRingInverseImageId (X : Scheme.{u}) :
    proEtaleSheafInverseImage (𝟙 X) CommRingCat.{u + 1} ≅ 𝟭 _ :=
  (conjugateIsoEquiv Adjunction.id
    (proEtaleSheafAdjunction (𝟙 X) CommRingCat.{u + 1})).symm
      (Functor.sheafPushforwardContinuousId'
        (MorphismProperty.Over.pullbackId @WeaklyEtale ⊤ X) CommRingCat.{u + 1}
          (ProEt.topology X)).symm

/-- The composite comparison of inverse images is the mate of pullback pasting.
Source: Stacks, Tags 098T (2) and 04D3
(auxiliary; not a blueprint node). -/
noncomputable def proEtaleRingInverseImageComp {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    proEtaleSheafInverseImage (f ≫ g) CommRingCat.{u + 1} ≅
      proEtaleSheafInverseImage g CommRingCat.{u + 1} ⋙
        proEtaleSheafInverseImage f CommRingCat.{u + 1} :=
  ((conjugateIsoEquiv (proEtaleSheafAdjunction (f ≫ g) CommRingCat.{u + 1})
    ((proEtaleSheafAdjunction g CommRingCat.{u + 1}).comp
      (proEtaleSheafAdjunction f CommRingCat.{u + 1}))).symm
        (Functor.sheafPushforwardContinuousComp'
          (eFG := (MorphismProperty.Over.pullbackComp
            (P := @WeaklyEtale) (Q := ⊤) f g).symm) CommRingCat.{u + 1}
          (ProEt.topology Z) (ProEt.topology Y) (ProEt.topology X)).symm).symm

end AlgebraicGeometry.Scheme
