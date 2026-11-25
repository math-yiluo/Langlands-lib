/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.ConstructibleProEtaleComparisonData
import WeilConjectures.AlgebraicGeometry.ConstructibleComparisonModuleExact
import WeilConjectures.CategoryTheory.ConstantRingModuleSheaves
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import Mathlib.CategoryTheory.Sites.DenseSubsite.InducedTopology
import Mathlib.CategoryTheory.Sites.Adjunction
import Mathlib.Algebra.Category.Ring.Adjunctions
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-! # Ordinary realization of coefficient-sized constant module sheaves

Source: Stacks Project, Tags 03CY and 09AL; coefficient transport in the opening
paragraph of the finite comparison proof
(auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

section ConstantScalars
variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
  (A : Type u) [CommRing A]

private instance commRingForgetSheafification :
    J.PreservesSheafification (forget₂ CommRingCat.{u} RingCat.{u}) where
  le := by
    intro P Q f hf
    let : Presheaf.IsLocallyInjective J f := hf.isLocallyInjective
    let : Presheaf.IsLocallySurjective J f := hf.isLocallySurjective
    let : Presheaf.IsLocallyInjective J (Functor.whiskerRight f
        (forget₂ CommRingCat.{u} RingCat.{u})) :=
      ⟨fun x y h ↦ Presheaf.equalizerSieve_mem J f x y h⟩
    let : Presheaf.IsLocallySurjective J (Functor.whiskerRight f
        (forget₂ CommRingCat.{u} RingCat.{u})) :=
      ⟨fun x ↦ Presheaf.imageSieve_mem J f x⟩
    exact J.W_of_isLocallyBijective (Functor.whiskerRight f
      (forget₂ CommRingCat.{u} RingCat.{u}))

private def coefficientRingIso : SheafOfModules.constantCoefficientRing J A ≅
    (constantSheaf J RingCat.{u}).obj (RingCat.of A) :=
  (constantCommuteCompose J (forget₂ CommRingCat.{u} RingCat.{u})).app (CommRingCat.of A)

private def ringRestriction : ConstantCompletion.Mod (ConstantCompletion.constant J A) ⥤
    SheafOfModules.{u} ((constantSheaf J RingCat.{u}).obj (RingCat.of A)) :=
  SheafOfModules.restrictScalars (coefficientRingIso J A).inv

private theorem ringRestriction_equivalence : (ringRestriction J A).IsEquivalence := by
  let eC : C ≌ C := Equivalence.refl
  let : eC.functor.IsContinuous J J := inferInstanceAs (Functor.IsContinuous (𝟭 C) J J)
  let : eC.inverse.IsContinuous J J := inferInstanceAs (Functor.IsContinuous (𝟭 C) J J)
  let c := (coefficientRingIso J A).symm
  let e := SheafOfModules.pushforwardPushforwardEquivalence.{u}
    (J := J) (K := J) eC c.hom c.inv
    (by
      ext U x
      dsimp [eC, Equivalence.refl]
      simp only [Functor.map_id]
      exact congrArg (fun f ↦ f.hom.app U x) c.inv_hom_id.symm)
    (by
      ext U x
      dsimp [eC, Equivalence.refl]
      simp only [Functor.map_id]
      exact congrArg (fun f ↦ f.hom.app U x) c.hom_inv_id)
  exact e.isEquivalence_functor

private theorem coefficientRingIso_unit :
    SheafOfModules.constantCoefficientUnit J A ≫ (coefficientRingIso J A).hom.hom =
      toSheafify J ((Functor.const Cᵒᵖ).obj (RingCat.of A)) := by
  change SheafOfModules.constantCoefficientUnit J A ≫
    ((constantCommuteCompose J (forget₂ CommRingCat.{u} RingCat.{u})).hom.app
      (CommRingCat.of A)).hom = _
  rw [constantCommuteCompose_hom_app_hom]
  unfold SheafOfModules.constantCoefficientUnit
  rw [← Category.assoc, sheafComposeIso_inv_fac]
  exact (toSheafify_naturality J
    (Functor.constComp Cᵒᵖ (CommRingCat.of A)
      (forget₂ CommRingCat.{u} RingCat.{u})).hom).symm.trans
      (by rfl)

private theorem restriction_smul (M : ConstantCompletion.Mod (ConstantCompletion.constant J A))
    (V : Cᵒᵖ) (a : A) (x : M.val.obj V) :
    a • (show ((ringRestriction J A ⋙ constantRingModuleRestriction J A).obj M).obj.obj V
      from x) =
    a • (show ((coefficientModelFixedScalars J A).obj M).obj.obj V from x) := by
  have h := congrArg (fun f ↦ f.app V a) (coefficientRingIso_unit J A)
  have hi := congrArg (fun f ↦ f.hom.app V) (coefficientRingIso J A).hom_inv_id
  change (coefficientRingIso J A).inv.hom.app V
    ((toSheafify J ((Functor.const Cᵒᵖ).obj (RingCat.of A))).app V a) • x =
      (SheafOfModules.constantCoefficientUnit J A).app V a • x
  erw [← h]
  exact congrArg (fun b ↦ b • x) (ConcreteCategory.congr_hom hi _)

private def restrictionIso :
    ringRestriction J A ⋙ constantRingModuleRestriction J A ≅ coefficientModelFixedScalars J A := by
  refine NatIso.ofComponents (fun M ↦ ObjectProperty.isoMk _
    (NatIso.ofComponents (fun V ↦ ?_) ?_)) ?_
  · exact ModuleCat.isoMk (Iso.refl _) (fun a ↦ by
      ext x
      exact (restriction_smul J A M V a x).symm)
  · intro V W f
    ext x
    rfl
  · intro M N f
    ext V x
    rfl

/-- Restricting a module over the sheafified constant ring to constant scalars is an
exact equivalence. Source: Stacks Tag 03CY
(auxiliary; not a blueprint node).

Proof: the constant commutative ring, with commutativity forgotten, is canonically
isomorphic to the constant ring sheaf. Restriction along this isomorphism followed
by the constant-ring module equivalence is the specified constant-scalar functor:
the equality of its scalar actions follows from the sheafification unit equation.
The natural comparison has identity underlying additive maps. -/
theorem coefficientModelFixedScalars_isEquivalence :
    (coefficientModelFixedScalars J A).IsEquivalence := by
  let : (ringRestriction J A).IsEquivalence := ringRestriction_equivalence J A
  obtain ⟨⟨e, he, _⟩, _⟩ := constant_ring_module_sheaves J A
  have : (constantRingModuleRestriction J A).IsEquivalence := by
    rw [← he]
    infer_instance
  exact Functor.isEquivalence_of_iso (restrictionIso J A)

end ConstantScalars
end CategoryTheory

namespace AlgebraicGeometry.ProEtale

variable (X : Scheme.{u}) (A : Type (u + 1)) [CommRing A]

/-- Evaluate the etale coefficient model on the original etale site, retaining the
constant scalar action. Source: Stacks Tags 03CY and 09AL
(auxiliary; not a blueprint node). -/
def finiteComparisonEtaleModelRealization :
    ConstantCompletion.Mod (ConstantCompletion.constant
      (Scheme.smallModelComparisonEtaleTopology.{u, u + 1} X) A) ⥤
        Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A) :=
  let : (AsSmall.down : AsSmall.{u + 1} X.Etale ⥤ X.Etale).IsEquivalence :=
    (AsSmall.equiv.{u, u + 1, u + 1} (C := X.Etale)).isEquivalence_inverse
  let : (AsSmall.equiv.{u, u + 1, u + 1} (C := X.Etale)).inverse.IsDenseSubsite
      (Scheme.smallModelComparisonEtaleTopology.{u, u + 1} X) X.smallEtaleTopology :=
    inferInstanceAs ((AsSmall.down : Scheme.smallModelComparisonEtaleSite.{u, u + 1} X ⥤
      X.Etale).IsDenseSubsite
        ((AsSmall.down : Scheme.smallModelComparisonEtaleSite.{u, u + 1} X ⥤
          X.Etale).inducedTopology
          X.smallEtaleTopology) X.smallEtaleTopology)
  coefficientModelFixedScalars _ A ⋙
    (Equivalence.sheafCongr X.smallEtaleTopology
      (Scheme.smallModelComparisonEtaleTopology.{u, u + 1} X)
      (AsSmall.equiv.{u, u + 1, u + 1} (C := X.Etale)) (ModuleCat.{u + 1} A)).inverse

/-- Evaluate the pro-etale coefficient model on the original pro-etale site, retaining
the constant scalar action. Source: Stacks Tags 03CY and 09AL
(auxiliary; not a blueprint node). -/
def finiteComparisonProEtaleModelRealization :
    ConstantCompletion.Mod (ConstantCompletion.constant
      (Scheme.coefficientProEtaleModelTopology.{u, u + 1} X) A) ⥤
        Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A) :=
  let : (AsSmall.down : AsSmall.{u + 1} X.ProEt ⥤ X.ProEt).IsEquivalence :=
    (AsSmall.equiv.{u, u + 1, u + 1} (C := X.ProEt)).isEquivalence_inverse
  let : (AsSmall.equiv.{u, u + 1, u + 1} (C := X.ProEt)).inverse.IsDenseSubsite
      (Scheme.coefficientProEtaleModelTopology.{u, u + 1} X) (Scheme.ProEt.topology X) :=
    inferInstanceAs ((AsSmall.down : Scheme.coefficientProEtaleSiteModel.{u, u + 1} X ⥤
      X.ProEt).IsDenseSubsite
        ((AsSmall.down : Scheme.coefficientProEtaleSiteModel.{u, u + 1} X ⥤ X.ProEt).inducedTopology
          (Scheme.ProEt.topology X)) (Scheme.ProEt.topology X))
  coefficientModelFixedScalars _ A ⋙
    (Equivalence.sheafCongr (Scheme.ProEt.topology X)
      (Scheme.coefficientProEtaleModelTopology.{u, u + 1} X)
      (AsSmall.equiv.{u, u + 1, u + 1} (C := X.ProEt)) (ModuleCat.{u + 1} A)).inverse

/-- The etale model realization is an equivalence. Source: Stacks Tag 03CY
(auxiliary; not a blueprint node). -/
instance finiteComparisonEtaleModelRealization_isEquivalence :
    (finiteComparisonEtaleModelRealization X A).IsEquivalence := by
  let := coefficientModelFixedScalars_isEquivalence
    (Scheme.smallModelComparisonEtaleTopology.{u, u + 1} X) A
  unfold finiteComparisonEtaleModelRealization
  infer_instance

/-- The pro-etale model realization is an equivalence. Source: Stacks Tag 03CY
(auxiliary; not a blueprint node). -/
instance finiteComparisonProEtaleModelRealization_isEquivalence :
    (finiteComparisonProEtaleModelRealization X A).IsEquivalence := by
  let := coefficientModelFixedScalars_isEquivalence
    (Scheme.coefficientProEtaleModelTopology.{u, u + 1} X) A
  unfold finiteComparisonProEtaleModelRealization
  infer_instance

/-- The etale model realization preserves addition. Source: Stacks Tag 03CY
(auxiliary; not a blueprint node). -/
instance finiteComparisonEtaleModelRealization_additive :
    (finiteComparisonEtaleModelRealization X A).Additive :=
  Functor.additive_of_preserves_binary_products _

/-- The pro-etale model realization preserves addition. Source: Stacks Tag 03CY
(auxiliary; not a blueprint node). -/
instance finiteComparisonProEtaleModelRealization_additive :
    (finiteComparisonProEtaleModelRealization X A).Additive :=
  Functor.additive_of_preserves_binary_products _

private theorem modelComparisonRingMap_unit :
    SheafOfModules.constantCoefficientUnit
        (Scheme.smallModelComparisonEtaleTopology.{u, u + 1} X) A ≫
      (constructibleComparisonRingMap.{u, u + 1} X A).hom =
    Functor.whiskerLeft (Scheme.smallModelComparisonInclusion.{u, u + 1} X).op
      (SheafOfModules.constantCoefficientUnit
        (Scheme.coefficientProEtaleModelTopology.{u, u + 1} X) A) := by
  let J := Scheme.smallModelComparisonEtaleTopology.{u, u + 1} X
  let K := Scheme.coefficientProEtaleModelTopology.{u, u + 1} X
  let F := Scheme.smallModelComparisonInclusion.{u, u + 1} X
  let φ := Functor.whiskerLeft F.op
    (toSheafify K ((Functor.const _).obj (CommRingCat.of A)))
  have h := ((sheafificationAdjunction J CommRingCat.{u + 1}).homEquiv
    ((Functor.const _).obj (CommRingCat.of A))
    ((F.sheafPushforwardContinuous CommRingCat.{u + 1} J K).obj
      (ConstantCompletion.constant K A))).apply_symm_apply φ
  exact congrArg (fun f ↦ Functor.whiskerRight f
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})) h

private def modelPushforwardSquare :
    SheafOfModules.pushforward (constructibleComparisonRingMap.{u, u + 1} X A) ⋙
        finiteComparisonEtaleModelRealization X A ≅
      finiteComparisonProEtaleModelRealization X A ⋙
        comparisonLowerStar (ModuleCat.{u + 1} A) X := by
  refine NatIso.ofComponents (fun M ↦ ObjectProperty.isoMk _
    (NatIso.ofComponents (fun V ↦ ?_) ?_)) ?_
  · refine ModuleCat.isoMk (Iso.refl _) (fun a ↦ ?_)
    ext x
    have h := congrArg (fun f ↦ f.app (Opposite.op (AsSmall.up.obj V.unop)) a)
      (modelComparisonRingMap_unit X A)
    change a • (show ((finiteComparisonProEtaleModelRealization X A).obj M).obj.obj
        ((Scheme.toProEt X).op.obj V) from x) =
      a • (show ((finiteComparisonEtaleModelRealization X A).obj
        ((SheafOfModules.pushforward (constructibleComparisonRingMap.{u, u + 1} X A)).obj
          M)).obj.obj V from x)
    exact congrArg (fun b ↦ b • (show M.val.obj
      ((Scheme.smallModelComparisonInclusion.{u, u + 1} X).op.obj
        (Opposite.op (AsSmall.up.obj V.unop))) from x)) h.symm
  · intro U V f
    ext x
    rfl
  · intro M N f
    ext V x
    rfl

/-- The specified coefficient-model realization intertwines comparison inverse image.
Source: the constant-section equation, Stacks Tags 03CY and 09AL
(auxiliary; not a blueprint node).

Proof: on direct images, both paths have the same sections. The constant-section
unit equation identifies their scalar actions. Compose the model pullback adjunction
with the realization equivalences and use uniqueness of left adjoints. -/
theorem finiteComparisonModelPullbackSquare :
    Nonempty (constructibleComparisonPullback.{u, u + 1} X A ⋙
        finiteComparisonProEtaleModelRealization X A ≅
      finiteComparisonEtaleModelRealization X A ⋙
        comparisonUpperStar (ModuleCat.{u + 1} A) X) := by
  let E := (finiteComparisonEtaleModelRealization X A).asEquivalence
  let G := (finiteComparisonProEtaleModelRealization X A).asEquivalence
  let adjM := SheafOfModules.pullbackPushforwardAdjunction
    (constructibleComparisonRingMap.{u, u + 1} X A)
  let adjO := comparisonAdjunction (ModuleCat.{u + 1} A) X
  let a := adjM.comp G.toAdjunction
  let b := E.toAdjunction.comp adjO
  let R := SheafOfModules.pushforward (constructibleComparisonRingMap.{u, u + 1} X A)
  let S := comparisonLowerStar (ModuleCat.{u + 1} A) X
  let h : (G.inverse ⋙ R) ⋙ E.functor ≅ S :=
    Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft G.inverse (modelPushforwardSquare X A) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight G.counitIso S ≪≫ Functor.leftUnitor S
  let h' : (S ⋙ E.inverse) ⋙ E.functor ≅ S :=
    Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft S E.counitIso ≪≫
      Functor.rightUnitor S
  let r := ((Functor.FullyFaithful.ofFullyFaithful E.functor).whiskeringRight _)
    |>.preimageIso (h ≪≫ h'.symm)
  exact ⟨((conjugateIsoEquiv a b).symm r).symm⟩

end AlgebraicGeometry.ProEtale
