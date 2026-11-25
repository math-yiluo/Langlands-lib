/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
public import WeilConjectures.CategoryTheory.RingedSiteModules
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.AlgebraicGeometry.ProEtale.AffineClosedInverseImageLeftAdjoint
import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImageLimitsZariskiLocal
import WeilConjectures.AlgebraicGeometry.ProEtaleModuleInverseImageComparison
import all WeilConjectures.AlgebraicGeometry.ProEtaleOperations
import WeilConjectures.CategoryTheory.SheavesAlgebraicStructuresAbelian
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification

/-!
# Limits under inverse image along a pro-etale immersion

Source: Stacks Project, Tag 09AA (1), with open slice restriction, and Modules on Sites,
Tags 03D2, 03DB and 04JC
(auxiliary; not a blueprint node).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

private theorem abelianUnderlying {X Y : Scheme.{u}} (f : Y ⟶ X)
    [PreservesFiniteLimits (proEtaleSheafInverseImage f (Type (u + 1)))] :
    Nonempty (proEtaleSheafInverseImage f AddCommGrpCat.{u + 1} ⋙
        sheafCompose (ProEt.topology Y) (CategoryTheory.forget AddCommGrpCat.{u + 1}) ≅
      sheafCompose (ProEt.topology X) (CategoryTheory.forget AddCommGrpCat.{u + 1}) ⋙
        proEtaleSheafInverseImage f (Type (u + 1))) := by
  let J := ProEt.topology X
  let K := ProEt.topology Y
  let U := proEtaleBaseChange f
  open Functor.sheafPullbackConstruction in
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.defeqAttrib.useBackward true in
  exact (by
    let : BraidedCategory (Sheaf J (Type (u + 1))) :=
      BraidedCategory.ofCartesianMonoidalCategory
    let : BraidedCategory (Sheaf K (Type (u + 1))) :=
      BraidedCategory.ofCartesianMonoidalCategory
    let R := U.sheafPushforwardContinuous (Type (u + 1)) J K
    let : R.Braided := Functor.Braided.ofChosenFiniteProducts R
    let Rab := U.sheafPushforwardContinuous AddCommGrpCat.{u + 1} J K
    obtain ⟨FJ, GJ, hFJ, hGJ, hFJGJ, hGJFJ, opJ, _⟩ :=
      sheavesAlgebraicStructuresAbelian.{u + 1, u, u + 1} J
    obtain ⟨FK, GK, hFK, hGK, hFKGK, hGKFK, opK, _⟩ :=
      sheavesAlgebraicStructuresAbelian.{u + 1, u, u + 1} K
    let EJ := CategoryTheory.Equivalence.mk FJ GJ (eqToIso hFJGJ.symm) (eqToIso hGJFJ)
    let EK := CategoryTheory.Equivalence.mk FK GK (eqToIso hFKGK.symm) (eqToIso hGKFK)
    let e : (FK ⋙ R.mapCommGrp) ⋙ CommGrp.forget _ ≅
        (Rab ⋙ FJ) ⋙ CommGrp.forget _ :=
      (Functor.associator FK (CommGrp.forget _) R).symm ≪≫
        Functor.isoWhiskerRight (eqToIso hFK) R ≪≫
        Iso.refl _ ≪≫
        Functor.isoWhiskerLeft Rab (eqToIso hFJ).symm
    have hprod (X Y : Sheaf K (Type (u + 1))) :
        (CartesianMonoidalCategory.prodComparisonIso R X Y).inv = 𝟙 _ := by
      have h : (CartesianMonoidalCategory.prodComparisonIso R X Y).hom = 𝟙 _ := by
        rfl
      change (CartesianMonoidalCategory.prodComparisonIso R X Y).inv =
        𝟙 (R.obj (MonoidalCategory.tensorObj X Y))
      simpa only [h, Category.id_comp] using
      (CartesianMonoidalCategory.prodComparisonIso R X Y).hom_inv_id
    have hone : (CartesianMonoidalCategory.preservesTerminalIso R).inv = 𝟙 _ := by
      rfl
    have he (A : Sheaf K AddCommGrpCat.{u + 1}) :
        (e.app A).hom ≫ (eqToIso hFJ).hom.app (Rab.obj A) =
          R.map ((eqToIso hFK).hom.app A) := by
      simp [e]
    let egroup : FK ⋙ R.mapCommGrp ≅ Rab ⋙ FJ :=
      NatIso.ofComponents (fun A ↦ CommGrp.mkIso (e.app A) (by
        apply (cancel_mono ((eqToIso hFJ).hom.app (Rab.obj A))).1
        change (Functor.LaxMonoidal.ε R ≫ R.map MonObj.one) ≫
          (e.app A).hom ≫ (eqToIso hFJ).hom.app (Rab.obj A) = _
        rw [Functor.Monoidal.ε_of_cartesianMonoidalCategory, hone, Category.id_comp, he]
        apply Sheaf.hom_ext
        ext X t
        exact (opK A (U.op.obj X)).2.1 t |>.trans
          ((opJ (Rab.obj A) X).2.1 t).symm) (by
        apply (cancel_mono ((eqToIso hFJ).hom.app (Rab.obj A))).1
        change (Functor.LaxMonoidal.μ R _ _ ≫ R.map MonObj.mul) ≫
          (e.app A).hom ≫ (eqToIso hFJ).hom.app (Rab.obj A) = _
        rw [Functor.Monoidal.μ_of_cartesianMonoidalCategory, hprod, Category.id_comp, he]
        apply Sheaf.hom_ext
        ext X ab
        rcases ab with ⟨a, b⟩
        change ((eqToIso hFK).hom.app A).hom.app (U.op.obj X)
          ((MonObj.mul (X := (FK.obj A).X)).hom.app (U.op.obj X) (a, b)) = _
        rw [(opK A (U.op.obj X)).1 a b]
        change _ = ((eqToIso hFJ).hom.app (Rab.obj A)).hom.app X
          ((MonObj.mul (X := (FJ.obj (Rab.obj A)).X)).hom.app X
            (((e.app A).hom.hom.app X) a, ((e.app A).hom.hom.app X) b))
        rw [(opJ (Rab.obj A) X).1]
        have hea (x : (R.obj (FK.obj A).X).obj.obj X) :
            ((eqToIso hFJ).hom.app (Rab.obj A)).hom.app X
                (((e.app A).hom.hom.app X) x) =
              ((eqToIso hFK).hom.app A).hom.app (U.op.obj X) x :=
          congrArg (fun f ↦ f.hom.app X x) (he A)
        rw [hea a, hea b])) (by
        intro A B f
        apply CommGrp.hom_ext
        exact e.hom.naturality f)
    let eR := Functor.isoWhiskerRight egroup GJ ≪≫
      Functor.associator Rab FJ GJ ≪≫
      Functor.isoWhiskerLeft Rab (eqToIso hFJGJ) ≪≫ Rab.rightUnitor
    -- Lift and transport the adjunction using Mathlib's canonical commutative-group lift.
    let L := sheafPullback U (Type (u + 1)) J K
    let : L.Braided := Functor.Braided.ofChosenFiniteProducts L
    let adj := sheafAdjunctionContinuous U (Type (u + 1)) J K
    let lifted := (EJ.toAdjunction.comp adj.mapCommGrp).comp EK.symm.toAdjunction
    let transported := lifted.ofNatIsoRight eR
    let comparison :=
      (sheafAdjunctionContinuous U AddCommGrpCat.{u + 1} J K).leftAdjointUniq transported
    refine ⟨Functor.isoWhiskerRight comparison _ ≪≫ ?_⟩
    exact Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (eqToIso hGK) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (Iso.refl _) _ ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerRight (eqToIso hFJ) L)

private theorem comp_setLimits {X Y Z : Scheme.{u}} (f : Z ⟶ Y) (g : Y ⟶ X)
    [PreservesLimitsOfSize.{u + 1, u + 1} (proEtaleSheafInverseImage f (Type (u + 1)))]
    [PreservesLimitsOfSize.{u + 1, u + 1} (proEtaleSheafInverseImage g (Type (u + 1)))] :
    PreservesLimitsOfSize.{u + 1, u + 1} (proEtaleSheafInverseImage (f ≫ g) (Type (u + 1))) := by
  let a := (proEtaleSheafAdjunction g (Type (u + 1))).comp
    (proEtaleSheafAdjunction f (Type (u + 1)))
  let e := Functor.sheafPushforwardContinuousComp'
    (MorphismProperty.Over.pullbackComp (P := @WeaklyEtale) (Q := ⊤) f g).symm
    (Type (u + 1)) (ProEt.topology X) (ProEt.topology Y) (ProEt.topology Z)
  let b := a.ofNatIsoRight e
  let q := (proEtaleSheafAdjunction (f ≫ g) (Type (u + 1))).leftAdjointUniq b
  exact preservesLimits_of_natIso q.symm

private theorem closed_setLimits {X Y : Scheme.{u}} (f : Y ⟶ X)
    [IsClosedImmersion f] :
    PreservesLimitsOfSize.{u + 1, u + 1} (proEtaleSheafInverseImage f (Type (u + 1))) := by
  apply proEtale_inverseImage_limits_zariski_local f
  intro U
  let : IsAffine U.1.toScheme := U.2
  let : IsAffine (f ⁻¹ᵁ U.1).toScheme := U.2.preimage f
  obtain ⟨L, ⟨adj⟩⟩ := exists_affineClosedInverseImageLeftAdjoint (f ∣_ U.1)
  exact adj.rightAdjoint_preservesLimits

private theorem immersion_setLimits {X Y : Scheme.{u}} (f : Y ⟶ X)
    [IsImmersion f] :
    PreservesLimitsOfSize.{u + 1, u + 1} (proEtaleSheafInverseImage f (Type (u + 1))) := by
  have := closed_setLimits f.liftCoborder
  have := restriction_preservesLimits f.coborderRange.ι
  simpa only [Scheme.Hom.liftCoborder_ι] using comp_setLimits f.liftCoborder f.coborderRange.ι

private theorem forgetAbelian_preservesLimits (X : Scheme.{u}) :
    PreservesLimitsOfSize.{u + 1, u + 1}
      (sheafCompose (ProEt.topology X) (CategoryTheory.forget AddCommGrpCat.{u + 1})) := by
  let : PreservesLimitsOfSize.{u + 1, u + 1}
      (sheafCompose (ProEt.topology X) (CategoryTheory.forget AddCommGrpCat.{u + 1}) ⋙
        sheafToPresheaf _ _) :=
    show PreservesLimitsOfSize.{u + 1, u + 1}
      (sheafToPresheaf _ _ ⋙ (Functor.whiskeringRight _ _ _).obj
        (CategoryTheory.forget AddCommGrpCat.{u + 1})) by infer_instance
  exact preservesLimits_of_reflects_of_preserves _ (sheafToPresheaf _ _)

private theorem immersion_abelianLimits {X Y : Scheme.{u}} (f : Y ⟶ X)
    [IsImmersion f] :
    PreservesLimitsOfSize.{u + 1, u + 1} (proEtaleSheafInverseImage f AddCommGrpCat.{u + 1}) := by
  let := immersion_setLimits f
  let := forgetAbelian_preservesLimits X
  let := forgetAbelian_preservesLimits Y
  let V := sheafCompose (ProEt.topology Y) (CategoryTheory.forget AddCommGrpCat.{u + 1})
  let : ReflectsLimitsOfSize.{u + 1, u + 1} V := reflectsLimits_of_reflectsIsomorphisms
  obtain ⟨e⟩ := abelianUnderlying f
  let : PreservesLimitsOfSize.{u + 1, u + 1}
      (proEtaleSheafInverseImage f AddCommGrpCat.{u + 1} ⋙ V) :=
    preservesLimits_of_natIso e.symm
  exact preservesLimits_of_reflects_of_preserves _ V

private theorem forgetModule_preservesLimits {X : Scheme.{u}}
    (R : Sheaf (ProEt.topology X) RingCat.{u + 1}) :
    PreservesLimitsOfSize.{u + 1, u + 1} (SheafOfModules.toSheaf.{u + 1} R) := by
  let : PreservesLimitsOfSize.{u + 1, u + 1}
      (SheafOfModules.toSheaf.{u + 1} R ⋙ sheafToPresheaf _ _) :=
    show PreservesLimitsOfSize.{u + 1, u + 1}
      (SheafOfModules.forget R ⋙ PresheafOfModules.toPresheaf R.obj) by infer_instance
  exact preservesLimits_of_reflects_of_preserves _ (sheafToPresheaf _ _)

section ScalarExtension

variable {X Y : Scheme.{u}} (f : X ⟶ Y)
  (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
  (S : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
  (c : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R ≅ S)

private theorem proEtaleRingExtension_preservesLimits :
    PreservesLimitsOfSize.{u + 1, u + 1} (proEtaleRingExtension f R S c) := by
  let rc := (sheafCompose (ProEt.topology X)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).mapIso c
  let e := proEtaleScalarEquivalence X rc
  let T := SheafOfModules.restrictScalars rc.hom
  let : T.IsEquivalence := inferInstanceAs e.functor.IsEquivalence
  let adj := proEtaleRingExtensionAdjunction f R S c
  let ei := adj.leftAdjointUniq e.symm.toAdjunction
  exact preservesLimits_of_natIso ei.symm

end ScalarExtension

/-- Inverse image along a locally closed immersion preserves all small limits, also on
abelian and module sheaves. The module underlying-sheaf comparison is natural; the graph
condition on arbitrary test sheaves expresses transport of the scalar action under the
finite-product comparison. The final functor is characterized on both objects and maps
by the specified sheaf tensor extension, so it is not an arbitrary exact functor.

Source: Stacks Project, Tag 09AA (1), and Modules on Sites, Tags 03D2, 03DB and 04JC
(auxiliary; not a blueprint node).

Proof:
1. For a weakly etale map, composition on pro-etale site objects is left adjoint
   to base change. Its sheaf restriction preserves limits sectionwise. Uniqueness
   of left adjoints identifies restriction with the specified inverse image.
   Compose adjunctions to obtain the inverse-image composition comparison.
2. For an affine closed immersion, the extra left adjoint supplied by
   lem-weil-pbc-affine-closed-inverse-image-left-adjoint makes inverse image a right
   adjoint, hence limit preserving. Apply the Zariski-local preservation theorem
   to affine opens to handle any closed immersion. Factor a locally closed immersion
   into its closed lift to the coborder followed by the open inclusion, and compose.
3. Identify abelian sheaves with commutative-group objects in set sheaves. Direct image
   commutes with this identification: the product and terminal comparisons of restriction
   are identities, and the operation equations verify preservation of zero and addition.
   Lift the set adjunction to groups and use uniqueness of left adjoints. This gives the
   underlying-set comparison, so the limit-preserving, conservative forgetful functor
   transfers all-limit preservation from sets to abelian sheaves.
4. Use proEtale_moduleInverseImage_comparison for the natural abelian comparison and
   the scalar graph assertion. Forgetting modules to abelian sheaves preserves limits
   and finite colimits and reflects them. Transfer preservation through the comparison;
   abelian inverse image preserves colimits by its adjunction. Its additivity transfers
   through the comparison and the faithful additive forgetful functor.
5. Take the specified proEtaleRingModulePullback, whose objects and maps are the given
   sheafified tensor extension. Its additive and finite exactness instances are available.
   The existing operations module proves the tensor/restriction adjunction, which
   identifies extension of scalars as left adjoint to restriction. Restriction along a ring
   isomorphism is an
   equivalence, with inverse restriction along its inverse. Uniqueness of left adjoints
   identifies extension with the inverse equivalence, so it preserves all limits.
   Compose with pure module inverse image. -/
theorem proEtale_immersion_inverseImage_preservesLimits
    {X Y : Scheme.{u}} (f : Y ⟶ X) [IsImmersion f] :
    PreservesLimitsOfSize.{u + 1, u + 1} (proEtaleSheafInverseImage f (Type (u + 1))) ∧
    PreservesLimitsOfSize.{u + 1, u + 1} (proEtaleSheafInverseImage f AddCommGrpCat.{u + 1}) ∧
    ∀ R : Sheaf (ProEt.topology X) CommRingCat.{u + 1},
      ∃ (_ : (proEtaleModuleInverseImage f R).Additive),
        PreservesFiniteLimits (proEtaleModuleInverseImage f R) ∧
        PreservesFiniteColimits (proEtaleModuleInverseImage f R) ∧
        PreservesLimitsOfSize.{u + 1, u + 1} (proEtaleModuleInverseImage f R) ∧
        Nonempty (proEtaleModuleInverseImage f R ⋙ SheafOfModules.toSheaf _ ≅
          SheafOfModules.toSheaf _ ⋙ proEtaleSheafInverseImage f AddCommGrpCat.{u + 1}) ∧
        (∃ (eR : (proEtaleSheafInverseImage f (Type (u + 1))).obj
            ((sheafCompose (ProEt.topology X) (CategoryTheory.forget CommRingCat.{u + 1})).obj R) ≅
            (sheafCompose (ProEt.topology Y) (CategoryTheory.forget CommRingCat.{u + 1})).obj
              ((proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R))
          (eM : proEtaleModuleInverseImage f R ⋙ SheafOfModules.toSheaf _ ⋙
              sheafCompose (ProEt.topology Y) (CategoryTheory.forget AddCommGrpCat.{u + 1}) ≅
            (SheafOfModules.toSheaf _ ⋙
              sheafCompose (ProEt.topology X) (CategoryTheory.forget AddCommGrpCat.{u + 1})) ⋙
                proEtaleSheafInverseImage f (Type (u + 1))),
          ∀ (M : SheafOfModules.{u + 1} ((sheafCompose (ProEt.topology X)
              (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R))
            (T : Sheaf (ProEt.topology X) (Type (u + 1)))
            (a : T ⟶ (sheafCompose (ProEt.topology X)
              (CategoryTheory.forget CommRingCat.{u + 1})).obj R)
            (b t : T ⟶ (SheafOfModules.toSheaf _ ⋙
              sheafCompose (ProEt.topology X) (CategoryTheory.forget AddCommGrpCat.{u + 1})).obj M),
            (∀ (U : X.ProEtᵒᵖ) (x : T.obj.obj U),
              @id (M.val.obj U) (t.hom.app U x) =
                @id (R.obj.obj U) (a.hom.app U x) •
                  @id (M.val.obj U) (b.hom.app U x)) →
            ∀ (V : Y.ProEtᵒᵖ)
              (x : ((proEtaleSheafInverseImage f (Type (u + 1))).obj T).obj.obj V),
              @id (((proEtaleModuleInverseImage f R).obj M).val.obj V)
                ((eM.inv.app M).hom.app V
                  (((proEtaleSheafInverseImage f (Type (u + 1))).map t).hom.app V x)) =
                @id (((proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R).obj.obj V)
                  (eR.hom.hom.app V
                    (((proEtaleSheafInverseImage f (Type (u + 1))).map a).hom.app V x)) •
                @id (((proEtaleModuleInverseImage f R).obj M).val.obj V)
                  ((eM.inv.app M).hom.app V
                    (((proEtaleSheafInverseImage f (Type (u + 1))).map b).hom.app V x))) ∧
        ∀ (S : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
          (c : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R ≅ S),
          ∃ (P : SheafOfModules.{u + 1} ((sheafCompose (ProEt.topology X)
                (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R) ⥤
              SheafOfModules.{u + 1} ((sheafCompose (ProEt.topology Y)
                (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S))
            (hobj : ∀ M, P.obj M = SheafOfModules.changeOfRings.{u, u + 1, u + 1}
              c.hom ((proEtaleModuleInverseImage f R).obj M)),
            (∀ (M N : SheafOfModules.{u + 1} ((sheafCompose (ProEt.topology X)
                  (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)) (a : M ⟶ N),
              P.map a = eqToHom (hobj M) ≫
                SheafOfModules.changeOfRingsHom.{u, u + 1, u + 1} c.hom
                  ((proEtaleModuleInverseImage f R).obj M)
                    ((proEtaleModuleInverseImage f R).map a) ≫ eqToHom (hobj N).symm) ∧
            ∃ (_ : P.Additive), PreservesFiniteLimits P ∧ PreservesFiniteColimits P ∧
              PreservesLimitsOfSize.{u + 1, u + 1} P := by
  let hs := immersion_setLimits f
  let ha := immersion_abelianLimits f
  refine ⟨hs, ha, ?_⟩
  intro R
  obtain ⟨⟨eA⟩, haction⟩ := proEtale_moduleInverseImage_comparison f R
  let A := (sheafCompose (ProEt.topology X)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R
  let B := (sheafCompose (ProEt.topology Y)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
      ((proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R)
  let L := proEtaleModuleInverseImage f R
  let V := SheafOfModules.toSheaf.{u + 1} B
  let := forgetModule_preservesLimits A
  let := forgetModule_preservesLimits B
  let : ReflectsLimitsOfSize.{u + 1, u + 1} V := reflectsLimits_of_reflectsIsomorphisms
  let : PreservesLimitsOfSize.{u + 1, u + 1} (L ⋙ V) :=
    preservesLimits_of_natIso eA.symm
  let hL : PreservesLimitsOfSize.{u + 1, u + 1} L :=
    preservesLimits_of_reflects_of_preserves L V
  let : PreservesFiniteColimits (proEtaleSheafInverseImage f AddCommGrpCat.{u + 1}) := by
    let : PreservesColimitsOfSize.{0, 0}
        (proEtaleSheafInverseImage f AddCommGrpCat.{u + 1}) :=
      (proEtaleSheafAdjunction f AddCommGrpCat.{u + 1}).leftAdjoint_preservesColimits
    infer_instance
  let : PreservesFiniteColimits (L ⋙ V) := preservesFiniteColimits_of_natIso eA.symm
  let : ReflectsFiniteColimits V := inferInstance
  let : PreservesFiniteColimits L := preservesFiniteColimits_of_reflects_of_preserves L V
  let : (proEtaleSheafInverseImage f AddCommGrpCat.{u + 1}).Additive :=
    (proEtaleSheafAdjunction f AddCommGrpCat.{u + 1}).left_adjoint_additive
  let : (L ⋙ V).Additive := Functor.additive_of_iso eA.symm
  let : L.Additive := Functor.additive_of_comp_faithful L V
  refine ⟨inferInstance, inferInstance, inferInstance, hL, ⟨eA⟩, haction, ?_⟩
  intro S c
  let P := proEtaleRingModulePullback f R S c
  refine ⟨P, (fun _ ↦ rfl), ?_, inferInstance, inferInstance, inferInstance, ?_⟩
  · intro M N a
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    rfl
  · let := proEtaleRingExtension_preservesLimits f R S c
    change PreservesLimitsOfSize.{u + 1, u + 1}
      (proEtaleModuleInverseImage f R ⋙ proEtaleRingExtension f R S c)
    infer_instance

end AlgebraicGeometry.Scheme
