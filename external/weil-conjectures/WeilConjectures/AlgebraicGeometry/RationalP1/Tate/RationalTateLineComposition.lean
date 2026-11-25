/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.RationalP1.Tate.RationalTatePullback
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.UnitCoherence
import WeilConjectures.CategoryTheory.Adjunction.UnitProjection
import all WeilConjectures.AlgebraicGeometry.Cartesian.CartesianCoefficientTwistsSupplement
import all WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleRootsOfUnityInverseImageSupplement

/-! Composition of the normalized unshifted rational Tate-line comparisons. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.RationalP1
open DiagonalCoefficients
open CategoryTheory.MonoidalCategory Opposite

attribute [local irreducible] coefficient lineComparison CondensedRing.upperStar
  CondensedRing.upperStarComp

private theorem ab_adjunct_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    {LZ : Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}}
    {LY : Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}}
    {LX : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}}
    (a : (upperStar Ab.{u + 1} g).obj LZ ⟶ LY)
    (b : (upperStar Ab.{u + 1} f).obj LY ⟶ LX) :
    (upperStarLowerStarAdjunction Ab.{u + 1} (f ≫ g)).homEquiv _ _
        ((upperStarComp Ab.{u + 1} f g).hom.app LZ ≫
          (upperStar Ab.{u + 1} f).map a ≫ b) =
      (upperStarLowerStarAdjunction Ab.{u + 1} g).homEquiv _ _ a ≫
        (lowerStar Ab.{u + 1} g).map
          ((upperStarLowerStarAdjunction Ab.{u + 1} f).homEquiv _ _ b) ≫
        (lowerStarComp Ab.{u + 1} f g).hom.app LX := by
  have h := homEquiv_comp_conjugateEquiv_app
    ((upperStarLowerStarAdjunction Ab.{u + 1} g).comp
      (upperStarLowerStarAdjunction Ab.{u + 1} f))
    (upperStarLowerStarAdjunction Ab.{u + 1} (f ≫ g))
    (upperStarComp Ab.{u + 1} f g).hom ((upperStar Ab.{u + 1} f).map a ≫ b)
  rw [conjugateEquiv_upperStarComp_hom] at h
  rw [← h, Adjunction.comp_homEquiv]
  dsimp only [Equiv.trans]
  change (upperStarLowerStarAdjunction Ab.{u + 1} g).homEquiv _ _
    ((upperStarLowerStarAdjunction Ab.{u + 1} f).homEquiv _ _
      ((upperStar Ab.{u + 1} f).map a ≫ b)) ≫ _ = _
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right]
  exact Category.assoc _ _ _

private theorem linePull_adjunct
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}} (f : X ⟶ Y)
    (LY : Modules Λ Y) (LX : Modules Λ X)
    (a : (upperStar Ab.{u + 1} f).obj LY.X ⟶ LX.X)
    (h : SpInternalCartesian f Λ LY LX a) :
    (((CondensedRing.upperStarLowerStarAdjunction Λ f).homEquiv LY LX)
        (linePullIso Λ f LY LX a h).hom).hom =
      ((upperStarLowerStarAdjunction Ab.{u + 1} f).homEquiv LY.X LX.X) a := by
  exact eq_of_heq (linePull_existsUnique Λ f LY LX a h).exists.choose_spec

private theorem module_comparison_comp
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z)
    (LZ : Modules Λ Z) (LY : Modules Λ Y) (LX : Modules Λ X)
    (a : (upperStar Ab.{u + 1} g).obj LZ.X ⟶ LY.X)
    (b : (upperStar Ab.{u + 1} f).obj LY.X ⟶ LX.X)
    (c : (upperStar Ab.{u + 1} (f ≫ g)).obj LZ.X ⟶ LX.X)
    (ea : (CondensedRing.upperStar Λ g).obj LZ ⟶ LY)
    (eb : (CondensedRing.upperStar Λ f).obj LY ⟶ LX)
    (ec : (CondensedRing.upperStar Λ (f ≫ g)).obj LZ ⟶ LX)
    (ha : ((CondensedRing.upperStarLowerStarAdjunction Λ g).homEquiv LZ LY ea).hom =
      (upperStarLowerStarAdjunction Ab.{u + 1} g).homEquiv LZ.X LY.X a)
    (hb : ((CondensedRing.upperStarLowerStarAdjunction Λ f).homEquiv LY LX eb).hom =
      (upperStarLowerStarAdjunction Ab.{u + 1} f).homEquiv LY.X LX.X b)
    (hc : ((CondensedRing.upperStarLowerStarAdjunction Λ (f ≫ g)).homEquiv LZ LX ec).hom =
      (upperStarLowerStarAdjunction Ab.{u + 1} (f ≫ g)).homEquiv LZ.X LX.X c)
    (hcomp : (upperStarComp Ab.{u + 1} f g).hom.app LZ.X ≫
      (upperStar Ab.{u + 1} f).map a ≫ b = c) :
    (CondensedRing.upperStarComp Λ f g).hom.app LZ ≫
      (CondensedRing.upperStar Λ f).map ea ≫ eb = ec := by
  apply ((CondensedRing.upperStarLowerStarAdjunction Λ (f ≫ g)).homEquiv LZ LX).injective
  have h := homEquiv_comp_conjugateEquiv_app
    ((CondensedRing.upperStarLowerStarAdjunction Λ g).comp
      (CondensedRing.upperStarLowerStarAdjunction Λ f))
    (CondensedRing.upperStarLowerStarAdjunction Λ (f ≫ g))
    (CondensedRing.upperStarComp Λ f g).hom ((CondensedRing.upperStar Λ f).map ea ≫ eb)
  rw [← conjugateIsoEquiv_apply_hom, CondensedRing.conjugateIsoEquiv_upperStarComp] at h
  rw [← h, Adjunction.comp_homEquiv]
  change (CondensedRing.upperStarLowerStarAdjunction Λ g).homEquiv _ _
    ((CondensedRing.upperStarLowerStarAdjunction Λ f).homEquiv _ _
      ((CondensedRing.upperStar Λ f).map ea ≫ eb)) ≫ _ = _
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right]
  apply Mod.hom_ext
  simp only [Mod.comp_hom', CondensedRing.lowerStar_map_hom,
    CondensedRing.lowerStarComp_hom_app_hom, ha, hb, hc]
  exact (Category.assoc _ _ _).trans ((ab_adjunct_comp f g a b).symm.trans
    (congrArg ((upperStarLowerStarAdjunction Ab.{u + 1} (f ≫ g)).homEquiv LZ.X LX.X)
      hcomp))

private theorem coefficient_comp
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (upperStarComp Ab.{u + 1} f g).hom.app (condensedRingObj Λ Z) ≫
        (upperStar Ab.{u + 1} f).map (condensedPullbackHom Λ g) ≫
        condensedPullbackHom Λ f = condensedPullbackHom Λ (f ≫ g) := by
  apply ((upperStarLowerStarAdjunction Ab.{u + 1} (f ≫ g)).homEquiv _ _).injective
  rw [ab_adjunct_comp]
  exact (condensedPushforwardHom_comp Λ f g).symm

attribute [local irreducible] Scheme.proEtaleRootsOfUnitySheaf
  Scheme.proEtaleRootsOfUnitySections

private theorem roots_direct_spec {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ)
    (V : Y.ProEtᵒᵖ) (x : (Scheme.proEtaleRootsOfUnitySheaf Y n).obj.obj V) :
    Scheme.proEtaleRootsOfUnitySections X n ((Scheme.proEtaleBaseChange f).op.obj V)
      ((Scheme.proEtaleRootsOfUnityDirectImageMap f n).hom.app V x) =
    Additive.ofMul (restrictRootsOfUnity (pullback.fst V.unop.hom f).appTop.hom n
      (Additive.toMul (Scheme.proEtaleRootsOfUnitySections Y n V x))) :=
  (Scheme.existsUnique_proEtaleRootsOfUnityDirectImageMap f n).exists.choose_spec V x

private theorem roots_direct_comp {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (n : ℕ) :
    Scheme.proEtaleRootsOfUnityDirectImageMap g n ≫
      (lowerStar Ab.{u + 1} g).map (Scheme.proEtaleRootsOfUnityDirectImageMap f n) ≫
      (lowerStarComp Ab.{u + 1} f g).hom.app (Scheme.proEtaleRootsOfUnitySheaf X n) =
    Scheme.proEtaleRootsOfUnityDirectImageMap (f ≫ g) n := by
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext V
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro x
  apply (Scheme.proEtaleRootsOfUnitySections X n
    ((Scheme.proEtaleBaseChange (f ≫ g)).op.obj V)).injective
  change Scheme.proEtaleRootsOfUnitySections X n _
      (((lowerStarComp Ab.{u + 1} f g).hom.app _).hom.app V
        ((Scheme.proEtaleRootsOfUnityDirectImageMap f n).hom.app
          ((Scheme.proEtaleBaseChange g).op.obj V)
          ((Scheme.proEtaleRootsOfUnityDirectImageMap g n).hom.app V x))) = _
  rw [lowerStarComp_hom_app_hom_app]
  have hm := Scheme.sections_map X n
    (((MorphismProperty.Over.pullbackComp f g).hom.app V.unop).op)
    ((Scheme.proEtaleRootsOfUnityDirectImageMap f n).hom.app
      ((Scheme.proEtaleBaseChange g).op.obj V)
      ((Scheme.proEtaleRootsOfUnityDirectImageMap g n).hom.app V x))
  refine hm.trans ?_
  have hf := roots_direct_spec f n ((Scheme.proEtaleBaseChange g).op.obj V)
    ((Scheme.proEtaleRootsOfUnityDirectImageMap g n).hom.app V x)
  have hg := roots_direct_spec g n V x
  have hfg := roots_direct_spec (f ≫ g) n V x
  have hgf := hf.trans (congrArg (fun a ↦ Additive.ofMul (restrictRootsOfUnity
    (pullback.fst ((Scheme.proEtaleBaseChange g).obj V.unop).hom f).appTop.hom n
    (Additive.toMul a))) hg)
  have hall := congrArg (fun a ↦ Additive.ofMul (restrictRootsOfUnity
    (((MorphismProperty.Over.pullbackComp f g).hom.app V.unop).left.appTop.hom) n
    (Additive.toMul a))) hgf
  refine hall.trans (Eq.trans ?_ hfg.symm)
  apply Additive.toMul.injective
  apply Subtype.ext
  apply Units.ext
  have hp := MorphismProperty.Over.pullbackComp_left_fst_fst
    (P := @WeaklyEtale) (Q := ⊤) f g V.unop
  have he := congrArg (fun t ↦ t.appTop) hp
  simp only [Scheme.Hom.comp_appTop] at he
  exact congrArg (fun t ↦ t.hom
    (Additive.toMul (Scheme.proEtaleRootsOfUnitySections Z n V x)).val.val) he

private theorem roots_adjunct {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :
    (upperStarLowerStarAdjunction Ab.{u + 1} f).homEquiv _ _
      (Scheme.proEtaleRootsOfUnityInverseImageMap f n) =
    Scheme.proEtaleRootsOfUnityDirectImageMap f n := by
  change (Scheme.proEtaleSheafAdjunction f Ab.{u + 1}).homEquiv _ _
    (((Scheme.proEtaleSheafAdjunction f Ab.{u + 1}).homEquiv _ _).symm _) = _
  exact Equiv.apply_symm_apply _ _

private theorem roots_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (n : ℕ) :
    (upperStarComp Ab.{u + 1} f g).hom.app (Scheme.proEtaleRootsOfUnitySheaf Z n) ≫
        (upperStar Ab.{u + 1} f).map (Scheme.proEtaleRootsOfUnityInverseImageMap g n) ≫
        Scheme.proEtaleRootsOfUnityInverseImageMap f n =
      Scheme.proEtaleRootsOfUnityInverseImageMap (f ≫ g) n := by
  apply ((upperStarLowerStarAdjunction Ab.{u + 1} (f ≫ g)).homEquiv _ _).injective
  rw [ab_adjunct_comp, roots_adjunct, roots_adjunct, roots_adjunct]
  exact roots_direct_comp f g n

private theorem tensor_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (AZ BZ : Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
    (AY BY : Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
    (AX BX : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    (ag : (upperStar Ab.{u + 1} g).obj AZ ⟶ AY)
    (bg : (upperStar Ab.{u + 1} g).obj BZ ⟶ BY)
    (af : (upperStar Ab.{u + 1} f).obj AY ⟶ AX)
    (bf : (upperStar Ab.{u + 1} f).obj BY ⟶ BX) :
    (upperStarComp Ab.{u + 1} f g).hom.app (AZ ⊗ BZ) ≫
        (upperStar Ab.{u + 1} f).map
          (Functor.OplaxMonoidal.δ (upperStar Ab.{u + 1} g) AZ BZ ≫ (ag ⊗ₘ bg)) ≫
        Functor.OplaxMonoidal.δ (upperStar Ab.{u + 1} f) AY BY ≫ (af ⊗ₘ bf) =
      Functor.OplaxMonoidal.δ (upperStar Ab.{u + 1} (f ≫ g)) AZ BZ ≫
        (((upperStarComp Ab.{u + 1} f g).hom.app AZ ≫
          (upperStar Ab.{u + 1} f).map ag ≫ af) ⊗ₘ
         ((upperStarComp Ab.{u + 1} f g).hom.app BZ ≫
          (upperStar Ab.{u + 1} f).map bg ≫ bf)) := by
  simp only [Functor.map_comp, Category.assoc]
  rw [← Functor.OplaxMonoidal.δ_natural_assoc]
  change (upperStarComp Ab.{u + 1} f g).hom.app (AZ ⊗ BZ) ≫
    Functor.OplaxMonoidal.δ (upperStar Ab.{u + 1} g ⋙ upperStar Ab.{u + 1} f) AZ BZ ≫
    ((upperStar Ab.{u + 1} f).map ag ⊗ₘ (upperStar Ab.{u + 1} f).map bg) ≫
    (af ⊗ₘ bf) = _
  rw [← NatTrans.IsMonoidal.δ_comp_tensorHom_assoc]
  simp only [tensorHom_comp_tensorHom]

private theorem tensor_comp_eq {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (AZ BZ : Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
    (AY BY : Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
    (AX BX : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    (ag : (upperStar Ab.{u + 1} g).obj AZ ⟶ AY)
    (bg : (upperStar Ab.{u + 1} g).obj BZ ⟶ BY)
    (af : (upperStar Ab.{u + 1} f).obj AY ⟶ AX)
    (bf : (upperStar Ab.{u + 1} f).obj BY ⟶ BX)
    (afg : (upperStar Ab.{u + 1} (f ≫ g)).obj AZ ⟶ AX)
    (bfg : (upperStar Ab.{u + 1} (f ≫ g)).obj BZ ⟶ BX)
    (ha : (upperStarComp Ab.{u + 1} f g).hom.app AZ ≫
      (upperStar Ab.{u + 1} f).map ag ≫ af = afg)
    (hb : (upperStarComp Ab.{u + 1} f g).hom.app BZ ≫
      (upperStar Ab.{u + 1} f).map bg ≫ bf = bfg) :
    (upperStarComp Ab.{u + 1} f g).hom.app (AZ ⊗ BZ) ≫
        (upperStar Ab.{u + 1} f).map
          (Functor.OplaxMonoidal.δ (upperStar Ab.{u + 1} g) AZ BZ ≫ (ag ⊗ₘ bg)) ≫
        Functor.OplaxMonoidal.δ (upperStar Ab.{u + 1} f) AY BY ≫ (af ⊗ₘ bf) =
      Functor.OplaxMonoidal.δ (upperStar Ab.{u + 1} (f ≫ g)) AZ BZ ≫ (afg ⊗ₘ bfg) :=
  (tensor_comp f g AZ BZ AY BY AX BX ag bg af bf).trans
    (congrArg (Functor.OplaxMonoidal.δ (upperStar Ab.{u + 1} (f ≫ g)) AZ BZ ≫ ·)
      (congrArg₂ (fun a b ↦ a ⊗ₘ b) ha hb))

private theorem integral_level_comp (l : ℕ) [Fact l.Prime]
    (E : PadicAlgCl.FiniteIntermediateField l)
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (n : ℕ) :
    (upperStarComp Ab.{u + 1} f g).hom.app (spIntegralTwistLevel Z l E n).X ≫
      (upperStar Ab.{u + 1} f).map (integralLevelComparison g l E n) ≫
        integralLevelComparison f l E n = integralLevelComparison (f ≫ g) l E n := by
  exact tensor_comp_eq f g
    (condensedRingObj (spEllPointRingObj.{u} l E n) Z)
    (Scheme.proEtaleRootsOfUnitySheaf Z (l ^ (n + 1)))
    (condensedRingObj (spEllPointRingObj.{u} l E n) Y)
    (Scheme.proEtaleRootsOfUnitySheaf Y (l ^ (n + 1)))
    (condensedRingObj (spEllPointRingObj.{u} l E n) X)
    (Scheme.proEtaleRootsOfUnitySheaf X (l ^ (n + 1)))
    (condensedPullbackHom _ g) (Scheme.proEtaleRootsOfUnityInverseImageMap g _)
    (condensedPullbackHom _ f) (Scheme.proEtaleRootsOfUnityInverseImageMap f _)
    (condensedPullbackHom _ (f ≫ g)) (Scheme.proEtaleRootsOfUnityInverseImageMap (f ≫ g) _)
    (coefficient_comp _ f g) (roots_comp f g _)

private theorem comparison_square_comp {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z)
    {AZ BZ : Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}}
    {AY BY : Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}}
    {AX BX : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}}
    (pZ : AZ ⟶ BZ) (pY : AY ⟶ BY) (pX : AX ⟶ BX)
    (ag : (upperStar Ab.{u + 1} g).obj AZ ⟶ AY)
    (bg : (upperStar Ab.{u + 1} g).obj BZ ⟶ BY)
    (af : (upperStar Ab.{u + 1} f).obj AY ⟶ AX)
    (bf : (upperStar Ab.{u + 1} f).obj BY ⟶ BX)
    (hg : (upperStar Ab.{u + 1} g).map pZ ≫ bg = ag ≫ pY)
    (hf : (upperStar Ab.{u + 1} f).map pY ≫ bf = af ≫ pX) :
    (upperStar Ab.{u + 1} (f ≫ g)).map pZ ≫
        (upperStarComp Ab.{u + 1} f g).hom.app BZ ≫
        (upperStar Ab.{u + 1} f).map bg ≫ bf =
      (upperStarComp Ab.{u + 1} f g).hom.app AZ ≫
        (upperStar Ab.{u + 1} f).map ag ≫ af ≫ pX := by
  rw [NatTrans.naturality_assoc]
  simp only [Functor.comp_map]
  rw [← Functor.map_comp_assoc, hg, Functor.map_comp]
  simp only [Category.assoc]
  rw [hf]

private theorem integral_comp (l : ℕ) [Fact l.Prime]
    (E : PadicAlgCl.FiniteIntermediateField l)
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (upperStarComp Ab.{u + 1} f g).hom.app (spIntegralTwist Z l E).X ≫
        (upperStar Ab.{u + 1} f).map (spIntegralComparison g l E) ≫
        spIntegralComparison f l E = spIntegralComparison (f ≫ g) l E := by
  apply integral_maps_ext X l E
  intro n
  have h := comparison_square_comp f g
    (AZ := (spIntegralTwist Z l E).X) (AY := (spIntegralTwist Y l E).X)
    (AX := (spIntegralTwist X l E).X)
    (BZ := (spIntegralTwistLevel Z l E n).X)
    (BY := (spIntegralTwistLevel Y l E n).X)
    (BX := (spIntegralTwistLevel X l E n).X)
    (limit.π (spIntegralTwistSystem Z l E) (op n)).hom
    (limit.π (spIntegralTwistSystem Y l E) (op n)).hom
    (limit.π (spIntegralTwistSystem X l E) (op n)).hom
    (spIntegralComparison g l E) (integralLevelComparison g l E n)
    (spIntegralComparison f l E) (integralLevelComparison f l E n)
    (integralComparison_π g l E n).symm (integralComparison_π f l E n).symm
  simp only [Category.assoc] at h ⊢
  refine h.symm.trans ?_
  rw [integralComparison_π (f ≫ g) l E n]
  exact congrArg ((upperStar Ab.{u + 1} (f ≫ g)).map
    (limit.π (spIntegralTwistSystem Z l E) (op n)).hom ≫ ·)
      (integral_level_comp l E f g n)

private theorem rational_comp (l : ℕ) [Fact l.Prime]
    (E : PadicAlgCl.FiniteIntermediateField l)
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ x : Y, Invertible (l : Y.residueField x)]
    [∀ x : Z, Invertible (l : Z.residueField x)] :
    (upperStarComp Ab.{u + 1} f g).hom.app (spRationalTwist Z l E).X ≫
        (upperStar Ab.{u + 1} f).map ((adicComparison l g).rational E) ≫
        (adicComparison l f).rational E = (adicComparison l (f ≫ g)).rational E := by
  let q (T : Scheme.{u}) :=
    Mod.extendπ (padicIntegersToPadicSubfield T l E) (spIntegralTwist T l E)
  have : Epi ((upperStar Ab.{u + 1} (f ≫ g)).map (q Z)) := inferInstance
  apply (cancel_epi ((upperStar Ab.{u + 1} (f ≫ g)).map (q Z))).mp
  have h := comparison_square_comp f g
    (BZ := (spRationalTwist Z l E).X) (BY := (spRationalTwist Y l E).X)
    (BX := (spRationalTwist X l E).X) (q Z) (q Y) (q X)
    (Functor.OplaxMonoidal.δ (upperStar Ab.{u + 1} g) _ _ ≫
      (condensedPullbackHom (Profinite.continuousMapRingObj.{u} E.1) g ⊗ₘ
        spIntegralComparison g l E))
    ((adicComparison l g).rational E)
    (Functor.OplaxMonoidal.δ (upperStar Ab.{u + 1} f) _ _ ≫
      (condensedPullbackHom (Profinite.continuousMapRingObj.{u} E.1) f ⊗ₘ
        spIntegralComparison f l E))
    ((adicComparison l f).rational E)
    ((adicComparison l g).rational_scalar E) ((adicComparison l f).rational_scalar E)
  simp only [Category.assoc] at h ⊢
  have ht := tensor_comp_eq f g
    (condensedRingObj (Profinite.continuousMapRingObj.{u} E.1) Z) (spIntegralTwist Z l E).X
    (condensedRingObj (Profinite.continuousMapRingObj.{u} E.1) Y) (spIntegralTwist Y l E).X
    (condensedRingObj (Profinite.continuousMapRingObj.{u} E.1) X) (spIntegralTwist X l E).X
    (condensedPullbackHom _ g) (spIntegralComparison g l E)
    (condensedPullbackHom _ f) (spIntegralComparison f l E)
    (condensedPullbackHom _ (f ≫ g)) (spIntegralComparison (f ≫ g) l E)
    (coefficient_comp _ f g) (integral_comp l E f g)
  refine h.trans (Eq.trans ?_ ((adicComparison l (f ≫ g)).rational_scalar E).symm)
  simpa only [Category.assoc] using congrArg (fun k ↦ k ≫ q X) ht

private theorem qbar_comp (l : ℕ) [Fact l.Prime]
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ x : Y, Invertible (l : Y.residueField x)]
    [∀ x : Z, Invertible (l : Z.residueField x)] :
    (upperStarComp Ab.{u + 1} f g).hom.app (spQbarTwist Z l).X ≫
        (upperStar Ab.{u + 1} f).map (adicComparison l g).qbar ≫
        (adicComparison l f).qbar = (adicComparison l (f ≫ g)).qbar := by
  apply (isColimitOfPreserves (upperStar Ab.{u + 1} (f ≫ g))
    (colimit.isColimit (spRationalTwistDiagram Z l))).hom_ext
  intro E
  change (upperStar Ab.{u + 1} (f ≫ g)).map (colimit.ι _ E) ≫ _ = _
  have h := comparison_square_comp f g
    (BZ := (spQbarTwist Z l).X) (BY := (spQbarTwist Y l).X)
    (BX := (spQbarTwist X l).X)
    (AZ := (spRationalTwist Z l E).X) (AY := (spRationalTwist Y l E).X)
    (AX := (spRationalTwist X l E).X)
    (colimit.ι (spRationalTwistDiagram Z l) E)
    (colimit.ι (spRationalTwistDiagram Y l) E)
    (colimit.ι (spRationalTwistDiagram X l) E)
    ((adicComparison l g).rational E) (adicComparison l g).qbar
    ((adicComparison l f).rational E) (adicComparison l f).qbar
    ((adicComparison l g).qbar_coprojection E)
    ((adicComparison l f).qbar_coprojection E)
  refine h.trans (Eq.trans ?_ ((adicComparison l (f ≫ g)).qbar_coprojection E).symm)
  simpa only [Category.assoc] using
    congrArg (fun k ↦ k ≫ colimit.ι (spRationalTwistDiagram X l) E)
      (rational_comp l E f g)

private def abelianComparison (l : ℕ) [Fact l.Prime]
    (c : Option (PadicAlgCl.FiniteIntermediateField l)) {X Y : Scheme.{u}} (f : X ⟶ Y)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ x : Y, Invertible (l : Y.residueField x)] :
    (upperStar Ab.{u + 1} f).obj (line l c Y).X ⟶ (line l c X).X :=
  match c with
  | some E => (adicComparison l f).rational E
  | none => (adicComparison l f).qbar

private theorem lineComparison_adjunct (l : ℕ) [Fact l.Prime]
    (c : Option (PadicAlgCl.FiniteIntermediateField l)) {X Y : Scheme.{u}} (f : X ⟶ Y)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ x : Y, Invertible (l : Y.residueField x)] :
    ((CondensedRing.upperStarLowerStarAdjunction (coefficient l c).X f).homEquiv
      (line l c Y) (line l c X) (lineComparison l c f).hom).hom =
    (upperStarLowerStarAdjunction Ab.{u + 1} f).homEquiv _ _ (abelianComparison l c f) := by
  cases c <;> simp only [lineComparison, abelianComparison]
  all_goals
    -- Reuse the coefficient instances and Cartesianity witness already stored
    -- in lineComparison. Re-elaborating that witness unfolds large ring data.
    run_tac
      let goal ← Lean.Elab.Tactic.getMainGoal
      let target ← goal.getType
      let some iso := target.find? (fun e ↦ e.isAppOf ``linePullIso && !e.hasLooseBVars)
        | throwError "Expected the normalized linePullIso"
      let proof := Lean.mkAppN
        (Lean.mkConst ``linePull_adjunct iso.getAppFn.constLevels!) iso.getAppArgs
      Lean.Elab.Tactic.closeMainGoal `linePull_adjunct proof

private theorem abelianComparison_comp (l : ℕ) [Fact l.Prime]
    (c : Option (PadicAlgCl.FiniteIntermediateField l))
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ x : Y, Invertible (l : Y.residueField x)]
    [∀ x : Z, Invertible (l : Z.residueField x)] :
    (upperStarComp Ab.{u + 1} f g).hom.app (line l c Z).X ≫
      (upperStar Ab.{u + 1} f).map (abelianComparison l c g) ≫ abelianComparison l c f =
    abelianComparison l c (f ≫ g) := by
  cases c with
  | some E =>
    unfold abelianComparison line
    exact rational_comp l E f g
  | none =>
    unfold abelianComparison line
    exact qbar_comp l f g

attribute [local irreducible] abelianComparison

/-- The prescribed unshifted Tate-line comparison preserves composition. -/
theorem lineComparison_comp
    (l : ℕ) [Fact l.Prime] (c : Option (PadicAlgCl.FiniteIntermediateField l))
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ x : Y, Invertible (l : Y.residueField x)]
    [∀ x : Z, Invertible (l : Z.residueField x)] :
    (CondensedRing.upperStarComp (coefficient l c).X f g).hom.app (line l c Z) ≫
        (CondensedRing.upperStar (coefficient l c).X f).map (lineComparison l c g).hom ≫
        (lineComparison l c f).hom = (lineComparison l c (f ≫ g)).hom := by
  exact module_comparison_comp (coefficient l c).X f g
    (line l c Z) (line l c Y) (line l c X)
    (abelianComparison l c g) (abelianComparison l c f) (abelianComparison l c (f ≫ g))
    (lineComparison l c g).hom (lineComparison l c f).hom (lineComparison l c (f ≫ g)).hom
    (lineComparison_adjunct l c g) (lineComparison_adjunct l c f)
    (lineComparison_adjunct l c (f ≫ g)) (abelianComparison_comp l c f g)

end AlgebraicGeometry.ProEtale.RationalP1
