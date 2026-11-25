/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import WeilConjectures.AlgebraicGeometry.TorsionEtaleSheaf
public import Mathlib.Algebra.Category.Grp.ZModuleEquivalence
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Ring.ULift
import WeilConjectures.AlgebraicGeometry.TorsionSheafCharacterizations
import WeilConjectures.AlgebraicGeometry.FiniteLocalAbelianForget
import WeilConjectures.ConstructibleSheaf.Pullback
import WeilConjectures.Mathlib.CategoryTheory.Sites.Point.ConstantSheaf
import WeilConjectures.AlgebraicGeometry.FundamentalGroup.FiniteStalksComparison

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

private noncomputable abbrev integralCoefficients : AddCommGrpCat.{u + 1} ⥤
    ModuleCat.{u + 1} (ULift.{u + 1} ℤ) :=
  (forget₂ (ModuleCat.{u + 1} ℤ) AddCommGrpCat.{u + 1}).inv ⋙
    ModuleCat.restrictScalars (ULift.ringEquiv : ULift.{u + 1} ℤ ≃+* ℤ).toRingHom

private noncomputable def integralPullbackIso {X Y : Scheme.{u}} (g : Y ⟶ X)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    (sheafCompose Y.smallEtaleTopology integralCoefficients).obj
        ((Etale.upperStar AddCommGrpCat.{u + 1} g).obj F) ≅
      (Etale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) g).obj
        ((sheafCompose X.smallEtaleTopology integralCoefficients).obj F) := by
  let E := integralCoefficients.{u}
  let L := (MorphismProperty.Over.pullback @Etale ⊤ g).op
  have : Y.smallEtaleTopology.PreservesSheafification E :=
    GrothendieckTopology.instPreservesSheafification Y.smallEtaleTopology E
  let e₁ := (sheafComposeNatIso Y.smallEtaleTopology E
    (sheafificationAdjunction Y.smallEtaleTopology AddCommGrpCat.{u + 1})
    (sheafificationAdjunction Y.smallEtaleTopology
      (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)))).app (L.lan.obj F.obj)
  let e₂ := (presheafToSheaf Y.smallEtaleTopology
    (ModuleCat.{u + 1} (ULift.{u + 1} ℤ))).mapIso
      ((E.lanCompIsoOfPreserves L).app F.obj)
  exact e₁.symm ≪≫ e₂

private noncomputable def abelianSetPullbackIso {X Y : Scheme.{u}} (g : Y ⟶ X)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    (etaleSetPullback g).obj
        ((sheafCompose X.smallEtaleTopology
          (CategoryTheory.forget AddCommGrpCat.{u + 1})).obj F) ≅
      (sheafCompose Y.smallEtaleTopology (CategoryTheory.forget AddCommGrpCat.{u + 1})).obj
        ((Etale.upperStar AddCommGrpCat.{u + 1} g).obj F) := by
  let B := MorphismProperty.Over.pullback @Etale ⊤ g
  let U := CategoryTheory.forget AddCommGrpCat.{u + 1}
  let (V : Y.Etaleᵒᵖ) : IsFiltered (CostructuredArrow B.op V) :=
    IsFiltered.of_equivalence (structuredArrowOpEquivalence B V.unop)
  let : Limits.PreservesFilteredColimitsOfSize.{u, u + 1} U :=
    Limits.preservesFilteredColimitsOfSize_shrink.{u + 1, u + 1, u, u + 1} U
  let (V : Y.Etaleᵒᵖ) : U.PreservesPointwiseLeftKanExtensionAt F.obj B.op V := by
    infer_instance
  have : U.PreservesLeftKanExtension F.obj B.op := by infer_instance
  have : Y.smallEtaleTopology.PreservesSheafification U := by infer_instance
  let e := U.leftKanExtensionCompIsoOfPreserves F.obj B.op
  exact (presheafToSheaf Y.smallEtaleTopology (Type (u + 1))).mapIso e.symm ≪≫
    (sheafComposeNatIso Y.smallEtaleTopology U
      (sheafificationAdjunction Y.smallEtaleTopology AddCommGrpCat.{u + 1})
      (sheafificationAdjunction Y.smallEtaleTopology (Type (u + 1)))).app
        (B.op.leftKanExtension F.obj)

private theorem finiteLocalSets_of_iso {Y : Scheme.{u}}
    {G H : Sheaf Y.smallEtaleTopology (Type (u + 1))} (e : G ≅ H)
    (hG : IsFiniteLocallyConstantSheafOfTypes G) :
    IsFiniteLocallyConstantSheafOfTypes H := by
  obtain ⟨⟨𝒰, h𝒰⟩, hf⟩ := hG
  refine ⟨⟨𝒰, fun i ↦ ?_⟩, ?_⟩
  · have := h𝒰 i
    exact Sheaf.isConstant_congr _
      ((Y.smallEtaleTopology.overPullback (Type (u + 1)) _).mapIso e)
  · refine isFiniteSheaf_of_finite_algClosed_stalks _ fun Ω _ _ s ↦ ?_
    have := (ConcreteCategory.isFinitelyGenerated_iff_finite _).mp
      (hf.isFinitelyGenerated_sheafFiber Ω s)
    exact Finite.of_equiv _ (((pointSmallEtale s).sheafFiber.mapIso e).toEquiv)

private noncomputable def abelianConstantStalkIso {Y : Scheme.{u}}
    (G : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}) (U : Y.Etale)
    (A : AddCommGrpCat.{u + 1})
    (e : G.over U ≅ (constantSheaf (Y.smallEtaleTopology.over U)
      AddCommGrpCat.{u + 1}).obj A)
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ U.left) :
    ((pointSmallEtale (s ≫ U.hom)).sheafFiber
      (A := AddCommGrpCat.{u + 1})).obj G ≅ A := by
  let ePullback : (Etale.upperStar AddCommGrpCat.{u + 1} U.hom).obj G ≅
      (constantSheaf U.left.smallEtaleTopology AddCommGrpCat.{u + 1}).obj A :=
    (overSheafEquivFunctorObjOverIso AddCommGrpCat.{u + 1} U G).symm ≪≫
      (Etale.overSheafEquiv U AddCommGrpCat.{u + 1}).functor.mapIso e ≪≫
      ((Etale.overEquiv U).constantSheafSheafCongrIso
        (Y.smallEtaleTopology.over U) U.left.smallEtaleTopology
        AddCommGrpCat.{u + 1} CategoryTheory.Over.mkIdTerminal).app A
  have : Limits.PreservesFilteredColimitsOfSize.{u, u}
      (CategoryTheory.forget AddCommGrpCat.{u + 1}) :=
    Limits.preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1} _
  exact ((Etale.upperStarCompSheafFiberIso AddCommGrpCat.{u + 1} U.hom s).app G).symm ≪≫
    (pointSmallEtale s).sheafFiber.mapIso ePullback ≪≫
    (pointSmallEtale s).sheafFiberConstantSheafIso A

private theorem finiteAbelianStalks {Y : Scheme.{u}}
    (G : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hlc : IsLocallyConstantSheaf G)
    (hfinite : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ Y),
      Finite (((pointSmallEtale s).sheafFiber (A := AddCommGrpCat.{u + 1})).obj G))
    (Ω : Type u) [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ Y) :
    Finite (((pointSmallEtale s).sheafFiber (A := AddCommGrpCat.{u + 1})).obj G) := by
  classical
  have : JointlySurjective etalePrecoverage.{u} :=
    inferInstanceAs (JointlySurjective (precoverage @Etale))
  obtain ⟨d⟩ := hlc.nonempty_locallyConstantDatum
  obtain ⟨i, x, hx⟩ := d.cover.exists_eq (s default)
  have : Etale (d.cover.f i) := d.cover.map_prop i
  obtain ⟨t, ht, -⟩ := exists_fac_of_etale_of_isSepClosed (d.cover.f i) s x hx
  let U := d.cover.etalePrecoverageToEtale i
  have := d.isConstant i
  obtain ⟨A, ⟨e⟩⟩ := (G.over U).mem_essImage_of_isConstant
  let s₀ := U.left.algClosurePoint x
  have : Finite (((pointSmallEtale (s₀ ≫ U.hom)).sheafFiber
      (A := AddCommGrpCat.{u + 1})).obj G) := hfinite _ (s₀ ≫ U.hom)
  have : Finite A := Finite.of_equiv _
    (abelianConstantStalkIso G U A e.symm s₀).addCommGroupIsoToAddEquiv.toEquiv
  have hfin : Finite (((pointSmallEtale (t ≫ U.hom)).sheafFiber
      (A := AddCommGrpCat.{u + 1})).obj G) :=
    Finite.of_equiv A
      (abelianConstantStalkIso G U A e.symm t).addCommGroupIsoToAddEquiv.toEquiv.symm
  change Finite (((pointSmallEtale (t ≫ d.cover.f i)).sheafFiber
    (A := AddCommGrpCat.{u + 1})).obj G) at hfin
  simpa only [ht] using hfin

private theorem integralFiniteLocal {Y : Scheme.{u}}
    (G : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hG : IsLocallyConstantSheaf G ∧
      ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ Y),
        Finite (((pointSmallEtale s).sheafFiber (A := AddCommGrpCat.{u + 1})).obj G)) :
    IsFiniteLocallyConstantSheaf
      ((sheafCompose Y.smallEtaleTopology integralCoefficients).obj G) := by
  let E := integralCoefficients.{u}
  have hlocal : IsLocallyConstantSheaf ((sheafCompose Y.smallEtaleTopology E).obj G) := by
    obtain ⟨d⟩ := hG.1.nonempty_locallyConstantDatum
    refine ⟨⟨⟨d.cover, fun i ↦ ?_⟩⟩⟩
    have := d.isConstant i
    have : (Y.smallEtaleTopology.over (d.cover.etalePrecoverageToEtale i)).PreservesSheafification
        E := GrothendieckTopology.instPreservesSheafification _ E
    change ((sheafCompose (Y.smallEtaleTopology.over (d.cover.etalePrecoverageToEtale i))
      E).obj (G.over (d.cover.etalePrecoverageToEtale i))).IsConstant _
    infer_instance
  refine { toIsLocallyConstantSheaf := hlocal, isFinitelyGenerated_sheafFiber := ?_ }
  intro Ω _ _ s
  have hfinite : Finite (((pointSmallEtale s).sheafFiber
      (A := AddCommGrpCat.{u + 1})).obj G) :=
    finiteAbelianStalks G hG.1 hG.2 Ω s
  let V := forget₂ (ModuleCat.{u + 1} ℤ) AddCommGrpCat.{u + 1}
  let e₀ := V.asEquivalence.counitIso.app
    (((pointSmallEtale s).sheafFiber (A := AddCommGrpCat.{u + 1})).obj G)
  have hconverted : Finite (E.obj (((pointSmallEtale s).sheafFiber
      (A := AddCommGrpCat.{u + 1})).obj G)) :=
    @Finite.of_equiv _ _ hfinite e₀.addCommGroupIsoToAddEquiv.toEquiv.symm
  let e := ((pointSmallEtale s).sheafFiberCompIso E).app G
  have : Finite (((pointSmallEtale s).sheafFiber
      (A := ModuleCat.{u + 1} (ULift.{u + 1} ℤ))).obj
        ((sheafCompose Y.smallEtaleTopology E).obj G)) :=
    @Finite.of_equiv _ _ hconverted e.toLinearEquiv.toEquiv.symm
  apply (ModuleCat.isFinitelyGenerated_iff _).mpr
  infer_instance

/-- Backward direction of `isConstructibleSheaf_integral_iff`.
The proof refines finite set-valued trivializations so that the finite group
operation tables are constant; these are then integral-module trivializations.
Source: Stacks Project Tags 03RW and 095E; blueprint q1-constructible-integral-coefficients.
(blueprint: q1-constructible-integral-coefficients-backward) -/
theorem isConstructibleSheaf_integral_backward {X : Scheme.{u}}
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hF : X.IsTorsionAbelianSheaf F) :
    let E := (forget₂ (ModuleCat.{u + 1} ℤ) AddCommGrpCat.{u + 1}).inv ⋙
      ModuleCat.restrictScalars (ULift.ringEquiv : ULift.{u + 1} ℤ ≃+* ℤ).toRingHom
    IsConstructibleEtaleSheafOfSets
        ((sheafCompose X.smallEtaleTopology
          (CategoryTheory.forget AddCommGrpCat.{u + 1})).obj F) →
      IsConstructibleSheaf ((sheafCompose X.smallEtaleTopology E).obj F) := by
  have _hT := hF
  dsimp only
  intro hsets
  obtain ⟨S, hS⟩ := hsets
  refine ⟨⟨S, fun i ↦ ?_⟩⟩
  let g := S.immersion i
  let G := (Etale.upperStar AddCommGrpCat.{u + 1} g).obj F
  have hG := (finite_local_abelian_forget_iff G).mp
    (finiteLocalSets_of_iso (abelianSetPullbackIso g F) (hS i))
  have := integralFiniteLocal G hG
  exact IsFiniteLocallyConstantSheaf.of_iso (integralPullbackIso g F)

end AlgebraicGeometry.Scheme
