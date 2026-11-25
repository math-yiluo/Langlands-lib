/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.Tate.ProEtaleTateTwists

import WeilConjectures.AlgebraicGeometry.Native.NativeIntegralTateFiniteRepresentation
import WeilConjectures.AlgebraicGeometry.Limits.AffineOverLimitProperties
import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
import Mathlib.CategoryTheory.Sites.PreservesLimits
import Mathlib.CategoryTheory.Category.ULift
import WeilConjectures.CategoryTheory.SheafPullbackForgetComparison
import Mathlib.CategoryTheory.Sites.Pullback
import WeilConjectures.Mathlib.CategoryTheory.Functor.Flat

/-! # Inverse image preserves the native integral Tate tower limit

## References

* Stacks Project, Sites, Tag 03CF
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj CategoryTheory.MonObj

namespace AlgebraicGeometry.ProEtale

private theorem lift_representable_diagram
    {C B I : Type*} [Category C] [Category B] [Category I]
    (F : C ⥤ B) [F.Full] [F.Faithful] (A : I ⥤ B)
    (V : I → C) (e : ∀ i, F.obj (V i) ≅ A.obj i) :
    ∃ D : I ⥤ C, (∀ i, D.obj i = V i) ∧ Nonempty (D ⋙ F ≅ A) := by
  let D : I ⥤ C :=
    { obj := V
      map {i j} g := F.preimage ((e i).hom ≫ A.map g ≫ (e j).inv)
      map_id i := by
        apply F.map_injective
        simp
      map_comp g h := by
        apply F.map_injective
        simp [Category.assoc] }
  refine ⟨D, fun _ ↦ rfl, ⟨NatIso.ofComponents e ?_⟩⟩
  intro i j g
  change F.map (F.preimage _) ≫ (e j).hom = _
  simp [Category.assoc]

private theorem finiteEtale_geometric_limit
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    {I : Type u} [SmallCategory I] [IsCofiltered I]
    (D : I ⥤ Y.ProEt)
    (hfin : ∀ i, IsFinite (D.obj i).hom) (het : ∀ i, Etale (D.obj i).hom) :
    HasLimit D ∧ PreservesLimit D (Scheme.proEtaleBaseChange f) := by
  let A := D ⋙ Scheme.ProEt.forget Y ⋙ Over.forget Y
  let p (i : I) : A.obj i ⟶ Y := (D.obj i).hom
  have hp {i j : I} (g : i ⟶ j) : A.map g ≫ p j = p i := (D.map g).w
  let (i : I) : IsFinite (p i) := hfin i
  let (i : I) : Etale (p i) := het i
  let (i : I) : IsAffineHom (p i) := inferInstance
  let cA := Scheme.AffineOverLimit.limitCone A p hp
  let hcA := Scheme.AffineOverLimit.isLimitLimitCone A p hp
  let q := Scheme.AffineOverLimit.limitHom A p hp
  have hq (i : I) : cA.π.app i ≫ p i = q := Scheme.AffineOverLimit.π_p A p hp i
  let : WeaklyEtale q := Scheme.weaklyEtale_of_isLimit A hcA p hp q hq
  let c : Cone D :=
    { pt := Scheme.ProEt.mk q
      π :=
        { app i := MorphismProperty.Over.homMk (cA.π.app i) (hq i)
          naturality i j g := by
            apply MorphismProperty.Over.Hom.ext
            change 𝟙 _ ≫ cA.π.app j = cA.π.app i ≫ A.map g
            exact (Category.id_comp _).trans (cA.w g).symm } }
  have hcOver : IsLimit ((Scheme.ProEt.forget Y).mapCone c) := by
    apply isLimitOfReflects (Over.forget Y)
    exact hcA
  have hc : IsLimit c := isLimitOfReflects (Scheme.ProEt.forget Y) hcOver
  have hfc : IsLimit ((Scheme.proEtaleBaseChange f).mapCone c) := by
    apply isLimitOfReflects (Scheme.ProEt.forget X)
    exact isLimitOfPreserves (Over.pullback f) hcOver
  exact ⟨⟨⟨⟨c, hc⟩⟩⟩, preservesLimit_of_preserves_limit_cone hc hfc⟩

private noncomputable def representableInverseImageIso
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    Scheme.proEtaleBaseChange f ⋙ (Scheme.ProEt.topology X).uliftYoneda.{u + 1} ≅
      (Scheme.ProEt.topology Y).uliftYoneda.{u + 1} ⋙
        Scheme.proEtaleSheafInverseImage f (Type (u + 1)) := by
  let e := Presheaf.compULiftYonedaIsoULiftYonedaCompLan.{u + 1}
    (Scheme.proEtaleBaseChange f)
  exact Functor.isoWhiskerLeft
    (Scheme.proEtaleBaseChange f ⋙ (Scheme.ProEt.topology X).uliftYoneda.{u + 1})
    (sheafificationNatIso (Scheme.ProEt.topology X) (Type (u + 1))) ≪≫
    Functor.isoWhiskerRight e
      (presheafToSheaf (Scheme.ProEt.topology X) (Type (u + 1)))

private noncomputable def abelianForgetInverseImageIso
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    upperStar AddCommGrpCat.{u + 1} f ⋙
      sheafCompose (Scheme.ProEt.topology X) (forget AddCommGrpCat.{u + 1}) ≅
    sheafCompose (Scheme.ProEt.topology Y) (forget AddCommGrpCat.{u + 1}) ⋙
      Scheme.proEtaleSheafInverseImage f (Type (u + 1)) := by
  let : RepresentablyFlat (Scheme.proEtaleBaseChange f) := flat_of_preservesFiniteLimits _
  let : (forget AddCommGrpCat.{u + 1}).PreservesLeftKanExtensions
      (Scheme.proEtaleBaseChange f).op := by
    intro P
    let : PreservesFilteredColimitsOfSize.{u, u + 1}
        (forget AddCommGrpCat.{u + 1}) :=
      preservesFilteredColimitsOfSize_shrink.{u + 1, u + 1, u, u + 1} _
    let : ∀ V, Functor.PreservesPointwiseLeftKanExtensionAt
        (forget AddCommGrpCat.{u + 1}) P (Scheme.proEtaleBaseChange f).op V := by
      intro V
      infer_instance
    infer_instance
  exact sheafPullbackForgetIso (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X)
    (Scheme.proEtaleBaseChange f) (forget AddCommGrpCat.{u + 1})

/-- The particular inverse limit defining the integral Tate line is preserved by
inverse image. This asserts preservation of this tower, rather than arbitrary limits. -/
theorem spIntegralTwist_inverseImage_isLimit
    {X Y : Scheme.{u}} (f : X ⟶ Y) (ℓ : ℕ) [Fact ℓ.Prime]
    [∀ x : X, Invertible (ℓ : X.residueField x)]
    [∀ y : Y, Invertible (ℓ : Y.residueField y)]
    (E : PadicAlgCl.FiniteIntermediateField ℓ) :
    Nonempty (IsLimit ((upperStar AddCommGrpCat.{u + 1} f).mapCone
      ((Mod.forget
        (C := Sheaf (Scheme.ProEt.topology Y) AddCommGrpCat.{u + 1})
        (D := Sheaf (Scheme.ProEt.topology Y) AddCommGrpCat.{u + 1})
        (condensedRingObj (Profinite.padicIntegersRingObj.{u} ℓ E.1) Y)).mapCone
        (limit.cone (spIntegralTwistSystem Y ℓ E))))) := by
  let T := spIntegralTwistSystem Y ℓ E
  let V := Mod.forget
    (C := Sheaf (Scheme.ProEt.topology Y) AddCommGrpCat.{u + 1})
    (D := Sheaf (Scheme.ProEt.topology Y) AddCommGrpCat.{u + 1})
    (condensedRingObj (Profinite.padicIntegersRingObj.{u} ℓ E.1) Y)
  let Ry := sheafCompose (Scheme.ProEt.topology Y) (forget AddCommGrpCat.{u + 1})
  let Rx := sheafCompose (Scheme.ProEt.topology X) (forget AddCommGrpCat.{u + 1})
  let L := upperStar AddCommGrpCat.{u + 1} f
  let P := Scheme.proEtaleSheafInverseImage f (Type (u + 1))
  classical
  choose W hfin het e using spIntegralTwistLevel_finiteEtale_representation Y ℓ E
  obtain ⟨D, hD, ⟨e⟩⟩ := lift_representable_diagram
    (Scheme.ProEt.topology Y).uliftYoneda.{u + 1} (T ⋙ V ⋙ Ry)
    (fun n ↦ W n.unop) (fun n ↦ (e n.unop).some)
  have hfinD (n : ℕᵒᵖ) : IsFinite (D.obj n).hom := by rw [hD]; exact hfin _
  have hetD (n : ℕᵒᵖ) : Etale (D.obj n).hom := by rw [hD]; exact het _
  let liftIndex : ℕᵒᵖ ≌ AsSmall.{u} ℕᵒᵖ := AsSmall.equiv
  let : IsCofiltered (AsSmall.{u} ℕᵒᵖ) := IsCofiltered.of_equivalence liftIndex
  obtain ⟨hlim, hpres⟩ := finiteEtale_geometric_limit f
    (liftIndex.inverse ⋙ D) (fun i ↦ hfinD (ULift.down i)) (fun i ↦ hetD (ULift.down i))
  let := hlim
  let := hpres
  let : HasLimit D := Functor.Initial.hasLimit_of_comp liftIndex.inverse
  let : PreservesLimit D (Scheme.proEtaleBaseChange f) :=
    Functor.Initial.preservesLimit_of_comp liftIndex.inverse
  let Ly := (Scheme.ProEt.topology Y).uliftYoneda.{u + 1}
  let Lx := (Scheme.ProEt.topology X).uliftYoneda.{u + 1}
  let : PreservesLimit D (Scheme.proEtaleBaseChange f ⋙ Lx) := inferInstance
  let : PreservesLimit D (Ly ⋙ P) :=
    preservesLimit_of_natIso D (representableInverseImageIso f)
  let : PreservesLimit (D ⋙ Ly) P := by
    exact preservesLimit_of_preserves_limit_cone
      (isLimitOfPreserves Ly (limit.isLimit D))
      (isLimitOfPreserves (Ly ⋙ P) (limit.isLimit D))
  let : PreservesLimit ((T ⋙ V) ⋙ Ry) P :=
    preservesLimit_of_iso_diagram P (e ≪≫ (Functor.associator T V Ry).symm)
  let : PreservesLimitsOfShape ℕᵒᵖ (Ry ⋙ sheafToPresheaf _ _) :=
    inferInstanceAs (PreservesLimitsOfShape ℕᵒᵖ
      (sheafToPresheaf (Scheme.ProEt.topology Y) AddCommGrpCat.{u + 1} ⋙
        (Functor.whiskeringRight _ _ _).obj (forget AddCommGrpCat.{u + 1})))
  let : PreservesLimitsOfShape ℕᵒᵖ Ry :=
    preservesLimitsOfShape_of_reflects_of_preserves Ry (sheafToPresheaf _ _)
  let : PreservesLimitsOfShape ℕᵒᵖ (Rx ⋙ sheafToPresheaf _ _) :=
    inferInstanceAs (PreservesLimitsOfShape ℕᵒᵖ
      (sheafToPresheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1} ⋙
        (Functor.whiskeringRight _ _ _).obj (forget AddCommGrpCat.{u + 1})))
  let : PreservesLimitsOfShape ℕᵒᵖ Rx :=
    preservesLimitsOfShape_of_reflects_of_preserves Rx (sheafToPresheaf _ _)
  let : ReflectsLimitsOfShape ℕᵒᵖ Rx := reflectsLimitsOfShape_of_reflectsIsomorphisms
  let : PreservesLimit (T ⋙ V) (Ry ⋙ P) :=
    preservesLimit_of_preserves_limit_cone (limit.isLimit (T ⋙ V))
      (isLimitOfPreserves P (isLimitOfPreserves Ry (limit.isLimit (T ⋙ V))))
  let : PreservesLimit (T ⋙ V) (L ⋙ Rx) :=
    preservesLimit_of_natIso (T ⋙ V) (abelianForgetInverseImageIso f).symm
  let : PreservesLimit (T ⋙ V) L := preservesLimit_of_reflects_of_preserves L Rx
  exact ⟨isLimitOfPreserves L (isLimitOfPreserves V (limit.isLimit T))⟩

end AlgebraicGeometry.ProEtale
