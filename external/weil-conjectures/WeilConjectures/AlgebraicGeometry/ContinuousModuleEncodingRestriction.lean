/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ContinuousCoefficientModuleEncoding
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.InternalHom

/-! # Restriction of continuous module encodings

Source: Bhatt--Scholze, Section 6.8; Stacks Project, Modules on Sites.
(auxiliary; not a blueprint node)
-/

@[expose] public section

universe u v
open CategoryTheory Opposite MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor TensorProduct

namespace AlgebraicGeometry.ProEtale.CondensedRing

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

/-- Restriction of a continuous-function coefficient ring is identity on sections.
Source: Bhatt--Scholze, Section 6.8.
(auxiliary; not a blueprint node) -/
noncomputable def continuousRestrictionMap
    {X Y : Scheme.{u}} (f : Y ⟶ X) [WeaklyEtale f]
    (T : Type) [CommRing T] [TopologicalSpace T] [IsTopologicalRing T] :
    (continuousMapRingSheaf Y T).obj ⟶
      (MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale f)).op ⋙
        (continuousMapRingSheaf X T).obj :=
  { app := fun _ ↦ 𝟙 _
    naturality := fun _ _ _ ↦ rfl }

/-- Encoding canonical inverse image agrees with restriction of the sectionwise module.
Source: Bhatt--Scholze, Section 6.8; Stacks Project, Tags 03EK and 03EL.
(auxiliary; not a blueprint node)

Proof. Apply the monoidal localization comparison to the underlying module.
Conjugate its coefficient map by the two continuous charts. The chart-pullback
square identifies the result with the identity continuous-function coefficient
map. Evaluating the actions on pure tensors gives the sectionwise linearity.
Naturality is the localization comparison's naturality. -/
theorem continuousRing_module_restriction
    (X Y : Scheme.{u}) (f : Y ⟶ X) [WeaklyEtale f]
    (T : Type) [CommRing T] [TopologicalSpace T] [IsTopologicalRing T]
    [TotallyDisconnectedSpace T]
    (P : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj T) X)) :
    Nonempty (((continuousRingModuleEquivalence Y T).functor.obj
        ((upperStar (Profinite.continuousMapRingObj T) f).obj P)).val ≅
      (PresheafOfModules.pushforward (continuousRestrictionMap f T)).obj
        ((continuousRingModuleEquivalence X T).functor.obj P).val) := by
  let G := ProEtale.upperStar Ab.{u + 1} f
  let L := (MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale f)).sheafPushforwardContinuous
    Ab.{u + 1} (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X)
  let τ := ProEtale.upperStarIsoSheafPushforward Ab.{u + 1} f inferInstance
  let cX := chartComparison X T
  let cY := chartComparison Y T
  let : IsIso cX := chartComparison_isIso X T
  let : IsIso cY := chartComparison_isIso Y T
  let : NatTrans.IsMonoidal τ.hom := inferInstance
  let φ := condensedPullbackHom (Profinite.continuousMapRingObj T) f
  let A := (sheafCompose (Scheme.ProEt.topology X)
    (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj (continuousMapRingSheaf X T)
  let C := condensedRingObj (Profinite.continuousMapRingObj T) X
  let : MonObj C := inferInstanceAs
    (MonObj (condensedRingObj (Profinite.continuousMapRingObj T) X))
  have hs : G.map cX ≫ τ.hom.app A = φ ≫ cY := continuousChart_pullback X Y f T
  have hc : (inv cY ≫ inv φ) ≫ τ.hom.app C = L.map (inv cX) := by
    apply (cancel_epi (φ ≫ cY)).mp
    simp only [Category.assoc, IsIso.hom_inv_id_assoc]
    calc
      τ.hom.app C = G.map cX ≫ τ.hom.app A ≫ L.map (inv cX) := by
        rw [← τ.hom.naturality]
        simp
        rfl
      _ = φ ≫ cY ≫ L.map (inv cX) := by rw [← Category.assoc, hs, Category.assoc]
  let : IsMonHom (τ.hom.app C) := NatTrans.isMonHom_app τ.hom C
  let Q := (G.mapMod C).obj P
  let ψ := inv cY ≫ inv φ
  let e := (Functor.mapModNatIso τ C).app P
  let Q' := (Mod.comap ψ).obj Q
  let Q'' := (Mod.comap ψ).obj ((Mod.comap (τ.hom.app C)).obj ((L.mapMod C).obj P))
  let R := continuousMapRingSheaf Y T
  let AY := (sheafCompose (Scheme.ProEt.topology Y)
    (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj R
  let : IsCommMonObj AY := Sheaf.isCommMonObj_sheafCompose_obj _ R
    (fun V a b ↦ by exact @mul_comm (ULift C(V.unop.left, T)) inferInstance a b)
  let H := (InternalAbelianSheafModule.sectionModuleEquivalence
    (Scheme.ProEt.topology Y) AY).functor ⋙
      (ringModuleEquivalenceOfIso Y (reconstructedRingIso Y R).symm).functor
  let e₀ := ((Mod.comap (inv cY)).mapIso ((Mod.extendScalarsIsoComapInv φ).app Q)) ≪≫
    ((Mod.comapComp (inv cY) (inv φ)).app Q).symm ≪≫
      (Mod.comap ψ).mapIso e
  refine ⟨((SheafOfModules.forget _).mapIso (H.mapIso e₀)) ≪≫ ?_⟩
  refine PresheafOfModules.isoMk (fun Z ↦ ?_) ?_
  · refine ModuleCat.isoMk (Iso.refl _) ?_
    intro r
    ext m
    let Z' := (MorphismProperty.Over.map ⊤
      (inferInstance : WeaklyEtale f)).op.obj Z
    have ha :
        (Functor.LaxMonoidal.μ (sheafToPresheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
          AY (L.obj P.X)).app Z ≫
          (ψ ▷ _ ≫ (τ.hom.app C) ▷ _ ≫
            Functor.LaxMonoidal.μ L C P.X ≫ L.map (Mod.act P.X)).hom.app Z =
        (Functor.LaxMonoidal.μ (sheafToPresheaf (Scheme.ProEt.topology X) Ab.{u + 1})
          A P.X).app Z' ≫ ((inv cX) ▷ P.X ≫ Mod.act P.X).hom.app Z' := by
      have hh : ψ ▷ L.obj P.X ≫ (τ.hom.app C) ▷ L.obj P.X =
          (L.map (inv cX)) ▷ L.obj P.X := by
        rw [← comp_whiskerRight]
        exact congrArg (fun a ↦ a ▷ L.obj P.X) hc
      rw [← Category.assoc (ψ ▷ _) ((τ.hom.app C) ▷ _) _, hh]
      rw [Functor.LaxMonoidal.μ_natural_left_assoc L (inv cX) P.X,
        ← Functor.map_comp]
      simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app]
      rw [← Category.assoc]
      erw [Functor.μ_sheafToPresheaf_app_comp_μ_sheafPushforwardContinuous_app
          (MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale f)) Ab.{u + 1}
          (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X) A P.X Z]
      rfl
    exact ConcreteCategory.congr_hom ha.symm (r ⊗ₜ[ℤ] m)
  · intro Z W a
    ext m
    rfl

private theorem coefficientCast_app
    {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C)
    [J.HasSheafCompose (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})]
    {R S : Sheaf J CommRingCat.{u + 1}} (h : R = S) (Z : Cᵒᵖ) :
    ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
      (eqToHom h)).hom.app Z =
      eqToHom (congrArg (fun R : Sheaf J CommRingCat.{u + 1} ↦
        ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R).obj.obj Z) h) := by
  subst h
  simp

private theorem ringModuleEquivalenceOfIso_val (X : Scheme.{u})
    {R S : Sheaf (Scheme.ProEt.topology X) RingCat.{u + 1}} (e : S ≅ R)
    (M : SheafOfModules.{u + 1} R) :
    ((ringModuleEquivalenceOfIso X e).functor.obj M).val =
      (PresheafOfModules.pushforward (F := 𝟭 X.ProEt) e.hom.hom).obj M.val := rfl

private noncomputable def pushforwardSquare
    {C D : Type (u + 1)} [Category.{u} C] [Category.{u} D] (F : C ⥤ D)
    {R R' : Dᵒᵖ ⥤ RingCat.{u + 1}} {S S' : Cᵒᵖ ⥤ RingCat.{u + 1}}
    (pY : S' ⟶ S) (pX : R' ⟶ R) (j : S ⟶ F.op ⋙ R) (j' : S' ⟶ F.op ⋙ R')
    (h : pY ≫ j = j' ≫ F.op.whiskerLeft pX) :
    PresheafOfModules.pushforward.{u + 1} j ⋙
        PresheafOfModules.pushforward (F := 𝟭 C) pY ≅
      PresheafOfModules.pushforward (F := 𝟭 D) pX ⋙ PresheafOfModules.pushforward j' :=
  PresheafOfModules.pushforwardComp (F := 𝟭 C) (G := F) pY j ≪≫
    eqToIso (congrArg (fun a ↦ PresheafOfModules.pushforward (F := F) a) h) ≪≫
      (PresheafOfModules.pushforwardComp (F := F) (G := 𝟭 D) j' pX).symm

private theorem ringModule_restrictionOfIso
    (X Y : Scheme.{u}) (F : Y.ProEt ⥤ X.ProEt)
    {R₁ S₁ : Sheaf (Scheme.ProEt.topology X) RingCat.{u + 1}}
    {R₂ S₂ : Sheaf (Scheme.ProEt.topology Y) RingCat.{u + 1}}
    (eX : S₁ ≅ R₁) (eY : S₂ ≅ R₂)
    (j : R₂.obj ⟶ F.op ⋙ R₁.obj) (j' : S₂.obj ⟶ F.op ⋙ S₁.obj)
    (h : eY.hom.hom ≫ j = j' ≫ F.op.whiskerLeft eX.hom.hom)
    (M : SheafOfModules.{u + 1} R₁) (N : SheafOfModules.{u + 1} R₂)
    (e : N.val ≅ (PresheafOfModules.pushforward j).obj M.val) :
    Nonempty (((ringModuleEquivalenceOfIso Y eY).functor.obj N).val ≅
      (PresheafOfModules.pushforward j').obj
        ((ringModuleEquivalenceOfIso X eX).functor.obj M).val) := by
  rw [ringModuleEquivalenceOfIso_val, ringModuleEquivalenceOfIso_val]
  exact ⟨(PresheafOfModules.pushforward (F := 𝟭 _) eY.hom.hom).mapIso e ≪≫
    (pushforwardSquare F eY.hom.hom eX.hom.hom j j' h).app M.val⟩

section FieldRestriction

private theorem continuousFieldModuleEquivalence_functor
    (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [NormedField E]
    [NormedAlgebra ℚ_[ℓ] E] [FiniteDimensional ℚ_[ℓ] E] [TotallyDisconnectedSpace E]
    (X : Scheme.{u}) :
    (continuousFieldModuleEquivalence ℓ E X).functor =
      (continuousRingModuleEquivalence X E).functor ⋙
        (ringModuleEquivalenceOfIso X ((sheafCompose (Scheme.ProEt.topology X)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).mapIso
            (eqToIso (lisseFieldSheaf_eq ℓ E X)))).functor := rfl

private theorem field_restriction_transport
    (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [NormedField E]
    [NormedAlgebra ℚ_[ℓ] E] [FiniteDimensional ℚ_[ℓ] E]
    (X Y : Scheme.{u}) (f : Y ⟶ X) [Etale f]
    (P : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj E) X))
    [TotallyDisconnectedSpace E]
    (U : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj E) Y))
    (e : ((continuousRingModuleEquivalence Y E).functor.obj U).val ≅
      (PresheafOfModules.pushforward (continuousRestrictionMap f E)).obj
        ((continuousRingModuleEquivalence X E).functor.obj P).val) :
    Nonempty (((continuousFieldModuleEquivalence ℓ E Y).functor.obj
        U).val ≅
      (PresheafOfModules.pushforward (lisseEtaleCoefficientIdentification ℓ E f)).obj
        ((continuousFieldModuleEquivalence ℓ E X).functor.obj P).val) := by
  let eY := (sheafCompose (Scheme.ProEt.topology Y)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).mapIso
      (eqToIso (lisseFieldSheaf_eq ℓ E Y))
  let eX := (sheafCompose (Scheme.ProEt.topology X)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).mapIso
      (eqToIso (lisseFieldSheaf_eq ℓ E X))
  let F := lisseEtaleSiteInclusion f
  let pY := eY.hom.hom
  let pX := eX.hom.hom
  let j := continuousRestrictionMap f E
  let j' := lisseEtaleCoefficientIdentification ℓ E f
  have h : pY ≫ (𝟭 Y.ProEt).op.whiskerLeft j = j' ≫ F.op.whiskerLeft pX := by
    apply NatTrans.ext
    funext Z
    change eY.hom.hom.app Z = eX.hom.hom.app (F.op.obj Z)
    change ((sheafCompose (Scheme.ProEt.topology Y)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
        (eqToHom (lisseFieldSheaf_eq ℓ E Y))).hom.app Z =
      ((sheafCompose (Scheme.ProEt.topology X)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
          (eqToHom (lisseFieldSheaf_eq ℓ E X))).hom.app (F.op.obj Z)
    rw [coefficientCast_app, coefficientCast_app]
  have hpush : PresheafOfModules.pushforward.{u + 1} (F := F) j =
      PresheafOfModules.pushforward j := rfl
  let M := (continuousRingModuleEquivalence X E).functor.obj P
  let N := (continuousRingModuleEquivalence Y E).functor.obj U
  let eF : N.val ≅ (PresheafOfModules.pushforward (F := F) j).obj M.val :=
    e ≪≫ (eqToIso hpush.symm).app M.val
  obtain ⟨en⟩ := ringModule_restrictionOfIso X Y F eX eY j j' h M N eF
  let eFY := (eqToIso (continuousFieldModuleEquivalence_functor ℓ E Y)).app U
  let eFX := (eqToIso (continuousFieldModuleEquivalence_functor ℓ E X)).app P
  exact ⟨(SheafOfModules.forget _).mapIso
    eFY ≪≫
      en ≪≫ (PresheafOfModules.pushforward j').mapIso
        ((SheafOfModules.forget _).mapIso eFX.symm)⟩

/-- The rational encoding commutes with the etale restriction used in a lattice.
Source: Bhatt--Scholze, Proposition 6.8.4(6).
(auxiliary; not a blueprint node)

Proof. Apply continuousRing_module_restriction and transport its coefficient
rings through lisseFieldSheaf_eq. These transports commute with restriction
because they are induced by the same equality of coefficient topologies. -/
theorem continuousField_module_restriction
    (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [NormedField E]
    [NormedAlgebra ℚ_[ℓ] E] [FiniteDimensional ℚ_[ℓ] E]
    (X Y : Scheme.{u}) (f : Y ⟶ X) [Etale f]
    (P : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj E) X)) :
    Nonempty (((continuousFieldModuleEquivalence ℓ E Y).functor.obj
        ((upperStar (Profinite.continuousMapRingObj E) f).obj P)).val ≅
      (PresheafOfModules.pushforward (lisseEtaleCoefficientIdentification ℓ E f)).obj
        ((continuousFieldModuleEquivalence ℓ E X).functor.obj P).val) := by
  rename_i _ hE _ _ _
  let : IsUltrametricDist E := IsUltrametricDist.of_normedAlgebra ℚ_[ℓ]
  let : TotallySeparatedSpace E :=
    totallySeparatedSpace_iff_exists_isClopen.mpr fun x y h ↦ by
      obtain ⟨r, hr, hr'⟩ := exists_between (dist_pos.mpr h)
      refine ⟨_, IsUltrametricDist.isClopen_ball x r, ?_, ?_⟩
      · simp only [Metric.mem_ball, dist_self, hr]
      · simp only [Set.mem_compl, Metric.mem_ball, dist_comm, not_lt, hr'.le]
  -- Compare functors before evaluating them: reducing scalar extension here is expensive.
  have hF :
      upperStar (@Profinite.continuousMapRingObj E _ hE.toField.toDivisionRing.toRing _) f =
        upperStar (@Profinite.continuousMapRingObj E _ hE.toField.toCommRing.toRing _) f := rfl
  obtain ⟨e⟩ := continuousRing_module_restriction X Y f E P
  let eU := (eqToIso hF).app P
  let e' := (SheafOfModules.forget _).mapIso
    ((continuousRingModuleEquivalence Y E).functor.mapIso eU) ≪≫ e
  exact field_restriction_transport ℓ E X Y f P _ e'

end FieldRestriction

end AlgebraicGeometry.ProEtale.CondensedRing
