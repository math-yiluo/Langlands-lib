/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.RingComplexGodementConstruction
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
import WeilConjectures.AlgebraicGeometry.FiniteOrderedFlasqueCechComparison
import WeilConjectures.AlgebraicGeometry.ModuleCupGodementModelQuasiIso
import WeilConjectures.AlgebraicGeometry.ModuleCupGodementObjectFlasque
import WeilConjectures.AlgebraicGeometry.RingComplexGodementAffineSections
import WeilConjectures.AlgebraicGeometry.RingComplexOrderedCechCoordinates

/-! # The augmented ordered localization model of Godement ring complexes -/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

noncomputable section

private theorem constant_preservesHomology (A : CommRingCat.{u}) :
    (ringComplexConstant A).PreservesHomology := by
  let E : RingSiteModules A ⥤ ModuleCat.{u} A :=
    SheafOfModules.evaluation _ (op ⟨PUnit.unit⟩)
  have : E.PreservesZeroMorphisms := ⟨by intros; rfl⟩
  have : E.Faithful := ⟨by
    intro M N f g h
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    rintro ⟨⟨⟨⟩⟩⟩
    exact h⟩
  apply Functor.preservesHomology_of_map_exact
  intro S hS
  exact E.reflects_exact_of_faithful (S.map (ringComplexConstant A)) hS

private theorem fibre_square_iso (A : CommRingCat.{u})
    [HasDerivedCategory.{w} (RingSiteModules A)]
    {L M : CochainComplex (RingSiteModules A) ℤ}
    (ρ : ringComplexSingle A ⟶ L) (τ : ringComplexSingle A ⟶ M)
    (b : L ⟶ M) [QuasiIso b] (hb : ρ ≫ b = τ) :
    ∃ e : DerivedCategory.Q.obj (CochainComplex.mappingCone.triangle ρ).invRotate.obj₁ ≅
        DerivedCategory.Q.obj (CochainComplex.mappingCone.triangle τ).invRotate.obj₁,
      e.hom ≫ DerivedCategory.Q.map (CochainComplex.mappingCone.triangle τ).invRotate.mor₁ =
        DerivedCategory.Q.map (CochainComplex.mappingCone.triangle ρ).invRotate.mor₁ := by
  let t := CochainComplex.mappingCone.triangleMap ρ τ (𝟙 _) b (by simpa using hb)
  have hc : IsIso (DerivedCategory.Q.map t.hom₃) :=
    CategoryTheory.Pretriangulated.isIso₃_of_isIso₁₂
      (DerivedCategory.Q.mapTriangle.map t)
      (DerivedCategory.mappingCone_triangle_distinguished ρ)
      (DerivedCategory.mappingCone_triangle_distinguished τ)
      (by change IsIso (DerivedCategory.Q.map (𝟙 _)); infer_instance)
      (by change IsIso (DerivedCategory.Q.map b); infer_instance)
  have : QuasiIso t.hom₃ := (DerivedCategory.isIso_Q_map_iff_quasiIso (RingSiteModules A) _).mp hc
  let t' := (CategoryTheory.Pretriangulated.invRotate _).map t
  have : QuasiIso t'.hom₁ := by
    change QuasiIso (t.hom₃⟦(-1 : ℤ)⟧')
    infer_instance
  refine ⟨asIso (DerivedCategory.Q.map t'.hom₁), ?_⟩
  have h := congrArg (fun f ↦ DerivedCategory.Q.map f) t'.comm₁
  change DerivedCategory.Q.map
      ((CochainComplex.mappingCone.triangle ρ).invRotate.mor₁ ≫ 𝟙 _) =
    DerivedCategory.Q.map
      (t'.hom₁ ≫ (CochainComplex.mappingCone.triangle τ).invRotate.mor₁) at h
  simpa only [Functor.map_comp, asIso_hom, Functor.map_id, Category.comp_id] using h.symm

private theorem fibre_roof_iso (A : CommRingCat.{u})
    [HasDerivedCategory.{w} (RingSiteModules A)]
    {L M D : CochainComplex (RingSiteModules A) ℤ}
    (ρ : ringComplexSingle A ⟶ L) (τ : ringComplexSingle A ⟶ M)
    (α : L ⟶ D) (β : M ⟶ D) [QuasiIso α] [QuasiIso β]
    (h : ρ ≫ α = τ ≫ β) :
    ∃ e : DerivedCategory.Q.obj (CochainComplex.mappingCone.triangle τ).invRotate.obj₁ ≅
        DerivedCategory.Q.obj (CochainComplex.mappingCone.triangle ρ).invRotate.obj₁,
      e.hom ≫ DerivedCategory.Q.map (CochainComplex.mappingCone.triangle ρ).invRotate.mor₁ =
        DerivedCategory.Q.map (CochainComplex.mappingCone.triangle τ).invRotate.mor₁ := by
  obtain ⟨a, ha⟩ := fibre_square_iso A ρ (ρ ≫ α) α rfl
  obtain ⟨b, hb⟩ := fibre_square_iso A τ (ρ ≫ α) β h.symm
  refine ⟨b ≪≫ a.symm, ?_⟩
  rw [Iso.trans_hom, Iso.symm_hom, Category.assoc, ← ha, Iso.inv_hom_id_assoc]
  exact hb

private theorem godement_flasque (X : Scheme.{u}) (q : ℕ) :
    TopCat.Sheaf.IsFlasque ((SheafOfModules.toSheaf (moduleRings X.toRingedSpace)).obj
      ((ringComplexGodementResolution X).X (q : ℤ))) := by
  let F := SheafOfModules.unit (moduleRings X.toRingedSpace)
  have h := (Scheme.Modules.moduleCup_godement_models_exist X F).choose_spec.choose_spec.1
  obtain ⟨ht, _, _⟩ := h
  let e : (ringComplexGodementResolution X).X (q : ℤ) ≅
      Scheme.Modules.moduleCup_godementIterate X F (q + 1) :=
    (((AlgebraicTopology.alternatingCofaceMapComplex X.Modules).obj
      (ringComplexGodementModel X)).extendXIso ComplexShape.embeddingUpNat rfl) ≪≫
        eqToIso (ht q)
  let E := (SheafOfModules.toSheaf (moduleRings X.toRingedSpace)).mapIso e
  have hn := Scheme.Modules.moduleCup_godement_object_flasque X
    (Scheme.Modules.moduleCup_godementIterate X F q)
  constructor
  intro U V i
  have : Epi (((SheafOfModules.toSheaf (moduleRings X.toRingedSpace)).obj
      (Scheme.Modules.moduleCup_godementIterate X F (q + 1))).obj.map i) := hn.epi i
  have he := E.hom.hom.naturality i
  have hr : (((SheafOfModules.toSheaf (moduleRings X.toRingedSpace)).obj
      ((ringComplexGodementResolution X).X (q : ℤ))).obj.map i) =
      E.hom.hom.app U ≫
        (((SheafOfModules.toSheaf (moduleRings X.toRingedSpace)).obj
          (Scheme.Modules.moduleCup_godementIterate X F (q + 1))).obj.map i) ≫
            E.inv.hom.app V := by
    rw [← Category.assoc, ← he, Category.assoc]
    simp
  rw [hr]
  infer_instance

/-- The Godement mapping fibre has the augmented ordered localization model.
Source: Stacks Project, Tags 099D(d), 0FKS, 01ET, 01EQ, 01FJ.
(auxiliary; not a blueprint node)

Proof: cover Spec A minus V(I) by D(f_i) for the supplied generating list. Its
ordered intersections are the principal affine opens for the corresponding
products; sections of the structure sheaf are their specified localizations.
The structure module is quasi-coherent. Its higher cohomology on those affine
intersections vanishes. The prescribed Godement augmentation is a quasi-isomorphism
and its terms are flasque; restriction to an open preserves both properties.
The acyclic-resolution comparison therefore makes each section augmentation a
quasi-isomorphism. Apply finiteOrderedFlasqueCechComparison to get the natural
augmented roof between localization sections, the finite double total, and
Godement sections. Adjoin A as the first term to each arrow. Equivalently, take
mapping fibres of the augmented maps from A[0]. The identity on A and the two
quasi-isomorphisms on sections give quasi-isomorphisms on these fibres, by the
long exact cohomology sequence. The fibre of the localization augmentation has
exactly the displayed coordinates; negate successive positive-degree coordinates
as necessary to identify the mapping-cone signs with the displayed differential.
The projection in degree zero is the identity. Invert the roof in the derived
category. For r=0, the open complement is empty, all section terms are zero, and
the fibre is A[0]. Zero rings and zero or repeated generators obey the same formulas. -/
theorem ringComplex_godement_cech (A : CommRingCat.{u})
    [HasDerivedCategory.{w} (RingSiteModules A)] (I : {I : Ideal A // I.FG}) :
    RingComplexHasCechModel A I.val (ringComplexGodement A I.val)
      (ringComplexGodementAugmentation A I.val) := by
  intro r f hf
  let X := (ringComplexOpen A I.val).toScheme
  let F : X.Modules := SheafOfModules.unit (moduleRings X.toRingedSpace)
  let G := ringComplexGodementResolution X
  let e := ringComplexGodementUnit X
  let V := ringComplexPrincipalCover A I.val f
  have hm := (Scheme.Modules.moduleCup_godement_models_exist X F).choose_spec.choose_spec.1
  have : QuasiIso e := Scheme.Modules.moduleCup_godement_model_quasiIso X F
    (ringComplexGodementModel X) e hm
  have : G.IsStrictlyGE 0 := by
    unfold G ringComplexGodementResolution
    infer_instance
  obtain ⟨hα, β, _, hβ, hzero, _⟩ := finiteOrderedFlasqueCechComparison X F G e
    (godement_flasque X) r V (ringComplexPrincipalCover_iSup A I.val f hf)
    (ringComplexGodement_affineSections A I.val r f hf)
  let S := ringComplexSectionScalars A I.val
  have : (ringComplexConstant A).PreservesHomology := constant_preservesHomology A
  have : PreservesFiniteLimits (ringComplexConstant A) :=
    Functor.preservesFiniteLimits_of_preservesHomology _
  have : PreservesFiniteColimits (ringComplexConstant A) :=
    Functor.preservesFiniteColimits_of_preservesHomology _
  have : S.PreservesHomology := by
    unfold S ringComplexSectionScalars
    infer_instance
  let T := S.mapHomologicalComplex (.up ℤ)
  let α := alternatingCechAugmentationMap V G
  have : QuasiIso α := hα
  have : QuasiIso β := hβ
  have hsquare : ringComplexGodementRestriction A I.val ≫ T.map α =
      ringComplexOrderedCechRestriction A I.val f ≫ T.map β := by
    apply HomologicalComplex.from_single_hom_ext
    unfold ringComplexGodementRestriction ringComplexOrderedCechRestriction
    simp only [HomologicalComplex.comp_f, HomologicalComplex.mkHomFromSingle_f]
    change (_ ≫ (ringComplexStructureRestriction A I.val ≫ S.map _)) ≫ S.map (α.f 0) =
      (_ ≫ (ringComplexStructureRestriction A I.val ≫ S.map _)) ≫ S.map (β.f 0)
    simp only [Category.assoc, ← S.map_comp]
    apply congrArg (fun z ↦ _ ≫ (ringComplexStructureRestriction A I.val ≫ z))
    change S.map ((RingedSpace.globalSectionsFunctor X.toRingedSpace).map (e.f 0) ≫
      α.f 0) = S.map (alternatingCechZero V F ≫ β.f 0)
    exact congrArg S.map hzero
  obtain ⟨γ, hγ⟩ := fibre_roof_iso A (ringComplexGodementRestriction A I.val)
    (ringComplexOrderedCechRestriction A I.val f) (T.map α) (T.map β) hsquare
  obtain ⟨e₀, e', l, hneg, hd₀, hd, ha⟩ :=
    ringComplexOrderedCech_coordinates A I.val r f hf
  exact ⟨ringComplexOrderedCech A I.val f, ringComplexOrderedCechAugmentation A I.val f,
    e₀, e', l, hneg, hd₀, hd, ha, γ, hγ⟩

end
end AlgebraicGeometry
