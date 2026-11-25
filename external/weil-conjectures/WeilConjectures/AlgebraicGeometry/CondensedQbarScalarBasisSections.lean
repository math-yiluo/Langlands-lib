/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.CondensedQbarScalarBasisPushforward
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteSubextension
import WeilConjectures.AlgebraicGeometry.ProfinitePointPullback
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility

/-! Coherent coefficient sections for the algebraic closure.

This is the finite-support coordinate part of the scalar-basis construction. -/

@[expose] public section

universe u v w

open CategoryTheory Limits MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor

set_option backward.isDefEq.respectTransparency false

namespace CategoryTheory.Mod
open MonObj
variable {C : Type w} [Category.{v} C] [Abelian C] [MonoidalCategory C]
  [MonoidalPreadditive C] [SymmetricCategory C] [MonoidalClosed C]
  [IsGrothendieckAbelian.{v} C] [Abelian.HasFunctorialFlatResolution C]
  {R S : C} [MonObj R] [MonObj S] [IsCommMonObj R] [IsCommMonObj S]
  (φ : R ⟶ S) [IsMonHom φ]

private noncomputable def restrictExtendTensorIso (M : Mod C R) :
    (comap φ).obj ((extendScalars φ).obj M) ≅ ((comap φ).obj (regular S)) ⊗ M :=
  isoMk (extendForgetTensorObjIso φ M) (by
    dsimp only [extendForgetTensorObjIso]
    apply (cancel_epi (R ◁ extendπ φ M)).1
    change R ◁ extendπ φ M ≫ (φ ▷ _ ≫ γ[S,_]) ≫ _ = _
    simp only [Category.assoc]
    rw [whisker_exchange_assoc, whiskerLeft_extendπ_smul_assoc]
    rw [extendπ_extendDescHom]
    rw [← whiskerLeft_comp_assoc, extendπ_extendDescHom, whiskerLeft_tensorπ_smul]
    rw [associator_inv_naturality_left_assoc]
    change _ = (α_ R S M.X).inv ≫ (φ ▷ S ≫ μ[S]) ▷ M.X ≫
      tensorObjπ ((comap φ).obj (regular S)) M
    rw [comp_whiskerRight, Category.assoc])

omit [MonoidalPreadditive C] [Abelian.HasFunctorialFlatResolution C] in
private lemma extendUnit_qbar_scalarEndo (b : 𝟙_ C ⟶ S) (M : Mod C R) :
    extendUnitHom φ M ≫ (qbar_scalarEndo b ((extendScalars φ).obj M)).hom =
      (λ_ M.X).inv ≫ b ▷ M.X ≫ extendπ φ M := by
  rw [qbar_scalarEndo_hom]
  change extendUnitHom φ M ≫ (λ_ (extendScalarsObj φ M).X).inv ≫
    b ▷ (extendScalarsObj φ M).X ≫ γ[S,(extendScalarsObj φ M).X] = _
  rw [leftUnitor_inv_naturality_assoc]
  rw [whisker_exchange_assoc, whiskerLeft_extendUnitHom_smul']

omit [MonoidalPreadditive C] [Abelian.HasFunctorialFlatResolution C] in
private lemma extendUnit_qbar_scalarEndo_tensor (q : regular R ⟶ (comap φ).obj (regular S))
    (M : Mod C R) :
    extendUnit φ M ≫ (comap φ).map
        (qbar_scalarEndo (S := S) (η[R] ≫ q.hom) ((extendScalars φ).obj M)) ≫
        (restrictExtendTensorIso φ M).hom =
      (λ_ M).inv ≫ (q ▷ M) := by
  apply hom_ext
  simp only [comp_hom', comap_map_hom, extendUnit_hom]
  change extendUnitHom φ M ≫
    (qbar_scalarEndo (S := S) (η[R] ≫ q.hom) ((extendScalars φ).obj M)).hom ≫
    (extendForgetTensorObjIso φ M).hom = _
  rw [← Category.assoc, extendUnit_qbar_scalarEndo]
  simp only [extendForgetTensorObjIso, Category.assoc, extendπ_extendDescHom]
  rw [leftUnitor_inv_hom]
  simp only [Category.assoc]
  rw [tensorObjπ_whiskerRight, comp_whiskerRight]
  simp only [Category.assoc]

private noncomputable def copowerTensorIso {I : Type v} (M : Mod C R) [HasCoproduct (fun _ : I ↦ M)]
    (e : (∐ fun _ : I ↦ regular R) ≅ (comap φ).obj (regular S)) :
    (∐ fun _ : I ↦ M) ≅ ((comap φ).obj (regular S)) ⊗ M :=
  HasColimit.isoOfNatIso (Discrete.natIso
    (F := Discrete.functor (fun _ : I ↦ M))
    (G := Discrete.functor (fun _ : I ↦ (regular R) ⊗ M)) (fun _ ↦ (λ_ M).symm)) ≪≫
    (asIso (sigmaComparison (tensorRight M) (fun _ : I ↦ regular R))) ≪≫
    (tensorRight M).mapIso e

omit [MonoidalPreadditive C] [Abelian.HasFunctorialFlatResolution C] [IsCommMonObj S] in
private lemma copowerTensorIso_hom {I : Type v} (M : Mod C R) [HasCoproduct (fun _ : I ↦ M)]
    (e : (∐ fun _ : I ↦ regular R) ≅ (comap φ).obj (regular S)) :
    (copowerTensorIso φ M e).hom =
      Sigma.desc (fun i ↦ (λ_ M).inv ≫ ((Sigma.ι _ i ≫ e.hom) ▷ M)) := by
  have : HasColimitsOfShape (Discrete I) C :=
    (IsGrothendieckAbelian.hasColimits C).has_colimits_of_shape _
  have : HasColimitsOfShape (Discrete I) (Mod C R) :=
    hasColimitsOfShape_of_hasColimitsOfShape_createsColimitsOfShape (forget R)
  apply Sigma.hom_ext
  intro i
  simp only [copowerTensorIso, Iso.trans_hom, Sigma.ι_comp_desc,
    asIso_hom, Functor.mapIso_hom]
  rw [HasColimit.ι_isoOfNatIso_hom_assoc]
  change (λ_ M).inv ≫ Sigma.ι (fun _ : I ↦ (tensorRight M).obj (regular R)) i ≫
    sigmaComparison (tensorRight M) (fun _ : I ↦ regular R) ≫
      (tensorRight M).map e.hom = _
  rw [ι_comp_sigmaComparison_assoc]
  rw [← Functor.map_comp]
  rfl

omit [Abelian.HasFunctorialFlatResolution C] [MonoidalPreadditive C] in
private lemma isIso_copowerAdjUnitDesc {I : Type v} (M : Mod C R) [HasCoproduct (fun _ : I ↦ M)]
    (e : (∐ fun _ : I ↦ regular R) ≅ (comap φ).obj (regular S)) :
    IsIso (Sigma.desc (f := fun _ : I ↦ M) fun i : I ↦
      (extendRestrictAdjunction φ).unit.app M ≫ (comap φ).map
        (qbar_scalarEndo (S := S) (η[R] ≫ (Sigma.ι _ i ≫ e.hom).hom)
          ((extendScalars φ).obj M))) := by
  have : HasColimitsOfShape (Discrete I) C :=
    (IsGrothendieckAbelian.hasColimits C).has_colimits_of_shape _
  have : HasColimitsOfShape (Discrete I) (Mod C R) :=
    hasColimitsOfShape_of_hasColimitsOfShape_createsColimitsOfShape (forget R)
  have hu : (extendRestrictAdjunction φ).unit.app M = extendUnit φ M := by
    change extendUnit φ M ≫ (comap φ).map (𝟙 _) = _
    rw [CategoryTheory.Functor.map_id, Category.comp_id]
  rw [hu]
  let t := restrictExtendTensorIso φ M
  have h : (Sigma.desc (f := fun _ : I ↦ M) fun i : I ↦ extendUnit φ M ≫ (comap φ).map
      (qbar_scalarEndo (S := S) (η[R] ≫ (Sigma.ι _ i ≫ e.hom).hom)
        ((extendScalars φ).obj M))) ≫ t.hom = (copowerTensorIso φ M e).hom := by
    rw [copowerTensorIso_hom]
    apply Sigma.hom_ext
    intro i
    simp only [Sigma.ι_comp_desc_assoc, Sigma.ι_comp_desc]
    dsimp only [t]
    rw [Category.assoc]
    exact extendUnit_qbar_scalarEndo_tensor φ (Sigma.ι (fun _ : I ↦ regular R) i ≫ e.hom) M
  have hi : IsIso ((Sigma.desc (f := fun _ : I ↦ M) fun i : I ↦ extendUnit φ M ≫ (comap φ).map
      (qbar_scalarEndo (S := S) (η[R] ≫ (Sigma.ι _ i ≫ e.hom).hom)
        ((extendScalars φ).obj M))) ≫ t.hom) := by
    rw [h]
    infer_instance
  exact @IsIso.of_isIso_comp_right _ _ _ _ _ _ t.hom inferInstance hi

omit [Abelian.HasFunctorialFlatResolution C] in
private theorem exact_of_copower {I : Type v}
    (e : (∐ fun _ : I ↦ regular R) ≅ (comap φ).obj (regular S)) :
    PreservesFiniteLimits (extendScalars φ) := by
  have h : ObjectProperty.flat ((comap φ).obj (regular S)) :=
    ObjectProperty.prop_of_iso _ e
      (ObjectProperty.flat_coproduct (fun _ : I ↦ 𝟙_ (Mod C R))
        (fun _ ↦ ObjectProperty.flat_of_tensorIso (λ_ (𝟙_ (Mod C R)))))
  have : PreservesFiniteLimits (tensorLeft ((comap φ).obj (regular S))) := h.1.1
  have : PreservesFiniteLimits (extendScalars φ ⋙ forget S) :=
    preservesFiniteLimits_of_natIso (extendForgetTensorIso φ).symm
  exact preservesFiniteLimits_of_reflects_of_preserves (extendScalars φ) (forget S)

end CategoryTheory.Mod

namespace CategoryTheory.Mod
section MapCopower
open MonObj
variable {C : Type w} [Category.{v} C] [MonoidalCategory C]
  {D : Type*} [Category.{v} D] [MonoidalCategory D]
  (F : C ⥤ D) [F.LaxMonoidal]
  {R S : C} [MonObj R] [MonObj S]
  (a : R ⟶ S) [IsMonHom a]

private noncomputable def mapRegularIso :
    (F.mapMod R).obj (regular R) ≅ regular (F.obj R) :=
  isoMk (Iso.refl _) (by simp only [Iso.refl_hom, Category.comp_id,
    MonoidalCategory.whiskerLeft_id, Category.id_comp])

private noncomputable def mapRestrictedRegularIso :
    (F.mapMod R).obj ((comap a).obj (regular S)) ≅
      (comap (F.map a)).obj (regular (F.obj S)) :=
  (F.mapModComapIso a).app (regular S) ≪≫
    (comap (F.map a)).mapIso (mapRegularIso F)

variable {I : Type v} [HasCoproductsOfShape I (Mod C R)]
  [HasCoproductsOfShape I (Mod D (F.obj R))]
  [PreservesColimitsOfShape (Discrete I) (F.mapMod R)]

private noncomputable def mapCopowerIso
    (e : (∐ fun _ : I ↦ regular R) ≅ (comap a).obj (regular S)) :
    (∐ fun _ : I ↦ regular (F.obj R)) ≅ (comap (F.map a)).obj (regular (F.obj S)) :=
  Sigma.mapIso (fun _ ↦ (mapRegularIso F).symm) ≪≫
    asIso (sigmaComparison (F.mapMod R) (fun _ : I ↦ regular R)) ≪≫
    (F.mapMod R).mapIso e ≪≫ mapRestrictedRegularIso F a

private lemma mapCopowerVector
    (e : (∐ fun _ : I ↦ regular R) ≅ (comap a).obj (regular S)) (i : I) :
    η[F.obj R] ≫ (Sigma.ι _ i ≫ (mapCopowerIso F a e).hom).hom =
      Functor.LaxMonoidal.ε F ≫ F.map (η[R] ≫ (Sigma.ι _ i ≫ e.hom).hom) := by
  have hi : Sigma.ι _ i ≫
      (Sigma.mapIso (fun _ : I ↦ (mapRegularIso F (R := R)).symm)).hom ≫
        sigmaComparison (F.mapMod R) (fun _ : I ↦ regular R) =
      (mapRegularIso F).inv ≫ (F.mapMod R).map
        (Sigma.ι (fun _ : I ↦ regular R) i) := by
    rw [Sigma.ι_mapIso_hom_assoc]
    rw [ι_comp_sigmaComparison]
    rfl
  simp only [mapCopowerIso, Iso.trans_hom, asIso_hom, ← Category.assoc, hi]
  simp only [Functor.obj.η_def, Functor.mapMod_map, Category.assoc, comp_hom',
    homMk_hom, Functor.map_comp]
  change Functor.LaxMonoidal.ε F ≫ F.map η[R] ≫ 𝟙 (F.obj R) ≫
    F.map (Sigma.ι (fun _ : I ↦ regular R) i).hom ≫
      F.map e.hom.hom ≫ 𝟙 (F.obj S) ≫ 𝟙 (F.obj S) = _
  simp only [Category.id_comp, Category.comp_id]
  simp only [← Category.assoc]
  exact Category.comp_id _
end MapCopower
end CategoryTheory.Mod

private lemma monoidal_section_comparison
    {C D A : Type*} [Category C] [Category D] [Category A]
    [MonoidalCategory C] [MonoidalCategory D] [MonoidalCategory A]
    (F : C ⥤ D) (G : D ⥤ A) (H : C ⥤ A)
    [F.LaxMonoidal] [G.LaxMonoidal] [H.LaxMonoidal]
    (τ : F ⋙ G ⟶ H) [NatTrans.IsMonoidal τ] {S : C} (b : 𝟙_ C ⟶ S) :
    Functor.LaxMonoidal.ε H ≫ H.map b =
      Functor.LaxMonoidal.ε G ≫ G.map (Functor.LaxMonoidal.ε F ≫ F.map b) ≫ τ.app S := by
  rw [← NatTrans.IsMonoidal.unit (τ := τ)]
  rw [Category.assoc, ← τ.naturality b]
  simp only [Functor.LaxMonoidal.comp_ε, Functor.comp_map, Functor.map_comp,
    Category.assoc]

namespace AlgebraicGeometry.ProEtale
open MonObj

/-- Use an explicit section API so assembling the basis does not unfold the coefficient rings. -/
private noncomputable def pulledSection
    {S : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    (b : 𝟙_ (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) ⟶ S)
    (X : Scheme.{u}) : 𝟙_ (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) ⟶
      (upperStarFromPoint X).obj S :=
  Functor.LaxMonoidal.ε (upperStarFromPoint X) ≫ (upperStarFromPoint X).map b

private lemma pulled_section_coherence
    (S : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj S]
    (b : 𝟙_ (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) ⟶ S)
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    pulledSection b X = Functor.LaxMonoidal.ε (f)^*[Ab.{u + 1}] ≫
      (f)^*[Ab.{u + 1}].map (pulledSection b Y) ≫ condensedPullbackHom S f := by
  have : NatTrans.IsMonoidal (upperStarFromPointComp f).hom := by
    rcases profinite_point_pullback.{u} with
      ⟨_, _, _, _, _, _, _, _, _, _, _, _, hm⟩
    exact hm X Y f
  exact monoidal_section_comparison (upperStarFromPoint Y) (f)^*[Ab.{u + 1}]
    (upperStarFromPoint X) (upperStarFromPointComp f).hom b

end AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.ProEtale.CondensedRing
open MonObj

/-- Keep the ring objects abstract while transporting a point copower. This avoids reducing
concrete coefficient-ring constructions when checking the section-coherence equation. -/
private theorem scheme_basis_from_point
    (R S : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj R] [MonObj S] [IsCommMonObj R] [IsCommMonObj S]
    (a : R ⟶ S) [IsMonHom a] (I : Type (u + 1))
    [HasCoproducts.{u + 1} (Mod (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) R)]
    (e : (∐ fun _ : I ↦ Mod.regular R) ≅ (Mod.comap a).obj (Mod.regular S)) :
    ∃ (b : ∀ Z : Scheme.{u}, I →
        (𝟙_ (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) ⟶
          condensedRingObj S Z)),
      (∀ {X Y : Scheme.{u}} (f : X ⟶ Y) (i : I), b X i =
        Functor.LaxMonoidal.ε (f)^*[Ab.{u + 1}] ≫
          (f)^*[Ab.{u + 1}].map (b Y i) ≫
            condensedPullbackHom S f) ∧
      (∀ Z : Scheme.{u}, PreservesFiniteLimits (Mod.extendScalars (coefficientMap
        a Z))) ∧
      (∀ (Z : Scheme.{u})
        (N : Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
          (condensedRingObj R Z))
        [HasCoproduct (fun _ : I ↦ N)],
        IsIso (Sigma.desc (f := fun _ : I ↦ N) fun i ↦
          (Mod.extendRestrictAdjunction (coefficientMap
            a Z)).unit.app N ≫
          (Mod.comap (coefficientMap
            a Z)).map
            (Mod.qbar_scalarEndo (b Z i) ((Mod.extendScalars (coefficientMap
              a Z)).obj N)))) := by
  classical
  let : HasColimitsOfSize.{u + 1, u + 1}
      (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) :=
    IsGrothendieckAbelian.hasColimits _
  have hpoint : HasCoproducts.{u + 1}
      (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) :=
    fun J ↦ HasColimitsOfShape.of_small.{u + 1, u + 1} _ (Discrete J)
  have hF (Z : Scheme.{u}) : (upperStarFromPoint Z).IsLeftAdjoint :=
    (pointUpperStarLowerStarAdjunction.comp
      (ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} (toSpecZ Z))).isLeftAdjoint
  have hcol (Z : Scheme.{u}) : HasColimitsOfSize.{u + 1, u + 1}
      (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
        ((upperStarFromPoint Z).obj R)) := IsGrothendieckAbelian.hasColimits _
  have hcop (Z : Scheme.{u}) : HasCoproducts.{u + 1}
      (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
        ((upperStarFromPoint Z).obj R)) :=
    fun J ↦ HasColimitsOfShape.of_small.{u + 1, u + 1} _ (Discrete J)
  have hamb (Z : Scheme.{u}) : HasCoproducts.{u + 1}
      (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) := by
    let : HasColimitsOfSize.{u + 1, u + 1}
        (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) :=
      IsGrothendieckAbelian.hasColimits _
    exact fun J ↦ HasColimitsOfShape.of_small.{u + 1, u + 1} _ (Discrete J)
  have hFM (Z : Scheme.{u}) :
      PreservesColimitsOfShape (Discrete I) ((upperStarFromPoint Z).mapMod R) := by
    let F := upperStarFromPoint Z
    have : F.IsLeftAdjoint := hF Z
    have : PreservesColimitsOfShape (Discrete I) (F.mapMod R ⋙ Mod.forget (F.obj R)) :=
      inferInstanceAs (PreservesColimitsOfShape (Discrete I) (Mod.forget R ⋙ F))
    have : ReflectsColimitsOfShape (Discrete I)
        (Mod.forget (F.obj R) : Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) _ ⥤ _) :=
      reflectsColimitsOfShape_of_reflectsIsomorphisms
    exact preservesColimitsOfShape_of_reflects_of_preserves _ (Mod.forget (F.obj R))
  let eZ (Z : Scheme.{u}) := Mod.mapCopowerIso (upperStarFromPoint Z) a e
  let b₀ (i : I) : 𝟙_ (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) ⟶ S :=
    η[R] ≫ (Sigma.ι (fun _ : I ↦ Mod.regular R) i ≫ e.hom).hom
  let b (Z : Scheme.{u}) (i : I) :
      𝟙_ (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) ⟶ condensedRingObj S Z :=
    pulledSection (b₀ i) Z
  have hb (Z : Scheme.{u}) (i : I) :
      η[(upperStarFromPoint Z).obj R] ≫ (Sigma.ι _ i ≫ (eZ Z).hom).hom = b Z i :=
    Mod.mapCopowerVector (upperStarFromPoint Z) a e i
  refine ⟨b, ?_, ?_, ?_⟩
  · intro X Y f i
    exact pulled_section_coherence S (b₀ i) f
  · intro Z
    exact Mod.exact_of_copower (coefficientMap a Z) (eZ Z)
  · intro Z N hN
    simpa only [hb] using
      Mod.isIso_copowerAdjUnitDesc (coefficientMap a Z) N (eZ Z)

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)

/-- Coherent sections giving the ordinary scalar-extension copower, with exact extension.
Source: Compatibility.lean, `continuousBasisSheafIso`, `isIso_basisAdjUnitDesc`, and
`preservesFiniteLimits_extendScalars_of_flat`; FiniteSubextension.lean, the sectionwise
finite-subextension model.

Proof: choose a small algebraic `E`-basis of `PadicAlgCl ℓ`. A finite-subextension-valued
section has values in an `E`-span of finite dimension (take the compositum with `E`), so
only finitely many basis coordinates occur. Each coordinate is continuous: restrict it to
this finite-dimensional span and apply finite-dimensional linear topology over `ℚ_[ℓ]`.
Conversely a finite sum of continuous `E`-valued coordinates times basis vectors takes
values in a finite subextension and is continuous. These inverse maps, natural on profinite
sets, exhibit the restricted regular coefficient module as the basis-indexed coproduct of
regular `E`-modules. Pull this decomposition to `Z` using the colimit-preserving monoidal
point inverse image. Its monoidal composition comparison proves coherence of the pulled-back
basis sections. Tensoring the regular-module coproduct with `N` preserves it, and the
extension-unit/scalar-action calculation identifies its legs with the displayed maps.
The regular module is flat; coproducts of flat modules are flat. Thus the restricted
regular closure module is flat, and `extendForgetTensorIso`, with reflection by the exact
forgetful functor, proves the finite-limit-preservation clause. This construction is entirely
in ordinary internal modules; no derived unit decomposition is assumed.
(auxiliary; not a blueprint node) -/
theorem exists_condensedQbar_scalar_basis_sections :
    ∃ (I : Type (u + 1))
      (b : ∀ Z : Scheme.{u}, I →
        (𝟙_ (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) ⟶
          condensedRingObj (Profinite.padicAlgClRingObj ℓ) Z)),
      (∀ {X Y : Scheme.{u}} (f : X ⟶ Y) (i : I), b X i =
        Functor.LaxMonoidal.ε (f)^*[Ab.{u + 1}] ≫
          (f)^*[Ab.{u + 1}].map (b Y i) ≫
            condensedPullbackHom (Profinite.padicAlgClRingObj ℓ) f) ∧
      (∀ Z : Scheme.{u}, PreservesFiniteLimits (Mod.extendScalars (coefficientMap
        (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E) Z))) ∧
      (∀ (Z : Scheme.{u})
        (N : Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
          (condensedRingObj (Profinite.continuousMapRingObj E) Z))
        [HasCoproduct (fun _ : I ↦ N)],
        IsIso (Sigma.desc (f := fun _ : I ↦ N) fun i ↦
          (Mod.extendRestrictAdjunction (coefficientMap
            (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E) Z)).unit.app N ≫
          (Mod.comap (coefficientMap
            (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E) Z)).map
            (Mod.qbar_scalarEndo (b Z i) ((Mod.extendScalars (coefficientMap
              (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E) Z)).obj N)))) := by
  classical
  let : HasColimitsOfSize.{u + 1, u + 1}
      (Mod (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
        (Profinite.continuousMapRingObj E)) := IsGrothendieckAbelian.hasColimits _
  let : HasCoproducts.{u + 1}
      (Mod (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
        (Profinite.continuousMapRingObj E)) :=
    fun J ↦ HasColimitsOfShape.of_small.{u + 1, u + 1} _ (Discrete J)
  obtain ⟨I, ⟨e⟩⟩ := Profinite.exists_padicAlgCl_point_basis.{u} ℓ E
  obtain ⟨b, hb⟩ := scheme_basis_from_point _ _
    (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E) I e
  exact ⟨I, b, hb⟩

end AlgebraicGeometry.ProEtale.CondensedRing
