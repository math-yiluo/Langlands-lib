/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SymmetricAlgebraSheaf.CanonicalSymmetricGradedAlgebra
public import WeilConjectures.AlgebraicGeometry.Tensor.TensorPullbackSectionAdjunction
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import Mathlib.AlgebraicGeometry.Fiber
import WeilConjectures.AlgebraicGeometry.ProjectiveBundlePicardClassification.ProjectiveBundleFiberGeometry
import WeilConjectures.AlgebraicGeometry.Picard.H1.PicardH1LocalSectionBaseDescentGenerator
import WeilConjectures.AlgebraicGeometry.Proper.Flat.ProperFlatGlobalSections
import WeilConjectures.AlgebraicGeometry.Projective.ProjectiveBundleProper
import WeilConjectures.AlgebraicGeometry.Modules.Dual
import WeilConjectures.AlgebraicGeometry.ModulePullbackTensor

/-!
# Lifting a fibre isomorphism as a morphism near the base point
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u
open CategoryTheory MonoidalCategory
namespace AlgebraicGeometry.ProjectiveBundlePicardClassification
open Scheme.Modules

private noncomputable def ordinaryPullbackComparison {X Y : Scheme.{u}} (g : X ⟶ Y) :
    tensorPullback g ≅ pullback g :=
  (tensorPullbackSectionAdjunction g).leftAdjointUniq (pullbackPushforwardAdjunction g)

private noncomputable def tensorUnitComparison {X Y : Scheme.{u}} (g : X ⟶ Y) :
    (tensorPullback g).obj (𝟙_ Y.Modules) ≅ 𝟙_ X.Modules :=
  (ordinaryPullbackComparison g).app _ ≪≫ pullbackObjUnitIso g

-- Retain the unit in the conclusion of the proper shrinking argument. The general
-- pullback-locus theorem only exposes an unspecified finite locally free base module.
private theorem trivial_near_fiber_generator {X S : Scheme.{u}} (f : X ⟶ S)
    [IsProper f] (L : X.Modules) [L.IsInvertible]
    {W : Scheme.{u}} (k : W ⟶ S) (w : W)
    (σ : Γ((tensorPullback (Limits.pullback.fst f k)).obj L, ⊤))
    (hσ : ∀ x : (Limits.pullback f k : Scheme.{u}),
      (Limits.pullback.snd f k) x = w → GeneratesAt σ x) :
    ∃ V : W.Opens, w ∈ V ∧ ∀ {T : Scheme.{u}} (h : T ⟶ W), Set.range h ⊆ V →
      Nonempty ((tensorPullback (Limits.pullback.fst f (h ≫ k))).obj L ≅
        𝟙_ (Limits.pullback f (h ≫ k)).Modules) := by
  classical
  let Y : Scheme.{u} := Limits.pullback f k
  let p : Y ⟶ W := Limits.pullback.snd f k
  let M : Y.Modules := (tensorPullback (Limits.pullback.fst f k)).obj L
  have : M.IsInvertible :=
    IsInvertible.of_iso ((ordinaryPullbackComparison _).app L).symm
  let D := generatingLocus σ
  let V : W.Opens := ⟨(p '' (D : Set Y)ᶜ)ᶜ,
    (p.isClosedMap _ D.isOpen.isClosed_compl).isOpen_compl⟩
  have hwV : w ∈ V := by
    rintro ⟨x, hx, hpw⟩
    exact hx (hσ x hpw)
  refine ⟨V, hwV, ?_⟩
  intro T h hh
  let q : Limits.pullback f (h ≫ k) ⟶ Y :=
    Limits.pullback.lift (Limits.pullback.fst f (h ≫ k))
      (Limits.pullback.snd f (h ≫ k) ≫ h)
      (by simp only [Category.assoc, Limits.pullback.condition])
  have hqfst : q ≫ Limits.pullback.fst f k = Limits.pullback.fst f (h ≫ k) := by
    simp [q]
  have hqsnd : q ≫ p = Limits.pullback.snd f (h ≫ k) ≫ h := by
    simp [q, p]
  have hqD (x : (Limits.pullback f (h ≫ k) : Scheme.{u})) : q x ∈ D := by
    by_contra hx
    have hxV := hh ⟨(Limits.pullback.snd f (h ≫ k)) x, rfl⟩
    apply hxV
    refine ⟨q x, hx, ?_⟩
    change (q ≫ p) x = _
    rw [hqsnd]
    rfl
  have hqtop : q ⁻¹ᵁ D = ⊤ := by
    exact eq_top_iff.mpr (fun x _ ↦ hqD x)
  obtain ⟨τ, hτ⟩ : ∃ τ : Γ((pullback q).obj M, ⊤), IsFreeGenerator τ := by
    have hgen := (isFreeGenerator_generatingLocus σ).pullback_unit_app q
    exact ⟨_, hgen.map hqtop.ge⟩
  have := isIso_homOfGlobalSection hτ
  let eR : (tensorPullback q).obj M ≅ 𝟙_ (Limits.pullback f (h ≫ k)).Modules :=
    (ordinaryPullbackComparison q).app M ≪≫
      (asIso (homOfGlobalSection _ τ)).symm
  let eL : (tensorPullback (Limits.pullback.fst f (h ≫ k))).obj L ≅
      (tensorPullback q).obj M :=
    (eqToIso (congrArg (fun g ↦ (tensorPullback g).obj L) hqfst.symm)) ≪≫
      (tensorPullbackSectionComp q (Limits.pullback.fst f k)).app L
  exact ⟨eL ≪≫ eR⟩

private noncomputable def cancelLine {X : Scheme.{u}} (M N : X.Modules)
    [M.IsInvertible] : M ⊗ (Mᵛ ⊗ N) ≅ N :=
  (α_ M Mᵛ N).symm ≪≫ (asIso (dualEvaluation M) ⊗ᵢ Iso.refl N) ≪≫ λ_ N

/-- A fibre isomorphism of lines lifts as a sheaf morphism above some base open,
whose pullback to the fibre is invertible.

EGA II, Remark 4.2.7 announces the projective-bundle classification.
-/
theorem projective_bundle_fiber_hom_lift (S : Scheme.{u}) (E : S.Modules)
    [E.IsQuasicoherent] (r : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E r] (hr : 2 ≤ r)
    (M N : (SymmetricAlgebraSheaf.gradedAlgebraData E).relProj.Modules)
    (hM : M.IsInvertible) (hN : N.IsInvertible) (s : S)
    (e : Nonempty
      ((tensorPullback
        ((SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom.fiberι s)).obj M ≅
        (tensorPullback
          ((SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom.fiberι s)).obj N)) :
    ∃ (U : S.Opens) (hs : s ∈ U)
      (φ : (tensorPullback
        ((SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom ⁻¹ᵁ U).ι).obj M ⟶
        (tensorPullback
          ((SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom ⁻¹ᵁ U).ι).obj N),
      IsIso ((tensorPullback
        (((SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom ∣_ U).fiberι
          (⟨s, hs⟩ : U.toScheme))).map φ) := by
  classical
  let p := (SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom
  have : M.IsInvertible := hM
  have : N.IsInvertible := hN
  have hfinite :=
    SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree.{u, u, u} E r
  obtain ⟨q, hq, hqfin⟩ := hfinite.exists_localGeneratorsData
  have : SheafOfModules.IsFiniteType.{u, u, u} E := by
    constructor
    exact ⟨q, hqfin⟩
  have : IsProper p := projectiveBundle_proper p
    ⟨E, inferInstance, inferInstance, 𝟙 _, inferInstance, Category.id_comp _⟩
  obtain ⟨hflat, hfp, hfib⟩ := projective_bundle_fiber_geometry S E r (by omega)
  let := hflat
  let := hfp
  have hO : ∀ {T : Scheme.{u}} (g : T ⟶ S),
      IsIso ((Classical.choose
        (exists_tensorPullbackAdjunction (Limits.pullback.snd p g))).unit.app
          (SheafOfModules.unit T.ringCatSheaf)) :=
    (isIso_structureSheafMap_of_proper_flat_geometricallyReduced_connected_fibers
      p (fun t ↦ (hfib t).1) (fun t ↦ (hfib t).2.1)).2
  let L := Mᵛ ⊗ N
  have : L.IsInvertible := inferInstance
  obtain ⟨es⟩ := e
  obtain ⟨et, _, _⟩ := module_pullback_tensor (p.fiberι s)
  let ev : (tensorPullback (p.fiberι s)).obj M ⊗
      (tensorPullback (p.fiberι s)).obj Mᵛ ≅ 𝟙_ (p.fiber s).Modules :=
    (et M Mᵛ).symm ≪≫ (tensorPullback (p.fiberι s)).mapIso (asIso (dualEvaluation M)) ≪≫
      tensorUnitComparison _
  let eLs : (tensorPullback (p.fiberι s)).obj L ≅ 𝟙_ (p.fiber s).Modules :=
    et Mᵛ N ≪≫ (Iso.refl _ ⊗ᵢ es.symm) ≪≫ β_ _ _ ≪≫ ev
  let Xi : Fin 0 → Scheme.{u} := fun i ↦ Fin.elim0 i
  let fi : ∀ i, Xi i ⟶ S := fun i ↦ Fin.elim0 i
  let ui : ∀ i, Xi i ⟶ (SymmetricAlgebraSheaf.gradedAlgebraData E).relProj :=
    fun i ↦ Fin.elim0 i
  have hui : ∀ i, ui i ≫ p = fi i := fun i ↦ Fin.elim0 i
  have : ∀ i, Flat (fi i) := fun i ↦ Fin.elim0 i
  have : ∀ i, IsProper (fi i) := fun i ↦ Fin.elim0 i
  have : ∀ i, LocallyOfFinitePresentation (fi i) := fun i ↦ Fin.elim0 i
  have hOi : ∀ i, ∀ {T : Scheme.{u}} (g : T ⟶ S),
      IsIso ((Classical.choose
        (exists_tensorPullbackAdjunction (Limits.pullback.snd (fi i) g))).unit.app
          (SheafOfModules.unit T.ringCatSheaf)) := fun i ↦ Fin.elim0 i
  have hLi : ∀ i, ∃ (A : S.Modules) (_ : A.IsFiniteLocallyFree),
      Nonempty ((tensorPullback (Limits.pullback.fst (fi i) (𝟙 S))).obj
        ((tensorPullback (ui i)).obj L) ≅
        (tensorPullback (Limits.pullback.snd (fi i) (𝟙 S))).obj A) :=
    fun i ↦ Fin.elim0 i
  have : SheafOfModules.IsInvertible.{u, u, u}
      (𝟙_ (Spec (S.residueField s)).Modules) :=
    IsInvertible.sheafOfModules_isInvertible _
  have hLs : ∃ (A : (Spec (S.residueField s)).Modules) (_ : A.IsFiniteLocallyFree),
      Nonempty ((tensorPullback (Limits.pullback.fst p (S.fromSpecResidueField s))).obj L ≅
        (tensorPullback (Limits.pullback.snd p (S.fromSpecResidueField s))).obj A) :=
    ⟨SheafOfModules.unit _,
      SheafOfModules.IsInvertible.isFiniteLocallyFree.{u, u, u} _,
      ⟨eLs ≪≫ (tensorUnitComparison _).symm⟩⟩
  have hH : Subsingleton (Sheaf.H (Scheme.structureSheafAb
      (Limits.pullback p (S.fromSpecResidueField s))) 1) := (hfib s).2.2
  obtain ⟨V, hsV, σ, hσ⟩ := Scheme.picard_h1_local_section_of_base_descent_generator
    p Xi fi ui hui hO hOi L S (𝟙 S) s s rfl hLi hLs
      (fun x y _ ↦ hH.elim x y)
  obtain ⟨W, hsW, hW⟩ := trivial_near_fiber_generator p L (V.ι ≫ 𝟙 S)
    (⟨s, hsV⟩ : V.toScheme) σ hσ
  let U := V.ι ''ᵁ W
  have hUV : U ≤ V := V.ι_image_le W
  let h : U.toScheme ⟶ V.toScheme := S.homOfLE hUV
  have hh : Set.range h ⊆ W := by
    rintro _ ⟨x, rfl⟩
    apply (Scheme.Opens.mem_ι_image_iff V).mp
    simpa only [h, Scheme.homOfLE_apply] using x.property
  obtain ⟨eL⟩ := hW h hh
  have hhcomp : h ≫ (V.ι ≫ 𝟙 S) = U.ι := by
    simp only [Category.comp_id, h, Scheme.homOfLE_ι]
  rw [hhcomp] at eL
  let a := pullbackRestrictIsoRestrict p U
  have ha : a.inv ≫ Limits.pullback.fst p U.ι = (p ⁻¹ᵁ U).ι :=
    pullbackRestrictIsoRestrict_inv_fst p U
  let d : (tensorPullback (p ⁻¹ᵁ U).ι).obj L ≅
      𝟙_ (p ⁻¹ᵁ U).toScheme.Modules :=
    (ordinaryPullbackComparison _).app L ≪≫ (pullbackCongr ha.symm).app L ≪≫
      (pullbackComp a.inv _).symm.app L ≪≫
      (pullback a.inv).mapIso ((ordinaryPullbackComparison _).symm.app L ≪≫ eL) ≪≫
      pullbackObjUnitIso a.inv
  let F := pullback (p ⁻¹ᵁ U).ι
  let d' : F.obj L ≅ 𝟙_ (p ⁻¹ᵁ U).toScheme.Modules :=
    (ordinaryPullbackComparison _).symm.app L ≪≫ d
  let t : F.obj M ≅ F.obj N :=
    (ρ_ _).symm ≪≫ (Iso.refl _ ⊗ᵢ d'.symm) ≪≫
      Functor.Monoidal.μIso F M L ≪≫ F.mapIso (cancelLine M N)
  let t' : (tensorPullback (p ⁻¹ᵁ U).ι).obj M ≅
      (tensorPullback (p ⁻¹ᵁ U).ι).obj N :=
    (ordinaryPullbackComparison _).app M ≪≫ t ≪≫
      (ordinaryPullbackComparison _).symm.app N
  exact ⟨U, ⟨⟨s, hsV⟩, hsW, rfl⟩, t'.hom, inferInstance⟩

end AlgebraicGeometry.ProjectiveBundlePicardClassification
