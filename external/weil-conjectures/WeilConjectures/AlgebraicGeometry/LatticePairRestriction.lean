/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
import WeilConjectures.AlgebraicGeometry.StrictPerfectPackageOnSite
public import WeilConjectures.AlgebraicGeometry.LatticeSheafBasic
import Mathlib.CategoryTheory.Sites.PreservesLocallyBijective

/-!
# Restriction of integral lattice pairs

Source: Bhatt--Scholze, Proposition 6.8.4(6), pp. 59–60.
(auxiliary; not a blueprint node).
-/

@[expose] public section

attribute [local instance] AlgebraicGeometry.ProEtale.latticeWeakSheafifyOver
  AlgebraicGeometry.Scheme.strictPerfectSliceLocallyBijective
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped ChangeOfRings
namespace AlgebraicGeometry.ProEtale
/-- Cache the existing strong additive sheafification instance on a slice.
Source: Mathlib, sheafification on small sites.
(auxiliary; not a blueprint node).
Proof: specialize the existing instance. -/
local instance restrictionStrongSheafifyOver (X : Scheme.{u}) (U : X.ProEt) :
    HasSheafify ((Scheme.ProEt.topology X).over U) AddCommGrpCat.{u + 1} := by
  infer_instance

/-- Cache additive sheafification on an iterated slice.
Source: Mathlib, sheafification on small sites.
(auxiliary; not a blueprint node).
Proof: specialize the existing instance. -/
local instance restrictionWeakSheafifyOverOver (X : Scheme.{u}) (U : X.ProEt) (T : Over U) :
    HasWeakSheafify (((Scheme.ProEt.topology X).over U).over T) AddCommGrpCat.{u + 1} := by
  infer_instance

/-- Cache the local bijectivity criterion on an iterated slice.
Source: Mathlib, sheafification on small sites.
(auxiliary; not a blueprint node).
Proof: specialize the existing instance. -/
local instance restrictionWEqualsOverOver (X : Scheme.{u}) (U : X.ProEt) (T : Over U) :
    (((Scheme.ProEt.topology X).over U).over T).WEqualsLocallyBijective
      AddCommGrpCat.{u + 1} := by
  infer_instance

/-- Cache strong additive sheafification on an iterated slice.
Source: Mathlib, sheafification on small sites.
(auxiliary; not a blueprint node).
Proof: specialize the existing instance. -/
local instance restrictionStrongSheafifyOverOver (X : Scheme.{u}) (U : X.ProEt) (T : Over U) :
    HasSheafify (((Scheme.ProEt.topology X).over U).over T) AddCommGrpCat.{u + 1} := by
  infer_instance
set_option backward.isDefEq.respectTransparency false
variable {X : Scheme.{u}}
  {R S : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}} (a : R ⟶ S)
  {U V : X.ProEt} (f : V ⟶ U)
set_option hygiene false in
local notation "𝓡" => (sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R
set_option hygiene false in
local notation "𝓢" => (sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S
variable (M : SheafOfModules.{u + 1} ((𝓡).over U))
noncomputable def restrictedTensorUnit :
    SheafOfModules.changeOfRingsPresheaf.{u, u + 1, u + 1}
      (latticeScalarMap a V) ((SheafOfModules.overMap 𝓡 f).obj M) ⟶
    ((SheafOfModules.overMap 𝓢 f).obj
      (SheafOfModules.changeOfRings.{u, u + 1, u + 1} (latticeScalarMap a U) M)).val where
  app T := ((PresheafOfModules.sheafificationAdjunction
    (𝟙 ((𝓢).over U).obj)).unit.app
      (SheafOfModules.changeOfRingsPresheaf.{u, u + 1, u + 1}
        (latticeScalarMap a U) M)).app ((Over.map f).op.obj T)
  naturality := by
    intro T T' g
    apply ModuleCat.ExtendScalars.hom_ext
    intro m
    let η := (PresheafOfModules.sheafificationAdjunction
      (𝟙 ((𝓢).over U).obj)).unit.app
        (SheafOfModules.changeOfRingsPresheaf.{u, u + 1, u + 1}
          (latticeScalarMap a U) M)
    have hn := PresheafOfModules.naturality_apply η ((Over.map f).op.map g)
      ((1 : (S.over V).obj.obj T) ⊗ₜ[(R.over V).obj.obj T,
        ((latticeScalarMap a V).hom.app T).hom] m)
    have hV := Classical.choose_spec
      (SheafOfModules.exists_changeOfRingsMap.{u, u + 1, u + 1}
        (latticeScalarMap a V) ((SheafOfModules.overMap 𝓡 f).obj M) g)
      (1 : (S.over V).obj.obj T) m
    have hU := Classical.choose_spec
      (SheafOfModules.exists_changeOfRingsMap.{u, u + 1, u + 1}
        (latticeScalarMap a U) M ((Over.map f).op.map g))
      (1 : (S.over V).obj.obj T) m
    change SheafOfModules.changeOfRingsMap.{u, u + 1, u + 1}
      (latticeScalarMap a V) ((SheafOfModules.overMap 𝓡 f).obj M) g _ = _ at hV
    change SheafOfModules.changeOfRingsMap.{u, u + 1, u + 1}
      (latticeScalarMap a U) M ((Over.map f).op.map g) _ = _ at hU
    change η.app ((Over.map f).op.obj T')
      (SheafOfModules.changeOfRingsMap.{u, u + 1, u + 1}
        (latticeScalarMap a V) ((SheafOfModules.overMap 𝓡 f).obj M) g _) = _
    change η.app ((Over.map f).op.obj T')
      (SheafOfModules.changeOfRingsMap.{u, u + 1, u + 1}
        (latticeScalarMap a U) M ((Over.map f).op.map g) _) = _ at hn
    rw [hV, map_one]
    rw [map_one] at hU
    exact (congrArg (η.app ((Over.map f).op.obj T')) hU.symm).trans hn
noncomputable def restrictedTensorComparison :
    SheafOfModules.changeOfRings.{u, u + 1, u + 1}
      (latticeScalarMap a V) ((SheafOfModules.overMap 𝓡 f).obj M) ⟶
    (SheafOfModules.overMap 𝓢 f).obj
      (SheafOfModules.changeOfRings.{u, u + 1, u + 1} (latticeScalarMap a U) M) :=
  (PresheafOfModules.sheafificationHomEquiv (𝟙 ((𝓢).over V).obj)).symm
    (restrictedTensorUnit a f M)

theorem restrictedTensorComparison_spec :
    PresheafOfModules.sheafificationHomEquiv (𝟙 ((𝓢).over V).obj)
      (restrictedTensorComparison a f M) = restrictedTensorUnit a f M :=
  (PresheafOfModules.sheafificationHomEquiv (𝟙 ((𝓢).over V).obj)
    (P := SheafOfModules.changeOfRingsPresheaf.{u, u + 1, u + 1}
      (latticeScalarMap a V) ((SheafOfModules.overMap 𝓡 f).obj M))
    (F := (SheafOfModules.overMap 𝓢 f).obj
      (SheafOfModules.changeOfRings.{u, u + 1, u + 1} (latticeScalarMap a U) M))).apply_symm_apply _

attribute [irreducible] restrictedTensorComparison

theorem restrictedTensorUnit_presheaf :
    (PresheafOfModules.toPresheaf _).map (restrictedTensorUnit a f M) =
      Functor.whiskerLeft (Over.map f).op (toSheafify
        ((Scheme.ProEt.topology X).over U)
        (SheafOfModules.changeOfRingsPresheaf.{u, u + 1, u + 1}
          (latticeScalarMap a U) M).presheaf) := rfl

theorem restrictedTensorComparison_app_unit (T : (Over V)ᵒᵖ)
    (z : (SheafOfModules.changeOfRingsPresheaf.{u, u + 1, u + 1}
      (latticeScalarMap a V) ((SheafOfModules.overMap 𝓡 f).obj M)).obj T) :
    (restrictedTensorComparison a f M).val.app T
      (((PresheafOfModules.sheafificationAdjunction
        (𝟙 ((𝓢).over V).obj)).unit.app
        (SheafOfModules.changeOfRingsPresheaf.{u, u + 1, u + 1}
          (latticeScalarMap a V) ((SheafOfModules.overMap 𝓡 f).obj M))).app T z) =
      ((PresheafOfModules.sheafificationAdjunction
        (𝟙 ((𝓢).over U).obj)).unit.app
        (SheafOfModules.changeOfRingsPresheaf.{u, u + 1, u + 1}
          (latticeScalarMap a U) M)).app ((Over.map f).op.obj T) z := by
  have h := congrArg (fun e ↦ e.app T z) (restrictedTensorComparison_spec a f M)
  exact h

attribute [irreducible] restrictedTensorUnit

instance restrictedTensorUnit_injective :
    PresheafOfModules.IsLocallyInjective ((Scheme.ProEt.topology X).over V)
      (restrictedTensorUnit a f M) := by
  unfold PresheafOfModules.IsLocallyInjective
  rw [restrictedTensorUnit_presheaf]
  exact Presheaf.isLocallyInjective_whisker _ ((Scheme.ProEt.topology X).over U)
    (Over.map f) _

instance restrictedTensorUnit_surjective :
    PresheafOfModules.IsLocallySurjective ((Scheme.ProEt.topology X).over V)
      (restrictedTensorUnit a f M) := by
  unfold PresheafOfModules.IsLocallySurjective
  rw [restrictedTensorUnit_presheaf]
  exact Presheaf.isLocallySurjective_whisker _ ((Scheme.ProEt.topology X).over U)
    (Over.map f) _

instance restrictedTensorComparison_isIso : IsIso (restrictedTensorComparison a f M) := by
  let N := SheafOfModules.changeOfRingsPresheaf.{u, u + 1, u + 1}
    (latticeScalarMap a V) ((SheafOfModules.overMap 𝓡 f).obj M)
  let g := (PresheafOfModules.toPresheaf _).map (restrictedTensorUnit a f M)
  let e := (PresheafOfModules.toPresheaf _).map
    (restrictedTensorComparison a f M).val
  have he : toSheafify ((Scheme.ProEt.topology X).over V) N.presheaf ≫ e = g := by
    have h := congrArg ((PresheafOfModules.toPresheaf _).map)
      (restrictedTensorComparison_spec a f M)
    rw [PresheafOfModules.toPresheaf_map_sheafificationHomEquiv_def] at h
    exact h
  have hi : Presheaf.IsLocallyInjective ((Scheme.ProEt.topology X).over V) e := by
    rw [← Presheaf.comp_isLocallyInjective_iff _ (toSheafify _ N.presheaf), he]
    exact restrictedTensorUnit_injective a f M
  have hs : Presheaf.IsLocallySurjective ((Scheme.ProEt.topology X).over V) e := by
    rw [← Presheaf.comp_isLocallySurjective_iff _ (toSheafify _ N.presheaf), he]
    exact restrictedTensorUnit_surjective a f M
  have : IsIso ((SheafOfModules.toSheaf _).map
      (restrictedTensorComparison a f M)) :=
    (Sheaf.isLocallyBijective_iff_isIso _).mp ⟨hi, hs⟩
  exact isIso_of_reflects_iso (restrictedTensorComparison a f M) (SheafOfModules.toSheaf _)

theorem postOverMap_continuous {C : Type*} [Category* C]
    (J : GrothendieckTopology C) {U V : C} (f : V ⟶ U) (W : Over V) :
    (Over.post (X := W) (Over.map f)).IsContinuous
      ((J.over V).over W)
      ((J.over U).over ((Over.map f).obj W)) := by
  let H' := W.iteratedSliceForward ⋙ ((Over.map f).obj W).iteratedSliceBackward
  have : ((Over.map f).obj W).iteratedSliceBackward.IsContinuous
      (J.over W.left)
      ((J.over U).over ((Over.map f).obj W)) :=
    inferInstanceAs (((Over.map f).obj W).iteratedSliceBackward.IsContinuous
      (J.over ((Over.map f).obj W).left) _)
  have : H'.IsContinuous ((J.over V).over W)
      ((J.over U).over ((Over.map f).obj W)) :=
    Functor.isContinuous_comp _ _ _ (J.over W.left) _
  let e : H' ≅ Over.post (X := W) (Over.map f) :=
    NatIso.ofComponents
      (fun T ↦ Over.isoMk (Over.isoMk (Iso.refl _) (by
        change (𝟙 _) ≫ (T.left.hom ≫ f) = T.hom.left ≫ (W.hom ≫ f)
        simpa only [Category.id_comp] using (Over.w_assoc T.hom f).symm)) (by
          ext
          change (𝟙 _) ≫ T.hom.left = T.hom.left
          exact Category.id_comp _))
      (by
        intro T T' g
        ext
        change g.left.left ≫ 𝟙 _ = 𝟙 _ ≫ g.left.left
        rw [Category.comp_id, Category.id_comp])
  exact Functor.isContinuous_of_iso e _ _

theorem finiteLocallyFree_overMap
    (R : Sheaf (Scheme.ProEt.topology X) RingCat.{u + 1})
    {U V : X.ProEt} (f : V ⟶ U)
    (M : SheafOfModules.{u + 1} (R.over U)) [hM : M.IsFiniteLocallyFree] :
    ((SheafOfModules.overMap R f).obj M).IsFiniteLocallyFree := by
  classical
  obtain ⟨q, hq, hf⟩ := hM.exists_localGeneratorsData
  let := hq
  let := hf
  let I := Σ i : q.I, Σ W : Over V, ((Over.map f).obj W ⟶ q.X i)
  let W : I → Over V := fun i ↦ i.2.1
  have hW : ((Scheme.ProEt.topology X).over V).CoversTop W := by
    intro T
    apply ((Scheme.ProEt.topology X).over V).superset_covering _
      ((Over.map f).cover_lift _ _ (q.coversTop ((Over.map f).obj T)))
    intro T' g hg
    obtain ⟨i, ⟨t⟩⟩ := hg
    exact ⟨⟨i, T', t⟩, ⟨𝟙 T'⟩⟩
  let κ (i : I) := (q.generators i.1).I
  have (i : I) : Finite (κ i) :=
    let := hf.isFiniteType i.1
    inferInstance
  apply SheafOfModules.isFiniteLocallyFree_of_exists_over_iso_free W hW κ
  intro i
  let H := Over.post (X := W i) (Over.map f) ⋙ Over.map i.2.2
  have := postOverMap_continuous (Scheme.ProEt.topology X) f (W i)
  have : H.IsContinuous (((Scheme.ProEt.topology X).over V).over (W i))
      (((Scheme.ProEt.topology X).over U).over (q.X i.1)) :=
    Functor.isContinuous_comp _ _ _
      (((Scheme.ProEt.topology X).over U).over ((Over.map f).obj (W i))) _
  have : H.IsCocontinuous (((Scheme.ProEt.topology X).over V).over (W i))
      (((Scheme.ProEt.topology X).over U).over (q.X i.1)) := by
    exact isCocontinuous_comp _ _
      (((Scheme.ProEt.topology X).over V).over (W i))
      (((Scheme.ProEt.topology X).over U).over ((Over.map f).obj (W i)))
  have : H.IsLeftAdjoint := by
    dsimp [H]
    infer_instance
  let F : SheafOfModules.{u + 1} ((R.over U).over (q.X i.1)) ⥤
      SheafOfModules.{u + 1} ((R.over V).over (W i)) :=
    SheafOfModules.pushforward (F := H) (𝟙 _)
  have h : F.obj (M.over (q.X i.1)) ≅
      ((SheafOfModules.overMap R f).obj M).over (W i) := Iso.refl _
  exact ⟨h.symm ≪≫ F.mapIso (asIso (q.generators i.1).π).symm ≪≫
    (SheafOfModules.mapFreeIso F (κ i) (Iso.refl _)).symm⟩

/-- Restriction of a lattice pair, using the tensor comparison on slice sites. -/
noncomputable def IntegralLatticePair.restrict
    {L : SheafOfModules.{u + 1} 𝓢} (P : IntegralLatticePair a L U) :
    IntegralLatticePair a L V where
  module := (SheafOfModules.overMap 𝓡 f).obj P.module
  locallyFree := by
    let := P.locallyFree
    exact finiteLocallyFree_overMap 𝓡 f P.module
  rationalization := asIso (restrictedTensorComparison a f P.module) ≪≫
    (SheafOfModules.overMap 𝓢 f).mapIso P.rationalization ≪≫
    (SheafOfModules.overFunctorMap 𝓢 f).app L

/-- Images of restricted pairs are the original images on the smaller slice.
Source: Bhatt--Scholze, Proposition 6.8.4(6), descent of embedded lattices.
(auxiliary; not a blueprint node).
Proof: the slice tensor comparison sends each sheafified unit tensor to the
same unit tensor on the original slice. Applying the original rationalization
therefore gives the same section, so the two maps have equal ranges. -/
theorem IntegralLatticePair.restrict_image
    {L : SheafOfModules.{u + 1} 𝓢} (P : IntegralLatticePair a L U)
    (T : (Over V)ᵒᵖ) :
    (P.restrict a f).image T = P.image ((Over.map f).op.obj T) := by
  apply congrArg Set.range
  funext m
  change P.rationalization.hom.val.app ((Over.map f).op.obj T)
    ((restrictedTensorComparison a f P.module).val.app T _) = _
  apply congrArg (P.rationalization.hom.val.app ((Over.map f).op.obj T))
  exact restrictedTensorComparison_app_unit a f P.module T _

end AlgebraicGeometry.ProEtale
