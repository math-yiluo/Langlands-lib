/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Vector.VectorIntegrationCartesianPrefix

/-! # Linear change between restricted inverse frames

Source: blueprint vector integration, overlap calculation, geometric part.
(blueprint: lem-amb-vector-integration-overlap-coordinates).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Etale

open Opposite VectorBundleZeroSection

private theorem tower_iso_over (T : Scheme.{u}) (d : ℕ) :
    (affineTraceAffineSpaceIso T d).inv ≫ affineTraceProjection T d =
      AffineSpace (ULift.{u} (Fin d)) T ↘ T := by
  apply (cancel_epi (affineTraceAffineSpaceIso T d).hom).mp
  simp only [Iso.hom_inv_id_assoc]
  exact (AffineSpace.homOfVector_over _ _).symm

private theorem tower_iso_coord (T : Scheme.{u}) (d : ℕ) (j : Fin d) :
    (affineTraceAffineSpaceIso T d).hom.appTop (AffineSpace.coord T (ULift.up j)) =
      affineTraceCoordinate T d j := by
  exact AffineSpace.homOfVector_appTop_coord _ _ _

private theorem same_open_coordinates
    (S : Scheme.{u}) [IsNoetherian S] (d : ℕ)
    (F : S.Modules) [F.IsFiniteLocallyFreeOfRank d]
    (U : S.Opens) (e e' : Trivialization S d F U) :
    ∃ g : Matrix.GeneralLinearGroup (Fin d) Γ(U.toScheme, ⊤),
      vectorIntegrationChart S d F U e' =
        affineTraceLinearMap U.toScheme d g ≫ vectorIntegrationChart S d F U e := by
  classical
  obtain ⟨G, H, hGH, hHG, _, hc⟩ := transition_spec S d F U e' e
  let g : Matrix.GeneralLinearGroup (Fin d) Γ(U.toScheme, ⊤) :=
    { val := G.transpose.map U.topIso.inv
      inv := H.transpose.map U.topIso.inv
      val_inv := by
        rw [← Matrix.map_mul, ← Matrix.transpose_mul, hHG]
        simpa only [Matrix.transpose_one] using
          (Matrix.map_one U.topIso.inv.hom (map_zero _) (map_one _))
      inv_val := by
        rw [← Matrix.map_mul, ← Matrix.transpose_mul, hGH]
        simpa only [Matrix.transpose_one] using
          (Matrix.map_one U.topIso.inv.hom (map_zero _) (map_one _)) }
  let t := trivializationMap S d F U e
  let t' := trivializationMap S d F U e'
  let a := affineTraceAffineSpaceIso U.toScheme d
  have ht : IsIso t := (trivializationMap_spec S d F U e).1
  have ht' : IsIso t' := (trivializationMap_spec S d F U e').1
  have hforward : t = t' ≫ a.inv ≫ affineTraceLinearMap U.toScheme d g ≫ a.hom := by
    apply AffineSpace.hom_ext
    · have ho : a.hom ≫ AffineSpace (ULift.{u} (Fin d)) U.toScheme ↘ U.toScheme =
          affineTraceProjection U.toScheme d := AffineSpace.homOfVector_over _ _
      simp only [Category.assoc, ho, affineTraceLinearMap_over]
      rw [show a.inv ≫ affineTraceProjection U.toScheme d =
        AffineSpace (ULift.{u} (Fin d)) U.toScheme ↘ U.toScheme from tower_iso_over _ _]
      exact ((trivializationMap_spec S d F U e).2.1).trans
        (trivializationMap_spec S d F U e').2.1.symm
    · rintro ⟨j⟩
      have hco : a.hom.appTop (AffineSpace.coord U.toScheme (ULift.up j)) =
          affineTraceCoordinate U.toScheme d j := tower_iso_coord _ _ _
      simp only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, hco,
        affineTraceLinearMap_coordinate, map_sum, map_mul]
      have hbase : t' ≫ a.inv ≫ affineTraceProjection U.toScheme d =
          (π S d F) ∣_ U := by
        rw [tower_iso_over]
        exact (trivializationMap_spec S d F U e').2.1
      have hcoord (i : Fin d) :
          a.inv.appTop (affineTraceCoordinate U.toScheme d i) =
            AffineSpace.coord U.toScheme (ULift.up i) := by
        rw [← tower_iso_coord U.toScheme d i, ← CommRingCat.comp_apply,
          ← Scheme.Hom.comp_appTop, a.inv_hom_id]
        rfl
      simp only [hcoord]
      simp only [t, t', trivializationMap, AffineSpace.homOfVector_appTop_coord]
      rw [hc j]
      apply Finset.sum_congr rfl
      intro i _
      congr 1
      · change _ = (t' ≫ a.inv ≫ affineTraceProjection U.toScheme d).appTop _
        rw [hbase]
        rfl
  refine ⟨g, ?_⟩
  unfold vectorIntegrationChart
  simp only [← Category.assoc]
  apply congrArg (fun z ↦ z ≫ ((π S d F) ⁻¹ᵁ U).ι)
  change a.hom ≫ inv t' = affineTraceLinearMap U.toScheme d g ≫ a.hom ≫ inv t
  apply (cancel_mono t).mp
  simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  rw [hforward]
  simp only [IsIso.inv_hom_id_assoc, Iso.hom_inv_id_assoc]

private theorem restrict_coproduct {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsOpenImmersion f] (d : ℕ) :
    PreservesColimitsOfShape (Discrete (ULift.{u} (Fin d)))
      (Scheme.Modules.restrictFunctor f) :=
  (Scheme.Modules.restrictAdjunction f).leftAdjoint_preservesColimits.preservesColimitsOfShape

private def restrict_frame (S : Scheme.{u}) (d : ℕ) (F : S.Modules)
    {U V : S.Opens} (h : U ≤ V) (e : Trivialization S d F V) :
    Trivialization S d F U := by
  letI := restrict_coproduct (S.homOfLE h) d
  exact Scheme.Modules.restrictCompIso F V.ι (S.homOfLE h) U.ι (S.homOfLE_ι h) ≪≫
    (Scheme.Modules.restrictFunctor (S.homOfLE h)).mapIso e ≪≫
    (SheafOfModules.mapFreeIso (Scheme.Modules.restrictFunctor (S.homOfLE h))
      (ULift.{u} (Fin d)) (Scheme.Modules.restrictUnitIso (S.homOfLE h)).symm).symm

private theorem restrict_frame_ι (S : Scheme.{u}) (d : ℕ) (F : S.Modules)
    {U V : S.Opens} (h : U ≤ V) (e : Trivialization S d F V) (i : Fin d) :
    SheafOfModules.ιFree (ULift.up i) ≫ (restrict_frame S d F h e).inv =
      (Scheme.Modules.restrictUnitIso (S.homOfLE h)).inv ≫
        (Scheme.Modules.restrictFunctor (S.homOfLE h)).map
          (SheafOfModules.ιFree (ULift.up i) ≫ e.inv) ≫
        (Scheme.Modules.restrictCompIso F V.ι (S.homOfLE h) U.ι
          (S.homOfLE_ι h)).inv := by
  let := restrict_coproduct (S.homOfLE h) d
  simp only [restrict_frame, Iso.trans_inv, Iso.symm_inv, Functor.mapIso_inv,
    ← Category.assoc, SheafOfModules.ιFree_mapFreeIso_hom, Functor.map_comp]
  simp only [Category.assoc, Iso.symm_hom]

private theorem presheaf_path {X : Type u} [TopologicalSpace X]
    (P : (TopologicalSpace.Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u})
    {A B C D E T : (TopologicalSpace.Opens X)ᵒᵖ}
    (a : A ⟶ B) (b : B ⟶ C) (c : C ⟶ D) (d : D ⟶ E)
    (e : A ⟶ T) (f : T ⟶ E) (x : P.obj A) :
    P.map d (P.map c (P.map b (P.map a x))) = P.map f (P.map e x) := by
  have h : a ≫ b ≫ c ≫ d = e ≫ f := Subsingleton.elim _ _
  simpa only [Functor.map_comp, ConcreteCategory.comp_apply] using
    congrArg (fun k ↦ P.map k x) h

private theorem restrict_frame_section (S : Scheme.{u}) (d : ℕ) (F : S.Modules)
    {U V : S.Opens} (h : U ≤ V) (e : Trivialization S d F V) (i : Fin d) :
    frameSection S d F U (restrict_frame S d F h e) i =
      F.presheaf.map (homOfLE h).op (frameSection S d F V e i) := by
  have hi := congrArg (fun (f : SheafOfModules.unit U.toScheme.ringCatSheaf ⟶
      F.restrict U.ι) ↦ (Scheme.Modules.Hom.app f ⊤) (1 : Γ(U.toScheme, ⊤)))
    (restrict_frame_ι S d F h e i)
  simp only [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply] at hi
  have hu : (Scheme.Modules.Hom.app
      (Scheme.Modules.restrictUnitIso (S.homOfLE h)).inv ⊤) (1 : Γ(U.toScheme, ⊤)) =
      (1 : Γ(V.toScheme, (S.homOfLE h) ''ᵁ ⊤)) := by
    change ((S.homOfLE h).appIso ⊤).inv (1 : Γ(U.toScheme, ⊤)) = _
    exact map_one _
  rw [hu] at hi
  change (restrict_frame S d F h e).inv.val.app (op ⊤)
      ((SheafOfModules.ιFree (R := U.toScheme.ringCatSheaf)
        (ULift.up i)).val.app (op ⊤) (1 : Γ(U.toScheme, ⊤))) =
    (Scheme.Modules.Hom.app
      (Scheme.Modules.restrictCompIso F V.ι (S.homOfLE h) U.ι (S.homOfLE_ι h)).inv ⊤)
      ((Scheme.Modules.Hom.app
        ((Scheme.Modules.restrictFunctor (S.homOfLE h)).map
          (SheafOfModules.ιFree (R := V.toScheme.ringCatSheaf) (ULift.up i) ≫ e.inv)) ⊤)
        (1 : Γ(V.toScheme, (S.homOfLE h) ''ᵁ ⊤))) at hi
  unfold frameSection
  rw [hi]
  dsimp only [Scheme.Modules.restrictAppIso, Iso.refl_hom]
  simp only [Scheme.Modules.restrictCompIso, Iso.trans_inv, Iso.symm_inv, Iso.app_inv,
    Scheme.Modules.Hom.comp_app, Scheme.Modules.restrictFunctorComp_inv_app_app,
    Scheme.Modules.restrictFunctorCongr_hom_app_app, ConcreteCategory.comp_apply]
  have hn := PresheafOfModules.naturality_apply
    (SheafOfModules.ιFree (R := V.toScheme.ringCatSheaf) (ULift.up i) ≫ e.inv).val
    (homOfLE (le_top : (S.homOfLE h) ''ᵁ ⊤ ≤ ⊤)).op (1 : Γ(V.toScheme, ⊤))
  change (Scheme.Modules.Hom.app
      (SheafOfModules.ιFree (R := V.toScheme.ringCatSheaf) (ULift.up i) ≫ e.inv)
        ((S.homOfLE h) ''ᵁ ⊤))
      (V.toScheme.presheaf.map (homOfLE (le_top : (S.homOfLE h) ''ᵁ ⊤ ≤ ⊤)).op 1) =
    (F.restrict V.ι).presheaf.map
      (homOfLE (le_top : (S.homOfLE h) ''ᵁ ⊤ ≤ ⊤)).op
      ((Scheme.Modules.Hom.app
        (SheafOfModules.ιFree (R := V.toScheme.ringCatSheaf) (ULift.up i) ≫ e.inv) ⊤)
        (1 : Γ(V.toScheme, ⊤))) at hn
  rw [map_one] at hn
  have hm : (Scheme.Modules.Hom.app
      ((Scheme.Modules.restrictFunctor (S.homOfLE h)).map
        (SheafOfModules.ιFree (R := V.toScheme.ringCatSheaf) (ULift.up i) ≫ e.inv)) ⊤)
      (1 : Γ(V.toScheme, (S.homOfLE h) ''ᵁ ⊤)) =
    (Scheme.Modules.Hom.app
      (SheafOfModules.ιFree (R := V.toScheme.ringCatSheaf) (ULift.up i) ≫ e.inv)
        ((S.homOfLE h) ''ᵁ ⊤)) (1 : Γ(V.toScheme, (S.homOfLE h) ''ᵁ ⊤)) := rfl
  rw [hm, hn]
  have hidU (x : Γ(F.restrict U.ι, ⊤)) : (𝟙 Γ(F.restrict U.ι, ⊤)) x = x := rfl
  have hidV (x : Γ(F.restrict V.ι, ⊤)) : (𝟙 Γ(F.restrict V.ι, ⊤)) x = x := rfl
  erw [hidU, hidV]
  have hr : (F.restrict V.ι).presheaf.map
      (homOfLE (le_top : (S.homOfLE h) ''ᵁ ⊤ ≤ ⊤)).op =
    F.presheaf.map (homOfLE (V.ι.image_mono
      (le_top : (S.homOfLE h) ''ᵁ ⊤ ≤ ⊤))).op := rfl
  rw [hr]
  exact presheaf_path F.presheaf _ _ _ _ _ _ _

private theorem homOfLE_topIso_inv {X : Scheme.{u}} {U V : X.Opens} (h : U ≤ V)
    (r : Γ(X, V)) :
    (X.homOfLE h).appTop (V.topIso.inv r) =
      U.topIso.inv (X.presheaf.map (homOfLE h).op r) := by
  simp only [Scheme.homOfLE_appTop, Scheme.Opens.topIso_inv]
  simp only [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

private theorem restrict_coordinate
    (S : Scheme.{u}) [IsNoetherian S] (d : ℕ)
    (F : S.Modules) [F.IsFiniteLocallyFreeOfRank d]
    {U V : S.Opens} (h : U ≤ V) (e : Trivialization S d F V) (i : Fin d) :
    ((scheme S d F).homOfLE ((π S d F).preimage_mono h)).appTop
      (coordinate S d F V e i) =
    coordinate S d F U (restrict_frame S d F h e) i := by
  rw [coordinate, homOfLE_topIso_inv]
  have ha := CategoryTheory.congr_fun
    ((algebraIso S d F).hom.right.hom.naturality (homOfLE h).op)
    ((SymmetricAlgebraSheaf.inclusion F).val.app (op V) (frameSection S d F V e i))
  have hj := PresheafOfModules.naturality_apply (SymmetricAlgebraSheaf.inclusion F).val
    (homOfLE h).op (frameSection S d F V e i)
  change (SymmetricAlgebraSheaf.inclusion F).val.app (op U)
    (F.presheaf.map (homOfLE h).op (frameSection S d F V e i)) =
    (SymmetricAlgebraSheaf.algebra F).right.obj.map (homOfLE h).op
      ((SymmetricAlgebraSheaf.inclusion F).val.app (op V) (frameSection S d F V e i)) at hj
  rw [← restrict_frame_section S d F h e i] at hj
  exact congrArg (((π S d F) ⁻¹ᵁ U).topIso.inv)
    (ha.symm.trans (congrArg ((algebraIso S d F).hom.right.hom.app (op U)) hj.symm))

private theorem restrict_trivialization
    (S : Scheme.{u}) [IsNoetherian S] (d : ℕ)
    (F : S.Modules) [F.IsFiniteLocallyFreeOfRank d]
    {U V : S.Opens} (h : U ≤ V) (e : Trivialization S d F V) :
    (scheme S d F).homOfLE ((π S d F).preimage_mono h) ≫ trivializationMap S d F V e =
      trivializationMap S d F U (restrict_frame S d F h e) ≫
        AffineSpace.map (ULift.{u} (Fin d)) (S.homOfLE h) := by
  apply AffineSpace.hom_ext
  · simp only [Category.assoc, trivializationMap, AffineSpace.map_over,
      AffineSpace.homOfVector_over_assoc, AffineSpace.homOfVector_over]
    exact (morphismRestrict_homOfLE (π S d F) U V h).symm
  · rintro ⟨i⟩
    simp only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
      trivializationMap, AffineSpace.homOfVector_appTop_coord, AffineSpace.map_appTop_coord]
    exact restrict_coordinate S d F h e i

private theorem tower_map_coord {T S : Scheme.{u}} (f : T ⟶ S) (d : ℕ) (j : Fin d) :
    (affineTraceMap f d).appTop (affineTraceCoordinate S d j) =
      affineTraceCoordinate T d j := by
  induction d with
  | zero => exact Fin.elim0 j
  | succ d ih =>
    refine Fin.lastCases ?_ (fun i ↦ ?_) j
    · simpa only [affineTraceCoordinate, Fin.lastCases_last, affineTraceMap] using!
        (AffineSpace.map_appTop_coord (affineTraceMap f d) PUnit.unit)
    · simp only [affineTraceCoordinate, Fin.lastCases_castSucc]
      change (affineTraceMap f (d + 1)).appTop
        ((AffineSpace PUnit.{u + 1} (affineTraceTower S d) ↘
          affineTraceTower S d).appTop (affineTraceCoordinate S d i)) = _
      erw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop]
      change ((AffineSpace.map PUnit.{u + 1} (affineTraceMap f d)) ≫
        AffineSpace PUnit.{u + 1} (affineTraceTower S d) ↘ affineTraceTower S d).appTop _ = _
      rw [AffineSpace.map_over, Scheme.Hom.comp_appTop, CommRingCat.comp_apply, ih]

private theorem tower_map_iso {T S : Scheme.{u}} (f : T ⟶ S) (d : ℕ) :
    affineTraceMap f d ≫ (affineTraceAffineSpaceIso S d).hom =
      (affineTraceAffineSpaceIso T d).hom ≫ AffineSpace.map (ULift.{u} (Fin d)) f := by
  apply AffineSpace.hom_ext
  · have ho (X : Scheme.{u}) :
        (affineTraceAffineSpaceIso X d).hom ≫
          AffineSpace (ULift.{u} (Fin d)) X ↘ X = affineTraceProjection X d :=
      AffineSpace.homOfVector_over _ _
    simp only [Category.assoc, ho, AffineSpace.map_over]
    rw [← Category.assoc, ho]
    exact (affineTraceMap_isPullback f d).w
  · rintro ⟨j⟩
    simp only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, tower_iso_coord,
      AffineSpace.map_appTop_coord, tower_map_coord]

private theorem restrict_chart
    (S : Scheme.{u}) [IsNoetherian S] (d : ℕ)
    (F : S.Modules) [F.IsFiniteLocallyFreeOfRank d]
    {U V : S.Opens} (h : U ≤ V) (e : Trivialization S d F V) :
    vectorIntegrationRestrictedChart S d F U V h e =
      vectorIntegrationChart S d F U (restrict_frame S d F h e) := by
  have ht : IsIso (trivializationMap S d F V e) := (trivializationMap_spec S d F V e).1
  have hu : IsIso (trivializationMap S d F U (restrict_frame S d F h e)) :=
    (trivializationMap_spec S d F U (restrict_frame S d F h e)).1
  have hi : ((π S d F) ⁻¹ᵁ U).ι =
      (scheme S d F).homOfLE ((π S d F).preimage_mono h) ≫ ((π S d F) ⁻¹ᵁ V).ι :=
    (Scheme.homOfLE_ι _ _).symm
  unfold vectorIntegrationRestrictedChart vectorIntegrationChart
  rw [hi]
  simp only [← Category.assoc]
  apply congrArg (fun z ↦ z ≫ ((π S d F) ⁻¹ᵁ V).ι)
  apply (cancel_mono (trivializationMap S d F V e)).mp
  simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  rw [restrict_trivialization S d F h e]
  simp only [IsIso.inv_hom_id_assoc]
  exact tower_map_iso (S.homOfLE h) d

/-- The two restricted inverse frames differ by an invertible linear coordinate map.
This statement concerns scheme maps only and has no coefficient ring or exchange map.
Source: blueprint sec-smooth-purity/sk-prop-an/def-amb-vector-integration.proof.md,
identification on overlaps by linear changes of frame, and the coordinate convention
of proposition-purity-vector-bundles.
(blueprint: lem-amb-vector-integration-overlap-coordinates).

Proof: restrict each module frame along U into its frame open, using restrictFunctorComp
and the canonical restriction of the finite free module. Their composite is an
isomorphism of the free module on U. The images of its standard global basis and of the
inverse give inverse matrices G,H over Gamma(U,O_U), as in transition_spec. This uses
sections over U itself, with no affineness assumption. In the convention
 e'_j = sum_i G_ij e_i the coordinate substitution is G transpose, so the inverse charts
are related by g = inverse(G transpose). Check this relation on the degree-one
symmetric-algebra generators. The symmetric-algebra universal property and the relative
Spec equivalence give equality of the scheme maps; affineTraceAffineSpaceIso conjugates
the coordinate substitution to affineTraceLinearMap. Restriction of the charts is
exactly affineTraceMap followed by the original inverse chart. For rank zero the empty
matrices are inverse; on the empty open the same generator test is vacuous. -/
theorem vectorIntegration_overlap_coordinates
    (S : Scheme.{u}) [IsNoetherian S] (d : ℕ)
    (F : S.Modules) [F.IsFiniteLocallyFreeOfRank d]
    (U V V' : S.Opens) (hUV : U ≤ V) (hUV' : U ≤ V')
    (e : VectorBundleZeroSection.Trivialization S d F V)
    (e' : VectorBundleZeroSection.Trivialization S d F V') :
    ∃ g : Matrix.GeneralLinearGroup (Fin d) Γ(U.toScheme, ⊤),
      vectorIntegrationRestrictedChart S d F U V' hUV' e' =
        affineTraceLinearMap U.toScheme d g ≫
          vectorIntegrationRestrictedChart S d F U V hUV e := by
  obtain ⟨g, hg⟩ := same_open_coordinates S d F U
    (restrict_frame S d F hUV e) (restrict_frame S d F hUV' e')
  exact ⟨g, by simpa only [restrict_chart] using hg⟩

end AlgebraicGeometry.Etale
