/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SymmetricAlgebraSheaf.CanonicalSymmetricGradedAlgebra
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import WeilConjectures.AlgebraicGeometry.StructureSheafCohomologyPullback
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Geometrically.Reduced
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
import WeilConjectures.AlgebraicGeometry.ProjectiveBundleQuotientGeometry.ProjectiveBundleQuotientGeometry
import WeilConjectures.AlgebraicGeometry.Structure.StructureSheafCohomologyPullbackFunctorial
import WeilConjectures.AlgebraicGeometry.Cohomology.ProjectiveSpaceTwist
import WeilConjectures.AlgebraicGeometry.Regular

/-! # Flatness and structure-sheaf cohomology of canonical projective bundles

## References

* Stacks Project, Constructions, Tags 01OB and 01OE
* Stacks Project, Constructions, Tags 01OB and 01OE, and Cohomology of Schemes, the projective-space
  structure-sheaf cohomology computation
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.ProjectiveBundlePicardClassification

attribute [local irreducible] Scheme.Modules.tensorPullback
  Scheme.GradedAlgebraData.relProj Scheme.GradedAlgebraData.relProjHom
  Scheme.structureSheafAb Scheme.structureSheafCohomologyPullback

private theorem smooth_projectiveSpace (n : Type u) [Finite n] (S : Scheme.{u}) :
    Smooth (ℙ(n; S) ↘ S) := by
  classical
  let _ := Fintype.ofFinite n
  apply IsZariskiLocalAtSource.of_iSup_eq_top (P := @Smooth)
    (ProjectiveSpace.standardOpen n S) (ProjectiveSpace.iSup_standardOpen n S)
  intro i
  rw [← ProjectiveSpace.standardOpenIso_hom_over]
  have := SmoothOfRelativeDimension.smooth (Nat.card {j : n // j ≠ i})
    (𝔸({j : n // j ≠ i}; S) ↘ S)
  infer_instance

private theorem connected_projectiveSpace (n : Type u) [Nonempty n]
    (k : Type u) [Field k] : ConnectedSpace (ℙ(n; Spec (.of k))) := by
  classical
  let S := Spec (CommRingCat.of k)
  have hs : Ideal.span (Set.range (fun _ : n ↦ (1 : Γ(S, ⊤)))) = ⊤ :=
    Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span ⟨Classical.arbitrary n, rfl⟩) isUnit_one
  let x : ℙ(n; S) := ProjectiveSpace.homOfSections (𝟙 S) _ hs (IsLocalRing.closedPoint k)
  have hx (i : n) : x ∈ ProjectiveSpace.standardOpen n S i := by
    have h : IsLocalRing.closedPoint k ∈ ProjectiveSpace.homOfSections (𝟙 S) _ hs ⁻¹ᵁ
        ProjectiveSpace.standardOpen n S i := by
      rw [ProjectiveSpace.homOfSections_preimage_standardOpen,
        Scheme.basicOpen_of_isUnit _ isUnit_one]
      trivial
    exact h
  have hc (i : n) : _root_.IsConnected (ProjectiveSpace.standardOpen n S i : Set ℙ(n; S)) := by
    let e := ProjectiveSpace.standardOpenIso n S i ≪≫ AffineSpace.SpecIso _ (.of k)
    have he : Set.range (e.inv ≫ (ProjectiveSpace.standardOpen n S i).ι) =
        (ProjectiveSpace.standardOpen n S i : Set ℙ(n; S)) := by
      rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
        show Set.range e.inv = Set.univ from Set.range_eq_univ.mpr e.inv.homeomorph.surjective,
        Set.image_univ, Scheme.Opens.range_ι]
    rw [← he]
    exact isConnected_range (e.inv ≫ _).continuous
  refine connectedSpace_iff_univ.mpr ⟨⟨x, trivial⟩, ?_⟩
  have hcover : (⋃ i, (ProjectiveSpace.standardOpen n S i : Set ℙ(n; S))) = Set.univ := by
    simpa only [TopologicalSpace.Opens.coe_iSup, TopologicalSpace.Opens.coe_top] using
      congrArg (fun U : (ℙ(n; S)).Opens ↦ (U : Set ℙ(n; S)))
        (ProjectiveSpace.iSup_standardOpen n S)
  rw [← hcover]
  exact isPreconnected_iUnion ⟨x, Set.mem_iInter.mpr hx⟩ (fun i ↦ (hc i).isPreconnected)

private theorem geometricallyConnected_projectiveSpace (n : Type u) [Nonempty n]
    (S : Scheme.{u}) : GeometricallyConnected (ℙ(n; S) ↘ S) := by
  refine ⟨fun K _ y Z fst snd h ↦ ?_⟩
  have e : Z ≅ ℙ(n; Spec (.of K)) :=
    h.isoIsPullback _ _ (ProjectiveSpace.isPullback_map n y)
  have := connected_projectiveSpace n K
  exact (Scheme.homeoOfIso e.symm).connectedSpace_iff.mp this

private theorem local_projectiveSpace_model (S : Scheme.{u}) (E : S.Modules)
    [E.IsQuasicoherent] (d : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E (d + 1)] :
    let p := (SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom
    ∃ (I : Type u) (U : I → S.Opens), (⨆ i, U i) = ⊤ ∧
      ∀ i, ∃ e : (p ⁻¹ᵁ U i).toScheme ≅ ℙ(ULift.{u} (Fin (d + 1)); (U i).toScheme),
        e.hom ≫ (ℙ(ULift.{u} (Fin (d + 1)); (U i).toScheme) ↘ (U i).toScheme) =
          p ∣_ U i := by
  classical
  let p := (SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom
  obtain ⟨I, U, hU, he⟩ :=
    Scheme.Modules.IsFiniteLocallyFreeOfRank.exists_restrict_iso_free E (r := d + 1)
  obtain ⟨D, _, _, _, _, _, hopen, _⟩ :=
    ProjectiveBundleQuotientGeometry.projective_bundle_quotient_geometry S E
  refine ⟨I, U, hU, fun i ↦ ?_⟩
  obtain ⟨hE, DV, j, hj, _⟩ := hopen (U i)
  let E' := (Scheme.Modules.tensorPullback (U i).ι).obj E
  let _ : E'.IsQuasicoherent := hE
  let b : RelativeProjectiveSpace.freeModule (U i).toScheme d ≅ E' :=
    (he i).some.symm ≪≫ (Scheme.Modules.restrictFunctorIsoPullback (U i).ι).app E ≪≫
      (Scheme.Modules.boundaryPullbackComparison (U i).ι).symm.app E
  obtain ⟨D', _, _, _, _, _, _, hfree⟩ :=
    ProjectiveBundleQuotientGeometry.projective_bundle_quotient_geometry (U i).toScheme E'
  obtain ⟨_, eStd, _, _, hStd, _⟩ := hfree d b
  let eOpen := hj.isoIsPullback _ _ (isPullback_morphismRestrict p (U i)).flip
  refine ⟨eOpen.symm ≪≫ eStd, ?_⟩
  change (eOpen.inv ≫ eStd.hom) ≫ _ = _
  rw [Category.assoc, hStd]
  exact hj.isoIsPullback_inv_snd _ _ _

private theorem fibre_projectiveSpace_model {X S : Scheme.{u}} (p : X ⟶ S)
    (n : Type u) (V : S.Opens)
    (e : (p ⁻¹ᵁ V).toScheme ≅ ℙ(n; V.toScheme))
    (he : e.hom ≫ (ℙ(n; V.toScheme) ↘ V.toScheme) = p ∣_ V)
    (s : S) (hs : s ∈ V) :
    ∃ e : p.fiber s ≅ ℙ(n; Spec (S.residueField s)),
      e.hom ≫ (ℙ(n; Spec (S.residueField s)) ↘ Spec (S.residueField s)) =
        p.fiberToSpecResidueField s := by
  classical
  have hrange : Set.range (S.fromSpecResidueField s) ⊆ Set.range V.ι := by
    rw [S.range_fromSpecResidueField, Scheme.Opens.range_ι]
    exact Set.singleton_subset_iff.mpr hs
  let g := IsOpenImmersion.lift V.ι (S.fromSpecResidueField s) hrange
  have hg : g ≫ V.ι = S.fromSpecResidueField s := IsOpenImmersion.lift_fac _ _ _
  have hi : IsPullback e.inv (ℙ(n; V.toScheme) ↘ V.toScheme)
      (p ∣_ V) (𝟙 V.toScheme) := by
    apply IsPullback.of_horiz_isIso
    constructor
    rw [← he, e.inv_hom_id_assoc, Category.comp_id]
  have hV := hi.paste_horiz (isPullback_morphismRestrict p V).flip
  simp only [Category.id_comp] at hV
  have h := (ProjectiveSpace.isPullback_map n g).paste_horiz hV
  rw [hg] at h
  let eF := (IsPullback.of_hasPullback p (S.fromSpecResidueField s)).isoIsPullback _ _ h
  exact ⟨eF, (IsPullback.of_hasPullback p (S.fromSpecResidueField s)).isoIsPullback_hom_snd
    _ _ h⟩

private theorem subsingleton_H1_projectiveSpace (d : ℕ) (k : Type u) [Field k] :
    Subsingleton (Sheaf.H (Scheme.structureSheafAb
      ℙ(ULift.{u} (Fin (d + 1)); Spec (.of k))) 1) := by
  let n := ULift.{u} (Fin (d + 1))
  have hn : Fintype.card n = d + 1 := by simp [n]
  have ht : Subsingleton ((ProjectiveSpace.twist n (Spec (.of k)) 0).H 1) := by
    by_cases hd : d = 1
    · subst d
      exact ProjectiveSpace.subsingleton_H_twist_top_of_commRing k hn (by decide) (by norm_num)
    · exact ProjectiveSpace.subsingleton_H_twist_of_ne_of_commRing k hn 0 (by decide) (Ne.symm hd)
  let _ := ht
  unfold Scheme.structureSheafAb
  change Subsingleton (Scheme.Modules.H
    (SheafOfModules.unit (ℙ(n; Spec (.of k))).ringCatSheaf) 1)
  exact Scheme.Modules.subsingleton_H_of_iso (ProjectiveSpace.unitIsoTwistZero n _).symm 1

private theorem subsingleton_structureH_of_iso {X Y : Scheme.{u}} (e : X ≅ Y) (q : ℕ)
    [Subsingleton (Sheaf.H (Scheme.structureSheafAb Y) q)] :
    Subsingleton (Sheaf.H (Scheme.structureSheafAb X) q) := by
  let f := Scheme.structureSheafCohomologyPullback e.inv q
  let g := Scheme.structureSheafCohomologyPullback e.hom q
  have hgf : g.comp f = AddMonoidHom.id _ := by
    rw [← Scheme.structureSheafCohomologyPullback_functorial.2, e.hom_inv_id,
      Scheme.structureSheafCohomologyPullback_functorial.1]
  have hinj : Function.Injective f :=
    Function.LeftInverse.injective (fun x ↦ DFunLike.congr_fun hgf x)
  exact ⟨fun a b ↦ hinj (Subsingleton.elim _ _)⟩

/-- The projection of a positive-rank vector bundle is flat and locally of finite
presentation. Its residue-field fibres are geometrically reduced and connected,
and their structure sheaves have vanishing first cohomology.
-/
theorem projective_bundle_fiber_geometry (S : Scheme.{u}) (E : S.Modules)
    [E.IsQuasicoherent] (r : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E r] (hr : 0 < r) :
    let p := (SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom
    Flat p ∧ LocallyOfFinitePresentation p ∧
      ∀ s : S, GeometricallyReduced (p.fiberToSpecResidueField s) ∧
        GeometricallyConnected (p.fiberToSpecResidueField s) ∧
        Subsingleton (Sheaf.H (Scheme.structureSheafAb (p.fiber s)) 1) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hr)
  let p := (SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom
  let n := ULift.{u} (Fin (d + 1))
  obtain ⟨I, U, hU, hmodel⟩ := local_projectiveSpace_model S E d
  have hSmooth : Smooth p := by
    apply IsZariskiLocalAtTarget.of_iSup_eq_top (P := @Smooth) U hU
    intro i
    obtain ⟨e, he⟩ := hmodel i
    rw [← he]
    have := smooth_projectiveSpace n (U i).toScheme
    infer_instance
  let _ := hSmooth
  have : GeometricallyReduced p := Smooth.geometricallyReduced p
  refine ⟨inferInstance, inferInstance, ?_⟩
  intro s
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp (show s ∈ ⨆ i, U i by rw [hU]; trivial)
  obtain ⟨e, he⟩ := hmodel i
  obtain ⟨eF, hF⟩ := fibre_projectiveSpace_model p n (U i) e he s hi
  refine ⟨inferInstance, ?_, ?_⟩
  · constructor
    rw [← hF]
    exact (MorphismProperty.cancel_left_of_respectsIso
      (geometrically (fun X : Scheme.{u} ↦ ConnectedSpace X)) eF.hom _).mpr
        (geometricallyConnected_projectiveSpace n
          (Spec (S.residueField s))).geometrically_connectedSpace
  · have := subsingleton_H1_projectiveSpace d (S.residueField s)
    exact subsingleton_structureH_of_iso eF 1

end AlgebraicGeometry.ProjectiveBundlePicardClassification
