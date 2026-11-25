/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProjectiveBundleQuotientGeometry.ProjectiveBundleQuotientData
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
import WeilConjectures.AlgebraicGeometry.Cohomology.ProjectiveSpaceTwist
import WeilConjectures.AlgebraicGeometry.Modules.TensorSection
import Mathlib.LinearAlgebra.Trace
import WeilConjectures.AlgebraicGeometry.SymmetricProjTautologicalCharts.SymmetricProjTautologicalCharts
import WeilConjectures.AlgebraicGeometry.SymmetricProjTautologicalCharts.SymmetricProjFreeComparison
import WeilConjectures.AlgebraicGeometry.Modules.HomOfBasis
import WeilConjectures.AlgebraicGeometry.Modules.ProjectionFormula

/-!
# Pullback to a projective bundle reflects line isomorphism classes

## References

* EGA II, Remark 4.2.7
* EGA II, Remark 4.2.7, printed p.75
* Stacks Project, Lemma cohomology-projective-space-over-ring (Tag 01XS), degree zero, Lemma
  glue-maps (Tag 04TN)
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.MonoidalCategory

namespace AlgebraicGeometry.ProjectiveBundlePicardClassification

open Scheme.Modules ProjectiveBundleQuotientGeometry

private theorem bijective_of_rank_one (R B : Type u) [CommRing R] [CommRing B]
    (f : R →+* B) (e : let := f.toAlgebra; Nonempty (B ≃ₗ[R] R)) :
    Function.Bijective f := by
  let := f.toAlgebra
  obtain ⟨e⟩ := e
  rcases subsingleton_or_nontrivial R with h | h
  · have : Subsingleton B := Module.subsingleton R B
    exact ⟨fun _ _ _ ↦ Subsingleton.elim _ _, fun b ↦ ⟨0, Subsingleton.elim _ _⟩⟩
  · let : Module.Free R B := Module.Free.of_equiv e.symm
    exact Module.Free.bijective_algebraMap_of_finrank_eq_one
      (e.finrank_eq.trans (Module.finrank_self R))

private theorem projective_space_functions (I R : Type u) [Finite I] [Nonempty I]
    [CommRing R] : IsIso (ℙ(I; Spec (.of R)) ↘ Spec (.of R)).appTop := by
  let P := ℙ(I; Spec (.of R))
  let p := P ↘ Spec (.of R)
  let f : R →+* Γ(P, ⊤) := ((Scheme.ΓSpecIso (.of R)).inv ≫ p.appTop).hom
  let := f.toAlgebra
  let O : P.Modules := 𝟙_ P.Modules
  let T := ProjectiveSpace.twist I (Spec (.of R)) 0
  let := moduleHOfSpec p O 0
  let := moduleHOfSpec p T 0
  let c : R ≃ₗ[R] MvPolynomial.homogeneousSubmodule I R 0 :=
    { (MvPolynomial.homogeneousSubmoduleZeroEquiv I R).toAddEquiv with
      map_smul' := fun a b ↦ Subtype.ext (by simp [smul_eq_mul, MvPolynomial.smul_eq_C_mul]) }
  obtain ⟨t⟩ := ProjectiveSpace.nonempty_H_zero_twist_linearEquiv (n := I) R 0
  let g := (H.zeroLinearEquiv O).trans (unitSectionsEquiv (X := P) ⊤).symm
  let g' : O.H 0 ≃ₗ[R] Γ(P, ⊤) :=
    { g.toAddEquiv with map_smul' := fun a x ↦ g.map_smul (f a) x }
  let h := H.mapLinearEquiv (ProjectiveSpace.unitIsoTwistZero I (Spec (.of R))) 0
  let h' : O.H 0 ≃ₗ[R] T.H 0 :=
    { h.toAddEquiv with map_smul' := fun a x ↦ h.map_smul (f a) x }
  have hf : Function.Bijective f :=
    bijective_of_rank_one R Γ(P, ⊤) f ⟨g'.symm ≪≫ₗ h' ≪≫ₗ t ≪≫ₗ c.symm⟩
  have : IsIso ((Scheme.ΓSpecIso (.of R)).inv ≫ p.appTop) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr hf
  exact IsIso.of_isIso_comp_left (Scheme.ΓSpecIso (.of R)).inv p.appTop

private theorem projective_space_functions_of_affine (I : Type u) [Finite I] [Nonempty I]
    (S : Scheme.{u}) [IsAffine S] : IsIso (ℙ(I; S) ↘ S).appTop := by
  let g := S.isoSpec.hom
  have : IsIso (ProjectiveSpace.map I g) :=
    (ProjectiveSpace.isPullback_map I g).isIso_fst_of_isIso
  have : IsIso (ℙ(I; Spec Γ(S, ⊤)) ↘ Spec Γ(S, ⊤)).appTop :=
    projective_space_functions I Γ(S, ⊤)
  have h := congrArg Scheme.Hom.appTop (ProjectiveSpace.map_over I g)
  rw [Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop] at h
  have : IsIso (g.appTop ≫ (ℙ(I; S) ↘ S).appTop) := h ▸ inferInstance
  exact IsIso.of_isIso_comp_left g.appTop _

private theorem isIso_app_of_isPullback {X Y T : Scheme.{u}} (p : X ⟶ Y)
    (V : Y.Opens) (j : T ⟶ X) (q : T ⟶ V.toScheme)
    (h : CategoryTheory.IsPullback j q p V.ι) [IsIso q.appTop] : IsIso (p.app V) := by
  let e := h.isoIsPullback _ _ (isPullback_morphismRestrict p V).flip
  have he : e.hom ≫ (p ∣_ V) = q := h.isoIsPullback_hom_snd _ _ _
  have : IsIso ((e.hom ≫ (p ∣_ V)).appTop) := he ▸ inferInstance
  rw [Scheme.Hom.comp_appTop] at this
  have : IsIso (p ∣_ V).appTop := IsIso.of_isIso_comp_right _ e.hom.appTop
  rw [morphismRestrict_appTop] at this
  have : IsIso (p.app (V.ι ''ᵁ ⊤)) := IsIso.of_isIso_comp_right _
    (X.presheaf.map (eqToHom (image_morphismRestrict_preimage p V ⊤)).op)
  exact V.ι_image_top ▸ this

private theorem bundle_functions_on_affine (S : Scheme.{u}) (E : S.Modules)
    [E.IsQuasicoherent] (n : ℕ) (V : S.Opens) (hV : IsAffineOpen V)
    (b : E.restrict V.ι ≅ SheafOfModules.free (ULift.{u} (Fin (n + 1)))) :
    IsIso ((SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom.app V) := by
  obtain ⟨D, hopen, _, _⟩ :=
    SymmetricProjTautologicalCharts.symmetric_proj_tautological_chart_gluing S E
  obtain ⟨hE, DV, j, hj, _, _⟩ := hopen V
  let : ((tensorPullback V.ι).obj E).IsQuasicoherent := hE
  let c : tensorPullback V.ι ≅ Scheme.Modules.pullback V.ι :=
    (tensorPullbackSectionAdjunction V.ι).leftAdjointUniq
      (pullbackPushforwardAdjunction V.ι)
  let d : (tensorPullback V.ι).obj E ≅ E.restrict V.ι :=
    c.app E ≪≫ ((restrictFunctorIsoPullback V.ι).app E).symm
  let b' : RelativeProjectiveSpace.freeModule V.toScheme n ≅
      (tensorPullback V.ι).obj E := b.symm ≪≫ d.symm
  obtain ⟨_, e, _, _, he, _, _⟩ :=
    SymmetricProjTautologicalCharts.free_compatibility_of_normalized_quotient
      V.toScheme ((tensorPullback V.ι).obj E) DV n b'
  let : IsAffine V.toScheme := hV
  have : IsIso (ℙ(ULift.{u} (Fin (n + 1)); V.toScheme) ↘ V.toScheme).appTop :=
    projective_space_functions_of_affine _ V.toScheme
  have : IsIso (SymmetricAlgebraSheaf.gradedAlgebraData
      ((tensorPullback V.ι).obj E)).relProjHom.appTop := by
    rw [← he, Scheme.Hom.comp_appTop]
    infer_instance
  exact isIso_app_of_isPullback _ V j _ hj

/-- The canonical map on functions of every base open is bijective. -/
private theorem projective_bundle_base_functions (S : Scheme.{u}) (E : S.Modules)
    [E.IsQuasicoherent] (r : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E r] (hr : 0 < r)
    (U : S.Opens) :
    Function.Bijective ((SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom.app U) := by
  classical
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hr)
  obtain ⟨ι, W, hW, eW⟩ :=
    IsFiniteLocallyFreeOfRank.exists_restrict_iso_free E (r := n + 1)
  let B : Set S.Opens := {V | IsAffineOpen V ∧
    Nonempty (E.restrict V.ι ≅ SheafOfModules.free (ULift.{u} (Fin (n + 1))))}
  have hB : TopologicalSpace.Opens.IsBasis B := by
    rw [TopologicalSpace.Opens.isBasis_iff_nbhd]
    intro V x hx
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp
      (hW.ge (show x ∈ ⊤ from trivial))
    obtain ⟨_, ⟨(Z : S.Opens), hZ, rfl⟩, hxZ, hZV⟩ :=
      S.isBasis_affineOpens.exists_subset_of_mem_open
      (show x ∈ V ⊓ W i from ⟨hx, hi⟩) (V ⊓ W i).isOpen
    let f := S.homOfLE (hZV.trans inf_le_right)
    let b : E.restrict Z.ι ≅ SheafOfModules.free (ULift.{u} (Fin (n + 1))) :=
      restrictCompIso E (W i).ι f Z.ι (S.homOfLE_ι _) ≪≫
        (restrictFunctor f).mapIso (eW i).some ≪≫ restrictFreeIso f _
    exact ⟨Z, ⟨hZ, ⟨b⟩⟩, hxZ, hZV.trans inf_le_left⟩
  let p := (SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom
  let a : 𝟙_ S.Modules ⟶ (pushforward p).obj (𝟙_ _) :=
    SheafOfModules.unitToPushforwardObjUnit p.toRingCatSheafHom
  have : IsIso a := by
    apply isIso_of_bijective_app_of_basis
      (O := fun V : {V // V ∈ B} ↦ V.val) (by simpa using hB)
    intro V
    obtain ⟨hV, ⟨b⟩⟩ := V.property
    have := bundle_functions_on_affine S E n V.val hV b
    exact ConcreteCategory.bijective_of_isIso
      ((SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom.app V.val)
  exact ConcreteCategory.bijective_of_isIso (a.app U)

/-- Isomorphic pullbacks of two base lines imply that the base lines are isomorphic. -/
theorem projective_bundle_pullback_line_reflection (S : Scheme.{u}) (E : S.Modules)
    [E.IsQuasicoherent] (r : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E r] (hr : 0 < r)
    (N N' : S.Modules) (hN : N.IsInvertible) (hN' : N'.IsInvertible)
    (e : Nonempty ((tensorPullback
      (SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom).obj N ≅
        (tensorPullback (SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom).obj N')) :
    Nonempty (N ≅ N') := by
  classical
  let p := (SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom
  let c : tensorPullback p ≅ Scheme.Modules.pullback p :=
    (tensorPullbackSectionAdjunction p).leftAdjointUniq (pullbackPushforwardAdjunction p)
  let a := SheafOfModules.unitToPushforwardObjUnit p.toRingCatSheafHom
  have ha : IsIso a := by
    rw [Scheme.Modules.Hom.isIso_iff_isIso_app]
    intro U
    rw [ConcreteCategory.isIso_iff_bijective]
    exact projective_bundle_base_functions S E r hr U
  let o : (pushforward p).obj (𝟙_ _) ≅ 𝟙_ S.Modules := (asIso a).symm
  let : N.IsInvertible := hN
  let : N'.IsInvertible := hN'
  obtain ⟨i⟩ := nonempty_pushforward_pullback_iso_self p o N
  obtain ⟨j⟩ := nonempty_pushforward_pullback_iso_self p o N'
  obtain ⟨e⟩ := e
  exact ⟨i.symm ≪≫ (pushforward p).mapIso
    ((c.app N).symm ≪≫ e ≪≫ c.app N') ≪≫ j⟩

end AlgebraicGeometry.ProjectiveBundlePicardClassification
