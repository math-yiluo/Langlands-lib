import Langlands.AlgebraicGeometry.ProjectiveSpace.HomogeneousSectionGeometry
import Langlands.AlgebraicGeometry.Modules.TensorLocalUnitFactorizationProof

/-! # The actual projective twist as a tensor power -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace MvPolynomial
open Langlands.SchemeModule Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules
open scoped TensorProduct

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AlgebraicGeometry.ProjectiveSpace

attribute [local instance] MvPolynomial.gradedAlgebra

private lemma sectionRes_tensorSection {Y : Scheme.{u}} (M N : Y.Modules)
    (s : GlobalSections M) (t : GlobalSections N) (U : Y.Opens) :
    sectionRes (tensorObj M N) (tensorSection M N s t) U =
      ((tensorSheafifyUnit M N).app (op U)).hom
        (sectionRes M s U ⊗ₜ[Y.presheaf.obj (op U)] sectionRes N t U) := by
  let one : (structureModule Y).val.obj (op U) := (1 : Γ(Y, U))
  have h₁ : ((tensorLeftUnitor (structureModule Y)).inv.val.app (op U)).hom one =
      ((tensorSheafifyUnit (structureModule Y) (structureModule Y)).app (op U)).hom
        (one ⊗ₜ[Y.presheaf.obj (op U)] one) := tensorLeftUnitor_inv_app_one U
  have h₂ : ((tensorSheafifyUnit M N).app (op U)).hom
      (((sectionHom M s).val.app (op U)).hom one ⊗ₜ[Y.presheaf.obj (op U)]
        ((sectionHom N t).val.app (op U)).hom one) =
      ((tensorMap (sectionHom M s) (sectionHom N t)).val.app (op U)).hom
        (((tensorSheafifyUnit (structureModule Y) (structureModule Y)).app (op U)).hom
          (one ⊗ₜ[Y.presheaf.obj (op U)] one)) :=
    congrArg (fun f => (f.app (op U)).hom (one ⊗ₜ[Y.presheaf.obj (op U)] one))
      (tensorSheafifyUnit_naturality (sectionHom M s) (sectionHom N t))
  have hm : ((sectionHom M s).val.app (op U)).hom one = sectionRes M s U :=
    sectionHom_app_one M s U
  have hn : ((sectionHom N t).val.app (op U)).hom one = sectionRes N t U :=
    sectionHom_app_one N t U
  rw [hm, hn] at h₂
  rw [show sectionRes (tensorObj M N) (tensorSection M N s t) U = _ from
    tensorSection_restrict M N s t U]
  change ((tensorMap (sectionHom M s) (sectionHom N t)).val.app (op U)).hom
    (((tensorLeftUnitor (structureModule Y)).inv.val.app (op U)).hom one) = _
  rw [h₁, ← h₂]

/-- A local coefficient relation between sections gives its `d`-th power as the local
coefficient relation between their `d`-th tensor powers. -/
lemma sectionRes_sectionPow_eq_smul {Y : Scheme.{u}} (M : Y.Modules)
    (s t : GlobalSections M) (U : Y.Opens) (r : Γ(Y, U))
    (h : sectionRes M s U = r • sectionRes M t U) (d : ℕ) :
    sectionRes (tensorPow M d) (sectionPow M s d) U =
      r ^ d • sectionRes (tensorPow M d) (sectionPow M t d) U := by
  induction d with
  | zero => rw [pow_zero, one_smul]; rfl
  | succ d ih =>
    change sectionRes (tensorObj M (tensorPow M d)) (tensorSection M _ s (sectionPow M s d)) U =
      r ^ (d + 1) • sectionRes (tensorObj M (tensorPow M d))
        (tensorSection M _ t (sectionPow M t d)) U
    rw [sectionRes_tensorSection, sectionRes_tensorSection, h, ih]
    let R := Γ(Y, U)
    let x : M.val.obj (op U) := sectionRes M t U
    let y : (tensorPow M d).val.obj (op U) := sectionRes (tensorPow M d) (sectionPow M t d) U
    let e := ((tensorSheafifyUnit M (tensorPow M d)).app (op U)).hom
    change e (((r : R) • x) ⊗ₜ[R] ((r ^ d : R) • y)) = (r ^ (d + 1) : R) • e (x ⊗ₜ[R] y)
    have hscale : ((r : R) • x) ⊗ₜ[R] ((r ^ d : R) • y) =
        (r ^ (d + 1) : R) • (x ⊗ₜ[R] y) := by
      rw [pow_succ']
      exact TensorProduct.smul_tmul_smul r (r ^ d) x y
    exact (congrArg e hscale).trans (e.map_smul _ _)

variable {A : Type u} [CommRing A] {m : ℕ}

private lemma coordinatePow_fraction (i j : Fin (m + 1)) (d : ℕ) :
    homogeneousChartSection i (isHomogeneous_X_pow j d :
      (X j ^ d : ProjectiveCoordinateRing A m).IsHomogeneous d) =
      projectiveSpaceCoordinateRatio A m i j ^ d := by
  let R := ProjectiveCoordinateRing A m
  let 𝒜 := projectiveSpaceGrading A m
  let Z := HomogeneousLocalization 𝒜 (.powers (X i : R))
  let a : Z := HomogeneousLocalization.Away.mk 𝒜 (projectiveSpace_X_mem A m i) 1 (X j)
    (by rw [one_smul]; exact projectiveSpace_X_mem A m j)
  let b : Z := HomogeneousLocalization.mk
    ⟨d, ⟨X j ^ d, (mem_homogeneousSubmodule _ _).mpr (isHomogeneous_X_pow j d)⟩,
      ⟨X i ^ d, (mem_homogeneousSubmodule _ _).mpr (isHomogeneous_X_pow i d)⟩, ⟨d, rfl⟩⟩
  have h : b = a ^ d := by
    apply HomogeneousLocalization.val_injective
    change Localization.mk (X j ^ d : R) (⟨X i ^ d, ⟨d, rfl⟩⟩ : Submonoid.powers (X i : R)) =
      (a ^ d).val
    rw [HomogeneousLocalization.val_pow]
    change _ = (Localization.mk (X j : R)
      (⟨X i ^ 1, ⟨1, rfl⟩⟩ : Submonoid.powers (X i : R))) ^ d
    rw [Localization.mk_pow]
    congr 1
    apply Subtype.ext
    simp [pow_one]
  change (Proj.awayToSection 𝒜 (X i)).hom b = (Proj.awayToSection 𝒜 (X i)).hom a ^ d
  rw [h, map_pow]

/-- The nonnegative-degree twist is isomorphic to the corresponding tensor power of
the degree-one twist. In positive degree the comparison can identify all pure powers of
the coordinate sections with the corresponding homogeneous sections. -/
theorem exists_twistTensorPowIso (A : Type u) [CommRing A] (m d : ℕ) :
    ∃ e : tensorPow (twistOne A m) d ≅ (twistLineBundle A m d).obj,
      ∀ j : Fin (m + 1), e.hom.app ⊤ (sectionPow (twistOne A m) (twistOneCoordinate A m j) d) =
        homogeneousSection (isHomogeneous_X_pow j d) := by
  by_cases hd : d = 0
  · subst d
    let q := homogeneousSection (isHomogeneous_X_pow (0 : Fin (m + 1)) 0 :
      (X (0 : Fin (m + 1)) ^ 0 : ProjectiveCoordinateRing A m).IsHomogeneous 0)
    have hq : ∀ j : Fin (m + 1), homogeneousSection (isHomogeneous_X_pow j 0 :
        (X j ^ 0 : ProjectiveCoordinateRing A m).IsHomogeneous 0) = q := by
      intro j
      apply Subtype.ext
      funext x
      change Localization.mk (X j ^ 0 : ProjectiveCoordinateRing A m) 1 =
        Localization.mk (X (0 : Fin (m + 1)) ^ 0 : ProjectiveCoordinateRing A m) 1
      rw [pow_zero, pow_zero]
    have hgen : trivializationOpen (twistLineBundle A m 0).obj q = ⊤ := by
      rw [trivializationOpen_homogeneousSection, pow_zero, Proj.basicOpen_one]
    have hbij (U : (ProjectiveSpace A m).Opens) := bijective_sectionHom_app_of_le
      (twistLineBundle A m 0).obj q (show U ≤ trivializationOpen _ q by rw [hgen]; exact le_top)
    have : IsIso (sectionHom (twistLineBundle A m 0).obj q) := by
      apply Scheme.Modules.Hom.isIso_iff_isIso_app.mpr
      intro U
      rw [ConcreteCategory.isIso_iff_bijective]
      exact hbij U
    refine ⟨asIso (sectionHom _ q), fun j => ?_⟩
    rw [hq, sectionPow_zero]
    exact Langlands.Scheme.Modules.sectionHom_app_top_one _ _
  · let U := projectiveSpaceCoordinateOpen A m
    let M := (twistLineBundle A m d).obj
    let N := tensorPow (twistOne A m) d
    let q := fun j : Fin (m + 1) => homogeneousSection (isHomogeneous_X_pow j d :
      (X j ^ d : ProjectiveCoordinateRing A m).IsHomogeneous d)
    let t := fun j => sectionPow (twistOne A m) (twistOneCoordinate A m j) d
    have hM (j) : trivializationOpen M (q j) = U j := by
      rw [trivializationOpen_homogeneousSection, Proj.basicOpen_pow _ _ d (Nat.pos_of_ne_zero hd)]
      rfl
    have hN (j) : trivializationOpen N (t j) = U j := by
      change trivializationOpen (tensorPow (twistOneLineBundle A m).obj d)
        (sectionPow (twistOneLineBundle A m).obj (twistOneCoordinate A m j) d) = U j
      rw [trivializationOpen_sectionPow _ _ (Nat.pos_of_ne_zero hd)]
      exact trivializationOpen_twistOneLinearSection A m ⟨X j, projectiveSpace_X_mem A m j⟩
    have hcov : (⨆ i, trivializationOpen M (q i)) = ⊤ := by
      simp only [hM]; exact iSup_projectiveSpaceCoordinateOpen A m
    change ∃ e : N ≅ M, ∀ j, e.hom.app ⊤ (t j) = q j
    apply LinearSystem.exists_iso_of_matching_sections q t hcov
    · intro j; rw [hM, hN]
    · intro i j V hV c hc
      rw [hM] at hV
      let r := projectiveSpaceCoordinateRatio A m i j
      let rV := (ProjectiveSpace A m).presheaf.map (homOfLE hV).op r
      have hres : sectionRes M (q j) V = rV ^ d • sectionRes M (q i) V := by
        have h := congrArg (M.presheaf.map (homOfLE hV).op)
          (homogeneousSection_restrict (isHomogeneous_X_pow j d :
            (X j ^ d : ProjectiveCoordinateRing A m).IsHomogeneous d) i)
        rw [coordinatePow_fraction, Scheme.Modules.map_smul, map_pow,
          sectionRes_res, sectionRes_res] at h
        exact h
      have hc' : c = rV ^ d := by
        apply ((LineBundleDescent.trivializesOn_iff_bijective _ _ (U i)).mp
          (trivializesOn_homogeneousCoordinate i d) V hV).injective
        rw [LineBundleDescent.sectionHom_app, LineBundleDescent.sectionHom_app]
        exact hc.symm.trans hres
      have hunpow : sectionRes (twistOne A m) (twistOneCoordinate A m j) V =
          rV • sectionRes (twistOne A m) (twistOneCoordinate A m i) V := by
        have h := congrArg ((twistOne A m).presheaf.map (homOfLE hV).op)
          (twistOneCoordinate_restrict_coordinateOpen A m i j)
        change (twistOne A m).presheaf.map (homOfLE hV).op (sectionRes _ _ (U i)) =
          (twistOne A m).presheaf.map (homOfLE hV).op (r • sectionRes _ _ (U i)) at h
        rw [Scheme.Modules.map_smul, sectionRes_res, sectionRes_res] at h
        exact h
      rw [hc']
      exact sectionRes_sectionPow_eq_smul _ _ _ V _ hunpow d

/-- Comparison of the actual degree-`d` twist with the `d`-th tensor power of `𝒪(1)`. -/
def twistTensorPowIso (A : Type u) [CommRing A] (m d : ℕ) :
    tensorPow (twistOne A m) d ≅ (twistLineBundle A m d).obj :=
  (exists_twistTensorPowIso A m d).choose

end Langlands.AlgebraicGeometry.ProjectiveSpace
