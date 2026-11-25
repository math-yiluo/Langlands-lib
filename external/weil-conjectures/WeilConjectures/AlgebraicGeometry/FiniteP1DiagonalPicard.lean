/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.ProjectiveLineDiagonalMaps
import WeilConjectures.AlgebraicGeometry.P1DiagonalLocalIdeal

/-! # The divisor line of the projective-line diagonal

Source: blueprint lemma-class-diagonal-projective-line, the equation x0*y1-x1*y0.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
namespace AlgebraicGeometry.Etale

open Scheme.Modules ProjectiveSpace

private def p1SectionHom {X : Scheme.{u}} (M : X.Modules) (s : Γ(M, ⊤)) :
    𝟙_ X.Modules ⟶ M :=
  M.unitHomEquiv.symm (PresheafOfModules.sectionsMk
    (fun W ↦ M.val.map (homOfLE le_top : W.unop ⟶ ⊤).op s)
    (fun W _ f ↦ (ConcreteCategory.congr_hom
      (M.presheaf.map_comp (homOfLE le_top : W.unop ⟶ ⊤).op f) s).symm))

private lemma p1SectionHom_app_one {X : Scheme.{u}} (M : X.Modules) (s : Γ(M, ⊤))
    (U : X.Opens) :
    (p1SectionHom M s).app U (1 : Γ(X, U)) =
      M.presheaf.map (homOfLE le_top).op s := by
  exact congrArg (fun t ↦ t.val (Opposite.op U))
    (M.unitHomEquiv.apply_symm_apply _)

private lemma coordinate_restrict {S X : Scheme.{u}} (g : X ⟶ ProjectiveLine S)
    (i k : ULift.{u} (Fin 2)) (U : X.Opens)
    (hU : U ≤ g ⁻¹ᵁ standardOpen (ULift.{u} (Fin 2)) S i) :
    ((Scheme.Modules.pullback g).obj (twist (ULift.{u} (Fin 2)) S 1)).presheaf.map
        (homOfLE (le_top : U ≤ ⊤)).op
        (pullbackTopSection g (twistOneSection (ULift.{u} (Fin 2)) S k)) =
      g.appLE _ U hU (coordRatio (ULift.{u} (Fin 2)) S i k) •
        ((Scheme.Modules.pullback g).obj (twist (ULift.{u} (Fin 2)) S 1)).presheaf.map
          (homOfLE (le_top : U ≤ ⊤)).op
          (pullbackTopSection g (twistOneSection (ULift.{u} (Fin 2)) S i)) := by
  have h := presheaf_map_homOfLE_eq_smul _ hU
    (pullbackSection_twistOneSection_map_eq_smul g k i)
  simpa only [pullbackTopSection, presheaf_map_homOfLE_map_homOfLE,
    coordRatio, standardOpen, Scheme.Hom.appLE, CommRingCat.comp_apply] using h

private lemma pic_map_ofIsInvertible {X Y : Scheme.{u}} (g : X ⟶ Y) (M : Y.Modules)
    [M.IsInvertible] :
    Scheme.Pic.map g (Scheme.Pic.ofIsInvertible M) =
      Scheme.Pic.ofIsInvertible ((Scheme.Modules.pullback g).obj M) := by
  apply (Scheme.Pic.eq_ofIsInvertible_iff _ _).2
  exact ⟨fromSkeletonToSkeletonIso _ ≪≫
    (Scheme.Modules.pullback g).mapIso (Scheme.Pic.ofIsInvertibleIso M)⟩

/-- Under either projection chart, the dual diagonal ideal is the tensor product
of the relative hyperplane line and the pullback of the base hyperplane line.
Source: blueprint lemma-class-diagonal-projective-line, standard-chart calculation;
lem-sp-finite-p1-diagonal-kummer-component-formula, proof step 1.
(auxiliary; not a blueprint node)

Proof: on the product chart xi*yj nonzero, the diagonal ideal has the frame
(x0*y1-x1*y0)/(xi*yj). Its dual frame has transition ratios those of
p1*O(1) tensor p2*O(1). Map these dual frames to the tensor products of the
standard hyperplane frames. The ratios agree on all pairwise overlaps, so these
maps glue to an isomorphism of invertible modules. Pulling this isomorphism
through either canonical chart identifies one factor with the relative O(1)
and the other with the pullback of O(1) on the base P. Passing to Picard classes
gives the equation. Interchanging the factors negates the equation of the
diagonal, which leaves the divisor line unchanged. The calculation works over
arbitrary rings, including nonreduced rings and the zero ring. -/
theorem finiteP1_diagonal_picard (S : Scheme.{u})
    (hI : (pullback.diagonal (ProjectiveLine S ↘ S)).ker.IsInvertible) (a : Bool) :
    letI := hI.isInvertible_dual_toModules
    Scheme.Pic.map (projectiveLineDiagonalChart S a).val.hom
        (Scheme.Pic.ofIsInvertible
          (Scheme.Modules.dual (pullback.diagonal (ProjectiveLine S ↘ S)).ker.toModules)) =
      Scheme.Pic.ofIsInvertible
          (ProjectiveSpace.twist (ULift.{u} (Fin 2)) (ProjectiveLine S) 1) *
        Scheme.Pic.map (ProjectiveLine (ProjectiveLine S) ↘ ProjectiveLine S)
          (Scheme.Pic.ofIsInvertible (ProjectiveSpace.twist (ULift.{u} (Fin 2)) S 1)) := by
  let := hI.isInvertible_dual_toModules
  let P := ProjectiveLine S
  let Q := Limits.pullback (P ↘ S) (P ↘ S)
  let p₁ : Q ⟶ P := pullback.fst _ _
  let p₂ : Q ⟶ P := pullback.snd _ _
  let L := twist (ULift.{u} (Fin 2)) S 1
  let A := (Scheme.Modules.pullback p₁).obj L
  let B := (Scheme.Modules.pullback p₂).obj L
  let x (k : ULift.{u} (Fin 2)) : Γ(A, ⊤) :=
    pullbackTopSection p₁ (twistOneSection (ULift.{u} (Fin 2)) S k)
  let y (k : ULift.{u} (Fin 2)) : Γ(B, ⊤) :=
    pullbackTopSection p₂ (twistOneSection (ULift.{u} (Fin 2)) S k)
  let t := tmulSection (x ⟨0⟩) (y ⟨1⟩) - tmulSection (x ⟨1⟩) (y ⟨0⟩)
  let φ := p1SectionHom (A ⊗ B) t
  have : SheafOfModules.IsInvertible.{u, u, u} (𝟙_ Q.Modules) :=
    IsInvertible.sheafOfModules_isInvertible _
  have : SheafOfModules.IsInvertible.{u, u, u} (A ⊗ B : Q.Modules) :=
    IsInvertible.sheafOfModules_isInvertible _
  have hzero : (pullback.diagonal (P ↘ S)).ker = φ.zeroLocus := by
    let C := {U : Q.affineOpens // ∃ i j : ULift.{u} (Fin 2),
      U.1 ≤ p₁ ⁻¹ᵁ standardOpen (ULift.{u} (Fin 2)) S i ∧
      U.1 ≤ p₂ ⁻¹ᵁ standardOpen (ULift.{u} (Fin 2)) S j}
    have hcov : ⨆ c : C, c.val.1 = ⊤ := by
      apply eq_top_iff.mpr
      intro z _
      obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp
        ((iSup_standardOpen (ULift.{u} (Fin 2)) S).ge (Set.mem_univ (p₁ z)))
      obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.mp
        ((iSup_standardOpen (ULift.{u} (Fin 2)) S).ge (Set.mem_univ (p₂ z)))
      obtain ⟨_, ⟨V, hV, rfl⟩, hzV, hVW⟩ :=
        Q.isBasis_affineOpens.exists_subset_of_mem_open (show z ∈
          p₁ ⁻¹ᵁ standardOpen (ULift.{u} (Fin 2)) S i ⊓
            p₂ ⁻¹ᵁ standardOpen (ULift.{u} (Fin 2)) S j from ⟨hi, hj⟩)
          (p₁ ⁻¹ᵁ standardOpen (ULift.{u} (Fin 2)) S i ⊓
            p₂ ⁻¹ᵁ standardOpen (ULift.{u} (Fin 2)) S j).2
      exact TopologicalSpace.Opens.mem_iSup.mpr
        ⟨⟨⟨V, hV⟩, i, j, hVW.trans inf_le_left, hVW.trans inf_le_right⟩, hzV⟩
    apply Scheme.IdealSheafData.ext_of_iSup_eq_top (fun c : C ↦ c.val) hcov
    intro c
    obtain ⟨i, j, hi, hj⟩ := c.property
    let U := c.val
    let xx (k : ULift.{u} (Fin 2)) :=
      A.presheaf.map (homOfLE (le_top : U.1 ≤ ⊤)).op (x k)
    let yy (k : ULift.{u} (Fin 2)) :=
      B.presheaf.map (homOfLE (le_top : U.1 ≤ ⊤)).op (y k)
    have hx : IsFreeGenerator (xx i) := by
      have h := (isFreeGenerator_pullbackSection_twistOneSection p₁ i).map hi
      simpa only [xx, x, A, L, pullbackTopSection,
        presheaf_map_homOfLE_map_homOfLE] using h
    have hy : IsFreeGenerator (yy j) := by
      have h := (isFreeGenerator_pullbackSection_twistOneSection p₂ j).map hj
      simpa only [yy, y, B, L, pullbackTopSection,
        presheaf_map_homOfLE_map_homOfLE] using h
    let r (k : ULift.{u} (Fin 2)) :=
      p₁.appLE _ U.1 hi (coordRatio (ULift.{u} (Fin 2)) S i k)
    let s (k : ULift.{u} (Fin 2)) :=
      p₂.appLE _ U.1 hj (coordRatio (ULift.{u} (Fin 2)) S j k)
    have hxx (k) : xx k = r k • xx i := coordinate_restrict p₁ i k U.1 hi
    have hyy (k) : yy k = s k • yy j := coordinate_restrict p₂ j k U.1 hj
    have ht : φ.app U.1 (1 : Γ(Q, U.1)) =
        (r ⟨0⟩ * s ⟨1⟩ - r ⟨1⟩ * s ⟨0⟩) • tmulSection (xx i) (yy j) := by
      rw [p1SectionHom_app_one]
      simp only [t, map_sub, tmulSection_map]
      change tmulSection (xx ⟨0⟩) (yy ⟨1⟩) -
        tmulSection (xx ⟨1⟩) (yy ⟨0⟩) = _
      rw [hxx ⟨0⟩, hxx ⟨1⟩, hyy ⟨0⟩, hyy ⟨1⟩]
      rw [smul_tmulSection, tmulSection_smul, smul_smul,
        smul_tmulSection, tmulSection_smul, smul_smul, sub_smul]
    rw [φ.ideal_zeroLocus U (isFreeGenerator_one U.1) (hx.tmulSection hy) ht]
    exact p1_diagonal_ideal_on_chart S i j U hi hj
  have hφ : φ.zeroLocus.IsInvertible := hzero ▸ hI
  obtain ⟨e⟩ := φ.nonempty_iso_dual_toModules_tensorObj hφ
  rw [← hzero] at e
  have hprod : Scheme.Pic.ofIsInvertible
      (Scheme.Modules.dual (pullback.diagonal (P ↘ S)).ker.toModules) =
      Scheme.Pic.map p₁ (Scheme.Pic.ofIsInvertible L) *
        Scheme.Pic.map p₂ (Scheme.Pic.ofIsInvertible L) := by
    rw [pic_map_ofIsInvertible, pic_map_ofIsInvertible,
      ← Scheme.Pic.ofIsInvertible_tensorObj]
    exact Scheme.Pic.ofIsInvertible_eq_of_iso (e ≪≫ ρ_ _).symm
  change Scheme.Pic.map (projectiveLineDiagonalChart S a).val.hom
      (Scheme.Pic.ofIsInvertible
        (Scheme.Modules.dual (pullback.diagonal (P ↘ S)).ker.toModules)) =
    Scheme.Pic.ofIsInvertible (twist (ULift.{u} (Fin 2)) P 1) *
      Scheme.Pic.map (ProjectiveLine P ↘ P) (Scheme.Pic.ofIsInvertible L)
  rw [hprod, Scheme.Pic.map_mul, ← Scheme.Pic.map_comp, ← Scheme.Pic.map_comp]
  have hm : Scheme.Pic.map (ProjectiveSpace.map (ULift.{u} (Fin 2)) (P ↘ S))
      (Scheme.Pic.ofIsInvertible L) =
        Scheme.Pic.ofIsInvertible (twist (ULift.{u} (Fin 2)) P 1) := by
    rw [pic_map_ofIsInvertible]
    exact Scheme.Pic.ofIsInvertible_eq_of_iso
      (pullbackMapTwistIso (ULift.{u} (Fin 2)) (P ↘ S) 1)
  cases a with
  | false =>
    have hfst := (isPullback_map (ULift.{u} (Fin 2)) (P ↘ S)).flip.isoPullback_hom_fst
    have hsnd := (isPullback_map (ULift.{u} (Fin 2)) (P ↘ S)).flip.isoPullback_hom_snd
    dsimp only [projectiveLineDiagonalChart, p₁, p₂]
    rw [hfst, hsnd, hm, mul_comm]
  | true =>
    have hfst := (isPullback_map (ULift.{u} (Fin 2)) (P ↘ S)).isoPullback_hom_fst
    have hsnd := (isPullback_map (ULift.{u} (Fin 2)) (P ↘ S)).isoPullback_hom_snd
    dsimp only [projectiveLineDiagonalChart, p₁, p₂]
    rw [hfst, hsnd, hm]

end AlgebraicGeometry.Etale
