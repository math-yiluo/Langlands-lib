/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import WeilConjectures.AlgebraicGeometry.BaseChangeNorm
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.CoordinateCover
public import WeilConjectures.Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Topology

/-!
# Descending ample coordinate covers along a finite field extension

Let `k'/k` be a finite field extension, `X` a `k`-scheme and `π : Y = X ×_k k' ⟶ X` the base
change. Let `𝒟` be a coordinate cover of `Y` by affine charts `Uᵢ` such that every fibre of `π`
lies in one chart. Then the opens `Wᵢ = {x | π⁻¹ x ⊆ Uᵢ}` of `X` are affine and, with the norms
`N(tᵢⱼ)` of the ratios of `𝒟` as ratios, form a coordinate cover of `X`: the norm of an ample
invertible module is ample (Stacks, Tag 0BCX, in the form used for Tag 0BDE).

As an application, a `k`-scheme `X` whose base change `X_{k'}` admits a morphism to projective
space with affine preimages of the standard opens has a finite coordinate cover by affine charts.
The fibre condition is achieved with forms over `ℤ` by graded prime avoidance.

## Main statements

- `AlgebraicGeometry.Scheme.CoordinateCover.exists_descent`: the descent of coordinate covers.
- `AlgebraicGeometry.exists_coordinateCover_of_isPullback`: a coordinate cover by affine charts on
  `X` from a morphism `X_{k'} ⟶ ℙ(β; k')` with affine preimages of the standard opens.
-/

@[expose] public section

universe u

open CategoryTheory Limits TopologicalSpace

noncomputable section

namespace AlgebraicGeometry

variable {k k' : Type u} [Field k] [Field k'] [Algebra k k'] [Module.Finite k k']
  {X Y : Scheme.{u}} {f : X ⟶ Spec (.of k)} {π : Y ⟶ X} {q : Y ⟶ Spec (.of k')}
  (H : IsPullback π q f (Spec.map (CommRingCat.ofHom (algebraMap k k'))))

namespace Scheme.CoordinateCover

variable {ι : Type u} (𝒟 : Y.CoordinateCover ι)

include H in
/-- The open `{x | π⁻¹ x ⊆ V}` of points all of whose preimages lie in the open `V`. -/
def saturatedPart (V : Y.Opens) : X.Opens :=
  ⟨(π '' (V : Set Y)ᶜ)ᶜ, by
    have := isFinite_of_isPullback_spec H
    exact (π.isClosedMap _ V.isOpen.isClosed_compl).isOpen_compl⟩

lemma mem_saturatedPart {V : Y.Opens} {x : X} :
    x ∈ saturatedPart H V ↔ ∀ y, π y = x → y ∈ V := by
  change x ∉ π '' (V : Set Y)ᶜ ↔ _
  simp only [Set.mem_image, Set.mem_compl_iff, SetLike.mem_coe, not_exists, not_and]
  exact ⟨fun h y hy ↦ by_contra fun h' ↦ h y h' hy, fun h y h' hy ↦ h' (h y hy)⟩

lemma preimage_saturatedPart_le (V : Y.Opens) : π ⁻¹ᵁ saturatedPart H V ≤ V :=
  fun y hy ↦ (mem_saturatedPart H).mp hy y rfl

/-- The ratio `N(tᵢⱼ)` of the descended coordinate cover. -/
def normRatio (𝒟 : Y.CoordinateCover ι) (i j : ι) : Γ(X, saturatedPart H (𝒟.U i)) :=
  π.normAt _ (Y.presheaf.map (homOfLE (preimage_saturatedPart_le H (𝒟.U i))).op (𝒟.ratio i j))

variable {𝒟} (h𝒟 : ∀ i, IsAffineOpen (𝒟.U i))
  (hfib : ∀ x : X, ∃ i, ∀ y, π y = x → y ∈ 𝒟.U i)

include h𝒟 hfib in
/-- The preimage of `{x | π⁻¹ x ⊆ Uᵢ}` is affine: it is affine over the affine chart `Uᵢ`, being
a basic open, over the affine opens `π⁻¹ A` for `A ⊆ {x | π⁻¹ x ⊆ Uⱼ}` affine, of the pullback of
the norm of `tⱼᵢ`. -/
lemma isAffineOpen_preimage_saturatedPart (i : ι) :
    IsAffineOpen (π ⁻¹ᵁ saturatedPart H (𝒟.U i)) := by
  have := isFinite_of_isPullback_spec H
  set Z := π ⁻¹ᵁ saturatedPart H (𝒟.U i)
  -- the affine opens of `X` inside some `{x | π⁻¹ x ⊆ Uⱼ}`
  let C : Type u := {A : X.Opens // IsAffineOpen A ∧ ∃ j, A ≤ saturatedPart H (𝒟.U j)}
  have hC (A : C) : IsAffineOpen (Z ⊓ π ⁻¹ᵁ A.1) := by
    obtain ⟨hA, j, hAj⟩ := A.2
    have hA' : IsAffineOpen (π ⁻¹ᵁ A.1) := hA.preimage π
    have hle : π ⁻¹ᵁ A.1 ≤ 𝒟.U j := (π.preimage_mono hAj).trans (preimage_saturatedPart_le H _)
    set N := π.normAt A.1 (Y.presheaf.map (homOfLE hle).op (𝒟.ratio j i))
    have : Z ⊓ π ⁻¹ᵁ A.1 = Y.basicOpen (π.app A.1 N) := by
      rw [← Scheme.preimage_basicOpen]
      ext y
      change π y ∈ saturatedPart H (𝒟.U i) ∧ π y ∈ A.1 ↔ π y ∈ X.basicOpen N
      refine ⟨fun ⟨hy, hyA⟩ ↦ ?_, fun hy ↦ ?_⟩
      · refine (mem_basicOpen_normAt H hA _ hyA).mpr fun y' hy' ↦ ?_
        rw [Scheme.basicOpen_res, 𝒟.basicOpen_ratio]
        have hy'A : y' ∈ π ⁻¹ᵁ A.1 := by change π y' ∈ A.1; rw [hy']; exact hyA
        exact ⟨hy'A, hle hy'A, (mem_saturatedPart H).mp hy y' hy'⟩
      · have hyA : π y ∈ A.1 := X.basicOpen_le N hy
        refine ⟨(mem_saturatedPart H).mpr fun y' hy' ↦ ?_, hyA⟩
        have := (mem_basicOpen_normAt H hA _ hyA).mp hy y' hy'
        rw [Scheme.basicOpen_res, 𝒟.basicOpen_ratio] at this
        exact this.2.2
    rw [this]
    exact hA'.basicOpen _
  -- `Z ⟶ Y` is affine, by the affine cover `π⁻¹ A` of `Y`
  have hcov : ⨆ A : C, (⟨π ⁻¹ᵁ A.1, A.2.1.preimage π⟩ : Y.affineOpens).1 = ⊤ := by
    refine top_le_iff.mp fun y _ ↦ ?_
    obtain ⟨j, hj⟩ := hfib (π y)
    obtain ⟨_, ⟨A, hA, rfl⟩, hyA, hAj⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
      (a := π y) ((mem_saturatedPart H).mpr hj) (saturatedPart H (𝒟.U j)).isOpen
    exact Opens.mem_iSup.mpr ⟨⟨A, hA, j, hAj⟩, hyA⟩
  have hZ : IsAffineHom Z.ι := by
    refine HasAffineProperty.of_iSup_eq_top (P := @IsAffineHom)
      (fun A : C ↦ (⟨π ⁻¹ᵁ A.1, A.2.1.preimage π⟩ : Y.affineOpens)) hcov fun A ↦ ?_
    change IsAffine (Z.ι ⁻¹ᵁ π ⁻¹ᵁ A.1).toScheme
    have : IsAffineOpen (Z.ι ''ᵁ (Z.ι ⁻¹ᵁ π ⁻¹ᵁ A.1)) := by
      rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
      exact hC A
    exact (Z.ι.isAffineOpen_iff_of_isOpenImmersion).mp this
  -- hence `Z ⟶ Uᵢ` is affine, and `Z` is affine
  have hZi : IsAffineHom (Y.homOfLE (preimage_saturatedPart_le H (𝒟.U i))) := by
    refine ⟨fun V hV ↦ ?_⟩
    have h := ((𝒟.U i).ι.isAffineOpen_iff_of_isOpenImmersion.mpr hV).preimage Z.ι
    have e : Y.homOfLE (preimage_saturatedPart_le H (𝒟.U i)) ⁻¹ᵁ V =
        Z.ι ⁻¹ᵁ (𝒟.U i).ι ''ᵁ V := by
      rw [← Scheme.homOfLE_ι _ (preimage_saturatedPart_le H _), Scheme.Hom.comp_preimage,
        Scheme.Hom.preimage_image_eq]
    rw [e]
    exact h
  have : IsAffine (𝒟.U i).toScheme := h𝒟 i
  exact isAffine_of_isAffineHom (Y.homOfLE (preimage_saturatedPart_le H (𝒟.U i)))

include h𝒟 hfib in
lemma isAffineOpen_saturatedPart (i : ι) : IsAffineOpen (saturatedPart H (𝒟.U i)) :=
  isAffineOpen_of_isAffineOpen_preimage H (isAffineOpen_preimage_saturatedPart H h𝒟 hfib i)

include h𝒟 hfib in
lemma basicOpen_normRatio (i j : ι) :
    X.basicOpen (normRatio H 𝒟 i j) = saturatedPart H (𝒟.U i) ⊓ saturatedPart H (𝒟.U j) := by
  have hW := isAffineOpen_saturatedPart H h𝒟 hfib i
  ext x
  refine ⟨fun hx ↦ ⟨X.basicOpen_le _ hx, ?_⟩, fun ⟨hxi, hxj⟩ ↦ ?_⟩
  · have := (mem_basicOpen_normAt H hW _ (X.basicOpen_le _ hx)).mp hx
    refine (mem_saturatedPart H).mpr fun y hy ↦ ?_
    have h := this y hy
    rw [Scheme.basicOpen_res, 𝒟.basicOpen_ratio] at h
    exact h.2.2
  · refine (mem_basicOpen_normAt H hW _ hxi).mpr fun y hy ↦ ?_
    rw [Scheme.basicOpen_res, 𝒟.basicOpen_ratio]
    have hyW : y ∈ π ⁻¹ᵁ saturatedPart H (𝒟.U i) := by
      rw [Scheme.Hom.mem_preimage, hy]; exact hxi
    exact ⟨hyW, preimage_saturatedPart_le H _ hyW, (mem_saturatedPart H).mp hxj y hy⟩

include H h𝒟 hfib in
/-- **Descent of coordinate covers along a finite field extension.** If `𝒟` is a coordinate
cover of `Y = X ×_k k'` by affine charts and every fibre of `π` lies in a chart, then `X` has a
coordinate cover by affine charts, with the same index type. -/
theorem exists_descent : ∃ 𝒟' : X.CoordinateCover ι, ∀ i, IsAffineOpen (𝒟'.U i) := by
  refine ⟨{ U := fun i ↦ saturatedPart H (𝒟.U i)
            ratio := normRatio H 𝒟
            ratio_self := fun i ↦ by simp [normRatio, 𝒟.ratio_self]
            basicOpen_ratio := basicOpen_normRatio H h𝒟 hfib
            ratio_mul := fun i j l ↦ ?_
            iSup_U := ?_ }, isAffineOpen_saturatedPart H h𝒟 hfib⟩
  · set V := saturatedPart H (𝒟.U i) ⊓ saturatedPart H (𝒟.U j)
    have hVi : V = X.basicOpen (normRatio H 𝒟 i j) := (basicOpen_normRatio H h𝒟 hfib i j).symm
    have hVj : V = X.basicOpen (normRatio H 𝒟 j i) := by
      rw [basicOpen_normRatio H h𝒟 hfib j i, inf_comm]
    have hi := isAffineOpen_saturatedPart H h𝒟 hfib i
    have hj := isAffineOpen_saturatedPart H h𝒟 hfib j
    rw [normRatio, normRatio, normRatio,
      ← normAt_map_of_eq_basicOpen H hi _ hVi, ← normAt_map_of_eq_basicOpen H hi _ hVi,
      ← normAt_map_of_eq_basicOpen H hj _ hVj, ← map_mul]
    congr 1
    have hle : π ⁻¹ᵁ V ≤ 𝒟.U i ⊓ 𝒟.U j :=
      le_inf ((π.preimage_mono inf_le_left).trans (preimage_saturatedPart_le H _))
        ((π.preimage_mono inf_le_right).trans (preimage_saturatedPart_le H _))
    have := congrArg (Y.presheaf.map (homOfLE hle).op) (𝒟.ratio_mul i j l)
    simp only [map_mul, Scheme.presheaf_map_map] at this ⊢
    exact this
  · refine top_le_iff.mp fun x _ ↦ ?_
    obtain ⟨i, hi⟩ := hfib x
    exact Opens.mem_iSup.mpr ⟨i, (mem_saturatedPart H).mpr hi⟩

end Scheme.CoordinateCover

attribute [local instance] MvPolynomial.gradedAlgebra

include H in
/-- **Ample coordinate covers descend along a finite field extension.** Let `X` be a
quasi-compact `k`-scheme and `ψ : X_{k'} ⟶ ℙ(β; k')` a morphism such that the preimages of the
standard opens are affine. Then `X` has a finite coordinate cover by affine charts. -/
theorem exists_coordinateCover_of_isPullback [CompactSpace X] {β : Type u}
    (ψ : Y ⟶ ℙ(β; Spec (.of k')))
    (hψ : ∀ b, IsAffineOpen (ψ ⁻¹ᵁ ProjectiveSpace.standardOpen β (Spec (.of k')) b)) :
    ∃ (ι : Type u) (_ : Finite ι) (𝒟 : X.CoordinateCover ι), ∀ i, IsAffineOpen (𝒟.U i) := by
  classical
  have := isFinite_of_isPullback_spec H
  have hψa : IsAffineHom ψ := HasAffineProperty.of_iSup_eq_top (P := @IsAffineHom)
    (fun b ↦ ⟨_, ProjectiveSpace.isAffineOpen_standardOpen β (Spec (.of k')) b⟩)
    (ProjectiveSpace.iSup_standardOpen _ _) fun b ↦ hψ b
  have hτ : IsAffineHom (ProjectiveSpace.toProjInt β (Spec (.of k'))) :=
    MorphismProperty.pullback_snd (P := @IsAffineHom) _ _ inferInstance
  set 𝒜 := MvPolynomial.homogeneousSubmodule β (ULift.{u} ℤ)
  let ρ := ψ ≫ ProjectiveSpace.toProjInt β (Spec (.of k'))
  have hρ {d : ℕ} (hd : 0 < d) {G : MvPolynomial β (ULift.{u} ℤ)} (hG : G ∈ 𝒜 d) :
      IsAffineOpen (ρ ⁻¹ᵁ Proj.basicOpen 𝒜 G) :=
    ((Proj.isAffineOpen_basicOpen 𝒜 G hG hd).preimage _).preimage ψ
  -- a form not vanishing on a given fibre
  have key (x : X) : ∃ d > 0, ∃ G ∈ 𝒜 d, ∀ y, π y = x → y ∈ ρ ⁻¹ᵁ Proj.basicOpen 𝒜 G := by
    have hfin : (π ⁻¹' {x}).Finite := π.finite_preimage_singleton x
    obtain ⟨d, hd, G, hG, hGs⟩ :=
      ProjectiveSpectrum.exists_homogeneous_notMem_of_finset (hfin.toFinset.image ρ)
    exact ⟨d, hd, G, hG, fun y hy ↦ hGs (ρ y) (Finset.mem_image_of_mem _ (by simpa using hy))⟩
  choose d hd G hG hGx using key
  obtain ⟨t, ht⟩ := CompactSpace.elim_nhds_subcover
    (fun x ↦ (Scheme.CoordinateCover.saturatedPart H (ρ ⁻¹ᵁ Proj.basicOpen 𝒜 (G x)) : Set X))
    fun x ↦ (Scheme.CoordinateCover.saturatedPart H _).isOpen.mem_nhds
      ((Scheme.CoordinateCover.mem_saturatedPart H).mpr (hGx x))
  set D := ∏ x ∈ t, d x
  have hdD (x : t) : d x ∣ D := Finset.dvd_prod_of_mem _ x.2
  have hD : 0 < D := Finset.prod_pos fun x _ ↦ hd x
  let F : t → MvPolynomial β (ULift.{u} ℤ) := fun x ↦ G x ^ (D / d x)
  have hF (x : t) : F x ∈ 𝒜 D := by
    have := SetLike.pow_mem_graded (D / d x) (hG x)
    rwa [smul_eq_mul, Nat.div_mul_cancel (hdD x)] at this
  have hFb (x : t) : Proj.basicOpen 𝒜 (F x) = Proj.basicOpen 𝒜 (G x) :=
    Proj.basicOpen_pow _ _ _ (Nat.div_pos (Nat.le_of_dvd hD (hdD x)) (hd x))
  -- every fibre lies in one of the charts
  have hfib (x' : X) : ∃ i : t, ∀ y, π y = x' → y ∈ ρ ⁻¹ᵁ Proj.basicOpen 𝒜 (F i) := by
    obtain ⟨x, hx, hx'⟩ := Set.mem_iUnion₂.mp (ht.ge (Set.mem_univ x'))
    refine ⟨⟨x, hx⟩, fun y hy ↦ ?_⟩
    rw [hFb]
    exact (Scheme.CoordinateCover.mem_saturatedPart H).mp hx' y hy
  have hcovY : ⨆ i : t, ρ ⁻¹ᵁ Proj.basicOpen 𝒜 (F i) = ⊤ := by
    refine top_le_iff.mp fun y _ ↦ ?_
    obtain ⟨i, hi⟩ := hfib (π y)
    exact Opens.mem_iSup.mpr ⟨i, hi y rfl⟩
  let 𝒟 := Scheme.CoordinateCover.ofProj 𝒜 ρ hD F hF hcovY
  obtain ⟨𝒟', h𝒟'⟩ := Scheme.CoordinateCover.exists_descent H (𝒟 := 𝒟)
    (fun i ↦ hρ hD (hF i)) hfib
  exact ⟨t, inferInstance, 𝒟', h𝒟'⟩

end AlgebraicGeometry
