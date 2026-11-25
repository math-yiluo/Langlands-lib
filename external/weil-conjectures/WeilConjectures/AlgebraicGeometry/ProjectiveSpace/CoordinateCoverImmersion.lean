/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.AffineImmersion
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.CoordinateCover

/-!
# Coordinate covers by affine charts give immersions into projective space

Let `X` be locally of finite type over an affine scheme `S` and let `𝒟` be a coordinate cover of
`X` by finitely many affine charts, i.e. an invertible module `L` with finitely many sections
`Tᵢ` whose non-vanishing loci `Uᵢ` are affine and cover `X`: `L` is ample. Then `X` admits an
immersion over `S` into a projective space `ℙ(β; S)` with `β` finite (EGA II, 4.5.2; Stacks,
Tag 01VS for the field case).

The proof is the classical one. Each ring `Γ(Uᵢ)` is generated over `Γ(S)` by finitely many
functions `gᵢ,μ`; by the extension lemma `AlgebraicGeometry.Scheme.CoordinateCover.exists_section`
each `gᵢ,μ` is the restriction to `Uᵢ` of a section of `L^{⊗ N}`, for a common `N`. The sections
`Tᵢᴺ` and these extensions define a morphism `X ⟶ ℙ(β; S)`, under which `Uᵢ` is the preimage of
the standard open of the coordinate `Tᵢᴺ`, and `Uᵢ` maps to that standard open by a closed
immersion, since the coordinates generate `Γ(Uᵢ)`.

## Main statements

- `AlgebraicGeometry.Scheme.CoordinateCover.exists_isImmersion`: a scheme locally of finite type
  over an affine scheme with a finite coordinate cover by affine charts admits an immersion into
  projective space.

## Implementation details

In `exists_isAffineOpen_preimage_of_isImmersion`, the morphism `ψ` is given by sections of
`j^* 𝒪(N)` whose non-vanishing loci are the preimages of basic opens `D(r) ⊆ D₊(Tᵢ)` contained in
the open in which `j(X)` is closed; they exist by the extension lemma.
-/

@[expose] public section

universe u

open CategoryTheory Limits TopologicalSpace

noncomputable section

namespace AlgebraicGeometry.Scheme.CoordinateCover

variable {X : Scheme.{u}} {ι : Type u} (𝒟 : X.CoordinateCover ι)

/-- The locus where a positive power of a coordinate section does not vanish is its chart. -/
lemma nonvanishing_coordPow (l : ι) {n : ℕ} (hn : 0 < n) :
    (𝒟.coordPow l n).nonvanishing = 𝒟.U l := by
  refine le_antisymm (iSup_le fun i ↦ ?_) ?_
  · rw [coordPow_s, Scheme.basicOpen_pow _ _ hn, 𝒟.basicOpen_ratio]
    exact inf_le_right
  · rw [← inf_eq_right.mpr (le_top : 𝒟.U l ≤ ⊤), ← 𝒟.iSup_U, iSup_inf_eq]
    refine iSup_le fun i ↦ ?_
    rw [← 𝒟.basicOpen_ratio, ← Scheme.basicOpen_pow _ _ hn, ← coordPow_s]
    exact le_iSup (fun i ↦ X.basicOpen ((𝒟.coordPow l n).s i)) i

/-- On an affine chart, finitely many functions generate the ring of functions over an affine
base `S`. -/
lemma exists_generators {S : Scheme.{u}} [IsAffine S] (g : X ⟶ S) [LocallyOfFiniteType g]
    (i : ι) (hi : IsAffineOpen (𝒟.U i)) :
    ∃ (m : Type u) (_ : Finite m) (t : m → Γ(X, 𝒟.U i)),
      Subring.closure (Set.range ((𝒟.U i).ι ≫ g).appTop ∪
        Set.range fun μ ↦ (𝒟.U i).topIso.inv (t μ)) = ⊤ := by
  have : IsAffine (𝒟.U i).toScheme := hi
  let : Algebra Γ(S, ⊤) Γ((𝒟.U i).toScheme, ⊤) := ((𝒟.U i).ι ≫ g).appTop.hom.toAlgebra
  have hft : ((𝒟.U i).ι ≫ g).appTop.hom.FiniteType :=
    HasRingHomProperty.iff_of_isAffine.mp (inferInstance : LocallyOfFiniteType ((𝒟.U i).ι ≫ g))
  obtain ⟨s, hs⟩ := hft.out
  refine ⟨s, inferInstance, fun μ ↦ (𝒟.U i).topIso.hom μ.1, ?_⟩
  have h := congrArg Subalgebra.toSubring hs
  rw [Algebra.adjoin_eq_ring_closure] at h
  have e : (Set.range fun μ : s ↦ (𝒟.U i).topIso.inv ((𝒟.U i).topIso.hom μ.1)) = ↑s := by
    rw [show (fun μ : s ↦ (𝒟.U i).topIso.inv ((𝒟.U i).topIso.hom μ.1)) = fun μ ↦ μ.1 from
      funext fun μ ↦ Iso.hom_inv_id_apply _ _]
    ext x
    simp
  rw [e]
  exact h

/-- **A finite coordinate cover by affine charts gives an immersion into projective space.**
Let `X` be locally of finite type over an affine scheme `S`, and let `𝒟` be a coordinate cover
of `X` by finitely many affine charts. Then `X` admits an immersion over `S` into a projective
space `ℙ(β; S)` with `β` finite. -/
theorem exists_isImmersion {S : Scheme.{u}} [IsAffine S] (g : X ⟶ S) [LocallyOfFiniteType g]
    [Finite ι] (h𝒟 : ∀ i, IsAffineOpen (𝒟.U i)) :
    ∃ (β : Type u) (_ : Finite β) (j : X ⟶ ℙ(β; S)), IsImmersion j ∧ j ≫ ℙ(β; S) ↘ S = g := by
  classical
  have := Fintype.ofFinite ι
  choose m hm t ht using fun i ↦ 𝒟.exists_generators g i (h𝒟 i)
  have hU (i : ι) : IsCompact (𝒟.U i : Set X) := (h𝒟 i).isCompact
  have hU' (i : ι) : IsQuasiSeparated (𝒟.U i : Set X) := (h𝒟 i).isQuasiSeparated
  choose N₀ hN₀ using fun p : Σ i, m i ↦ 𝒟.exists_section hU hU' p.1 (t p.1 p.2)
  have : Finite (Σ i, m i) := inferInstance
  have := Fintype.ofFinite (Σ i, m i)
  set N := max 1 (Finset.univ.sup N₀)
  have hN (p : Σ i, m i) : N ≥ N₀ p :=
    (Finset.le_sup (Finset.mem_univ p)).trans (le_max_right _ _)
  choose σ' hσ' using fun p ↦ hN₀ p N (hN p)
  let β : Type u := ι ⊕ (Σ i, m i)
  let σ : β → 𝒟.Section N := Sum.elim (fun i ↦ 𝒟.coordPow i N) σ'
  have hσ (j : ι) : Ideal.span (Set.range fun a ↦ (σ a).s j) = ⊤ := by
    refine Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span ⟨Sum.inl j, rfl⟩) ?_
    simp [σ, 𝒟.ratio_self]
  let Φ := hom σ hσ g
  have hpre (i : ι) : Φ ⁻¹ᵁ ProjectiveSpace.standardOpen β S (Sum.inl i) = 𝒟.U i := by
    rw [preimage_hom_standardOpen]
    exact 𝒟.nonvanishing_coordPow i (lt_of_lt_of_le one_pos (le_max_left _ _))
  refine ⟨β, inferInstance, Φ, ?_, hom_over σ hσ g⟩
  refine IsZariskiLocalAtTarget.of_range_subset_iSup
    (fun i : ι ↦ ProjectiveSpace.standardOpen β S (Sum.inl i)) ?_ fun i ↦ ?_
  · rintro _ ⟨x, rfl⟩
    obtain ⟨i, hi⟩ := Opens.mem_iSup.mp (𝒟.iSup_U.ge (Set.mem_univ x))
    refine SetLike.mem_coe.mpr (Opens.mem_iSup.mpr ⟨i, ?_⟩)
    change x ∈ Φ ⁻¹ᵁ ProjectiveSpace.standardOpen β S (Sum.inl i)
    rw [hpre i]
    exact hi
  · -- the chart `Uᵢ ⟶ D₊(Tᵢᴺ)`
    rw [← Scheme.Hom.resLE_eq_morphismRestrict,
      Scheme.Hom.resLE_congr Φ (U := ProjectiveSpace.standardOpen β S (Sum.inl i)) le_rfl rfl
        (hpre i) @IsImmersion]
    have : IsAffine (𝒟.U i).toScheme := h𝒟 i
    set V := (𝒟.U i).toScheme
    set s : β → Γ(V, ⊤) := fun a ↦ (𝒟.U i).topIso.inv ((σ a).s i)
    have hs1 : s (Sum.inl i) = 1 := by simp [s, σ, 𝒟.ratio_self]
    have hb : V.basicOpen (s (Sum.inl i)) = ⊤ := by rw [hs1]; exact V.basicOpen_one
    have : IsIso (V.basicOpen (s (Sum.inl i))).ι := by
      rw [← V.isoOfEq_hom_ι hb, ← Scheme.topIso_hom]
      infer_instance
    have hloc : (V.basicOpen (s (Sum.inl i))).ι ≫
        Φ.resLE (ProjectiveSpace.standardOpen β S (Sum.inl i)) (𝒟.U i) (hpre i).ge =
        (ProjectiveSpace.homOfSections ((𝒟.U i).ι ≫ g) s (span_topIso_inv σ hσ i)).resLE
          (ProjectiveSpace.standardOpen β S (Sum.inl i)) (V.basicOpen (s (Sum.inl i)))
          (ProjectiveSpace.homOfSections_preimage_standardOpen _ s _ (Sum.inl i)).ge := by
      rw [← cancel_mono (ProjectiveSpace.standardOpen β S (Sum.inl i)).ι, Category.assoc,
        Scheme.Hom.resLE_comp_ι, Scheme.Hom.resLE_comp_ι, ι_hom]
      rfl
    rw [← MorphismProperty.cancel_left_of_respectsIso @IsImmersion
      (V.basicOpen (s (Sum.inl i))).ι, hloc,
      ← MorphismProperty.cancel_right_of_respectsIso @IsImmersion _
        (ProjectiveSpace.standardOpenIso β S (Sum.inl i)).hom,
      ProjectiveSpace.homOfSections_resLE_standardOpenIso_hom]
    refine isImmersion_homOfVector_divBasicOpen ((𝒟.U i).ι ≫ g) s (Sum.inl i) ⊤
      (isAffineOpen_top S) (by simp) ?_
    -- generation of the ring of functions of the chart
    set ρ := (V.basicOpen (s (Sum.inl i))).ι.appTop
    have hρ : Function.Surjective ρ.hom := by
      have : IsIso ρ := inferInstance
      exact (ConcreteCategory.bijective_of_isIso ρ).2
    have hdiv (a : β) : V.divBasicOpen (s a) (s (Sum.inl i)) = ρ (s a) := by
      symm
      refine V.eq_divBasicOpen ?_
      have h1 : ∀ x : Γ(V, ⊤), x = 1 → ρ x = 1 := by rintro x rfl; exact map_one _
      rw [h1 _ hs1, mul_one]
    refine eq_top_iff.mpr ?_
    rw [← (RingHom.range_eq_top.mpr hρ), RingHom.range_eq_map, ← ht i, RingHom.map_closure]
    refine Subring.closure_mono ?_
    rintro _ ⟨x, (⟨r, rfl⟩ | ⟨μ, rfl⟩), rfl⟩
    · refine Or.inl ⟨(⊤ : S.Opens).ι.appTop r, ?_⟩
      rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop,
        ← Scheme.Hom.comp_appTop, Scheme.Hom.resLE_comp_ι]
    · refine Or.inr ⟨⟨Sum.inr ⟨i, μ⟩, Sum.inr_ne_inl⟩, ?_⟩
      refine (hdiv (Sum.inr ⟨i, μ⟩)).trans ?_
      simp only [s, σ, Sum.elim_inr, (hσ' ⟨i, μ⟩).1]

end AlgebraicGeometry.Scheme.CoordinateCover

namespace AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

/-- **An immersion into projective space can be replaced by a morphism with affine preimages of
the standard opens.** Let `j : X ⟶ ℙ(α; S)` be a quasi-compact immersion over an affine scheme
`S`, with `X` quasi-compact and quasi-separated. Then there is a morphism `ψ : X ⟶ ℙ(β; S)` over
`S`, with `β` finite, such that the preimage of every standard open `D₊(T_b)` is affine; i.e. the
pullback of `𝒪(1)` along `j` is ample (EGA II, 4.5.2). -/
theorem exists_isAffineOpen_preimage_of_isImmersion {X S : Scheme.{u}} [IsAffine S]
    {α : Type u} [Finite α] (j : X ⟶ ℙ(α; S)) [IsImmersion j] [QuasiCompact j] [CompactSpace X]
    [QuasiSeparatedSpace X] :
    ∃ (β : Type u) (_ : Finite β) (ψ : X ⟶ ℙ(β; S)),
      ψ ≫ ℙ(β; S) ↘ S = j ≫ ℙ(α; S) ↘ S ∧
        ∀ b, IsAffineOpen (ψ ⁻¹ᵁ ProjectiveSpace.standardOpen β S b) := by
  classical
  let ρ := j ≫ ProjectiveSpace.toProjInt α S
  have hX (i : α) : MvPolynomial.X i ∈
      MvPolynomial.homogeneousSubmodule α (ULift.{u} ℤ) 1 :=
    MvPolynomial.X_mem_homogeneousSubmodule_one _ i
  have hpre (i : α) : ρ ⁻¹ᵁ Proj.basicOpen (MvPolynomial.homogeneousSubmodule α (ULift.{u} ℤ))
      (MvPolynomial.X i) = j ⁻¹ᵁ ProjectiveSpace.standardOpen α S i := rfl
  have hcov : ⨆ i, ρ ⁻¹ᵁ Proj.basicOpen (MvPolynomial.homogeneousSubmodule α (ULift.{u} ℤ))
      (MvPolynomial.X i) = ⊤ := by
    simp only [hpre]
    rw [← Scheme.Hom.preimage_iSup, ProjectiveSpace.iSup_standardOpen, Scheme.Hom.preimage_top]
  let 𝒟 := Scheme.CoordinateCover.ofProj _ ρ one_pos _ hX hcov
  have hU (i : α) : IsCompact (𝒟.U i : Set X) :=
    QuasiCompact.isCompact_preimage (f := j) _ (ProjectiveSpace.standardOpen α S i).2
      (ProjectiveSpace.isAffineOpen_standardOpen α S i).isCompact
  have hU' (i : α) : IsQuasiSeparated (𝒟.U i : Set X) := .of_quasiSeparatedSpace _
  -- around every point, a basic open of a chart inside the open in which `j(X)` is closed
  have key (x : X) : ∃ (i : α) (r : Γ(ℙ(α; S), ProjectiveSpace.standardOpen α S i)),
      x ∈ j ⁻¹ᵁ ℙ(α; S).basicOpen r ∧ ℙ(α; S).basicOpen r ≤ j.coborderRange := by
    obtain ⟨i, hi⟩ := Opens.mem_iSup.mp (hcov.ge (Set.mem_univ x))
    obtain ⟨r, hr, hrO⟩ :=
      (ProjectiveSpace.isAffineOpen_standardOpen α S i).exists_basicOpen_le_of_finite
      (inf_le_left : ProjectiveSpace.standardOpen α S i ⊓ j.coborderRange ≤ _)
      (Set.finite_singleton (j x)) (by
        rw [Set.singleton_subset_iff]
        exact ⟨hi, subset_coborder ⟨x, rfl⟩⟩)
    exact ⟨i, r, hr rfl, hrO.trans inf_le_right⟩
  choose i r hxr hrO using key
  have hext (x : X) := 𝒟.exists_section hU hU' (i x) (j.app _ (r x))
  choose N₀ hN₀ using hext
  obtain ⟨t, ht⟩ := CompactSpace.elim_nhds_subcover
    (fun x ↦ (j ⁻¹ᵁ ℙ(α; S).basicOpen (r x) : Set X))
    fun x ↦ (j ⁻¹ᵁ ℙ(α; S).basicOpen (r x)).isOpen.mem_nhds (hxr x)
  set N := t.sup N₀
  have hσ (x : t) := hN₀ x N (Finset.le_sup x.2)
  choose σ hσs hσU using hσ
  have hnv (x : t) : (σ x).nonvanishing = j ⁻¹ᵁ ℙ(α; S).basicOpen (r x) := by
    rw [Scheme.CoordinateCover.nonvanishing_eq_basicOpen σ (fun x ↦ i x) hσU, hσs,
      Scheme.preimage_basicOpen]
  have hcov' : ⨆ x : t, (σ x).nonvanishing = ⊤ := by
    refine top_le_iff.mp fun y _ ↦ ?_
    obtain ⟨x, hx, hy⟩ := Set.mem_iUnion₂.mp (ht.ge (Set.mem_univ y))
    exact Opens.mem_iSup.mpr ⟨⟨x, hx⟩, by rw [hnv]; exact hy⟩
  let 𝒟' := Scheme.CoordinateCover.ofSections σ (fun x ↦ i x) hσU hcov'
  have hgen (a : t) : Ideal.span (Set.range fun b ↦ (𝒟'.coordPow b 1).s a) = ⊤ :=
    Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span ⟨a, rfl⟩) (by simp [𝒟'.ratio_self])
  refine ⟨t, inferInstance, Scheme.CoordinateCover.hom _ hgen (j ≫ ℙ(α; S) ↘ S), by simp,
    fun b ↦ ?_⟩
  rw [Scheme.CoordinateCover.preimage_hom_standardOpen,
    Scheme.CoordinateCover.nonvanishing_coordPow _ _ one_pos,
    Scheme.CoordinateCover.ofSections_U, hnv]
  exact j.isAffineOpen_preimage_of_le_coborderRange
    ((ProjectiveSpace.isAffineOpen_standardOpen α S _).basicOpen _) (hrO b)

end AlgebraicGeometry
