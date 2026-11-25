/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.Blowup.EliminationOfIndeterminacy.ZeroLocus
public import WeilConjectures.Mathlib.AlgebraicGeometry.AffineSpace
public import WeilConjectures.Mathlib.AlgebraicGeometry.PullbackCarrier

/-!
# Closedness of graphs cut out by fraction equations

A morphism to relative affine space over `Spec S` defined on a union of basic opens `D(v i)` by
fractions `w i j / v i` satisfying the compatibilities `v i * w i' j = v i' * w i j` has closed
graph as soon as the `v i` and `w i j` generate the unit ideal
(`AlgebraicGeometry.AffineSpace.isClosed_range_of_basicOpen_fractions`).
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry
section GraphClosedness
namespace AffineSpace

variable {σ : Type u}

/-- **Chart-local graph closedness.** Let `v i`, `w i j` be elements of a ring `S`
generating the unit ideal and satisfying the compatibilities
`v i * w i' j = v i' * w i j`, and let `γ` be a morphism over `Spec S` from the union
`O` of the basic opens `D(v i)` to the relative affine space whose `j`-th coordinate on
`D(v i)` is the fraction `w i j / v i`. Then the range of `γ` is closed in the whole
relative affine space: it is the vanishing locus of the sections
`v̂ᵢ · coordⱼ − ŵᵢⱼ`. -/
theorem isClosed_range_of_basicOpen_fractions {S : CommRingCat.{u}} {ι : Type*}
    (v : ι → S) (w : ι → σ → S)
    (hone : (1 : S) ∈ Ideal.span (Set.range v ∪ ⋃ i, Set.range (w i)))
    (hrel : ∀ i i' j, v i * w i' j = v i' * w i j)
    {O : (Spec S).Opens} {B : ι → (Spec S).Opens}
    (hBv : ∀ i, B i = PrimeSpectrum.basicOpen (v i)) (hO : O = ⨆ i, B i)
    (γ : O.toScheme ⟶ 𝔸(σ; Spec S)) (hγ : γ ≫ 𝔸(σ; Spec S) ↘ Spec S = O.ι)
    (hB : ∀ i, B i ≤ O)
    (hcoord : ∀ i j, ((Spec S).homOfLE (hB i) ≫ γ).appTop (coord (Spec S) j) *
        ((Scheme.ΓSpecIso S).inv ≫ (B i).ι.appTop) (v i) =
        ((Scheme.ΓSpecIso S).inv ≫ (B i).ι.appTop) (w i j)) :
    IsClosed (Set.range γ) := by
  classical
  -- the pulled-back ring elements and the graph equations
  set pl : S → Γ(𝔸(σ; Spec S), ⊤) := fun e ↦
    (𝔸(σ; Spec S) ↘ Spec S).appTop ((Scheme.ΓSpecIso S).inv e) with hpl
  set E : ι → σ → Γ(𝔸(σ; Spec S), ⊤) :=
    fun i j ↦ pl (v i) * coord (Spec S) j - pl (w i j) with hE
  -- restriction of ring elements to the basic pieces
  have hres : ∀ i (e : S), ((Spec S).homOfLE (hB i) ≫ γ).appTop (pl e) =
      ((Scheme.ΓSpecIso S).inv ≫ (B i).ι.appTop) e := by
    intro i e
    simp only [hpl]
    rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, Category.assoc, hγ,
      Scheme.homOfLE_ι, CommRingCat.comp_apply]
  -- the denominators are units on their own pieces
  have hu : ∀ i, IsUnit (((Scheme.ΓSpecIso S).inv ≫ (B i).ι.appTop) (v i)) := by
    intro i
    rw [CommRingCat.comp_apply]
    refine Scheme.isUnit_of_le_basicOpen (le_of_eq ?_)
    rw [← Scheme.preimage_basicOpen_top, basicOpen_eq_of_affine, ← hBv i,
      Scheme.Opens.ι_preimage_self]
  suffices h : Set.range γ = 𝔸(σ; Spec S).zeroLocus (U := ⊤) (⋃ i, Set.range (E i)) by
    rw [h]
    exact Scheme.zeroLocus_isClosed _ _
  apply subset_antisymm
  · -- the range satisfies the graph equations
    rintro - ⟨y, rfl⟩
    rw [Scheme.mem_zeroLocus_iff]
    intro e he
    simp only [Set.mem_iUnion, Set.mem_range] at he
    obtain ⟨i, j, rfl⟩ := he
    -- `y` lies in one of the basic pieces
    have hy : y.1 ∈ ⨆ i, B i := by rw [← hO]; exact y.2
    obtain ⟨i₀, hi₀⟩ := TopologicalSpace.Opens.mem_iSup.mp hy
    obtain ⟨y', rfl⟩ := (mem_opensRange_homOfLE (hB i₀) y).mpr hi₀
    rw [← Scheme.Hom.comp_apply]
    intro hmem
    have h1 : y' ∈ ((Spec S).homOfLE (hB i₀) ≫ γ) ⁻¹ᵁ
        𝔸(σ; Spec S).basicOpen (E i j) := hmem
    rw [Scheme.preimage_basicOpen_top] at h1
    -- the pulled-back equation is annihilated by the unit `v i₀`
    have hval : ((Spec S).homOfLE (hB i₀) ≫ γ).appTop (E i j) *
        ((Scheme.ΓSpecIso S).inv ≫ (B i₀).ι.appTop) (v i₀) = 0 := by
      simp only [hE, map_sub, map_mul]
      rw [hres i₀ (v i), hres i₀ (w i j), sub_mul, mul_assoc, hcoord i₀ j,
        ← map_mul, ← map_mul, hrel i i₀ j, mul_comm (w i j) (v i₀), sub_self]
    have hz : ((Spec S).homOfLE (hB i₀) ≫ γ).appTop (E i j) = 0 :=
      ((hu i₀).mul_left_eq_zero).mp hval
    rw [hz, Scheme.basicOpen_zero] at h1
    simp at h1
  · -- the graph equations cut out the range
    intro x hx
    rw [Scheme.mem_zeroLocus_iff] at hx
    -- some denominator is invertible at `x`
    have hbase : ∃ i, x ∈ 𝔸(σ; Spec S).basicOpen (pl (v i)) := by
      by_contra hnone
      push Not at hnone
      set φ := 𝔸(σ; Spec S).presheaf.germ ⊤ x trivial with hφ
      have hgermv : ∀ i, φ (pl (v i)) ∈ IsLocalRing.maximalIdeal _ := by
        intro i
        rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
        intro hunit
        exact hnone i ((Scheme.mem_basicOpen_top _ _ x).mpr hunit)
      have hgermE : ∀ i j, φ (E i j) ∈ IsLocalRing.maximalIdeal _ := by
        intro i j
        rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
        intro hunit
        exact hx (E i j) (Set.mem_iUnion.mpr ⟨i, Set.mem_range_self j⟩)
          ((Scheme.mem_basicOpen_top _ _ x).mpr hunit)
      have hgermw : ∀ i j, φ (pl (w i j)) ∈ IsLocalRing.maximalIdeal _ := by
        intro i j
        have hwe : pl (w i j) = pl (v i) * coord (Spec S) j - E i j := by
          simp only [hE]
          ring
        rw [hwe, map_sub, map_mul]
        exact sub_mem (Ideal.mul_mem_right _ _ (hgermv i)) (hgermE i j)
      set ψ : S ⟶ 𝔸(σ; Spec S).presheaf.stalk x :=
        (Scheme.ΓSpecIso S).inv ≫ (𝔸(σ; Spec S) ↘ Spec S).appTop ≫ φ with hψ
      have hψapp : ∀ e : S, ψ e = φ (pl e) := by
        intro e
        simp only [hψ, hpl, CommRingCat.comp_apply]
      have hmap : (1 : 𝔸(σ; Spec S).presheaf.stalk x) ∈
          Ideal.map ψ.hom (Ideal.span (Set.range v ∪ ⋃ i, Set.range (w i))) := by
        simpa using Ideal.mem_map_of_mem ψ.hom hone
      rw [Ideal.map_span] at hmap
      have hle : Ideal.span (⇑ψ.hom '' (Set.range v ∪ ⋃ i, Set.range (w i))) ≤
          IsLocalRing.maximalIdeal _ := by
        rw [Ideal.span_le]
        rintro - ⟨e, he, rfl⟩
        rcases he with ⟨i, rfl⟩ | he
        · exact hψapp (v i) ▸ hgermv i
        · simp only [Set.mem_iUnion, Set.mem_range] at he
          obtain ⟨i, j, rfl⟩ := he
          exact hψapp (w i j) ▸ hgermw i j
      exact absurd (hle hmap)
        ((Ideal.ne_top_iff_one _).mp (IsLocalRing.maximalIdeal.isMaximal _).ne_top)
    obtain ⟨i₀, hi₀⟩ := hbase
    -- `x` lies in the affine space over the basic piece
    have hrange : x ∈ (map σ (B i₀).ι).opensRange := by
      rw [(isPullback_map (n := σ) (B i₀).ι).opensRange_fst, Scheme.Opens.opensRange_ι,
        hBv i₀]
      simp only [hpl] at hi₀
      rwa [← Scheme.preimage_basicOpen_top, basicOpen_eq_of_affine] at hi₀
    obtain ⟨x', rfl⟩ := hrange
    have : IsAffine (B i₀).toScheme := by
      have h := (isAffineOpen_top (Spec S)).basicOpen ((Scheme.ΓSpecIso S).inv (v i₀))
      rwa [basicOpen_eq_of_affine, ← hBv i₀] at h
    -- the graph section over the basic piece
    set t : σ → Γ((B i₀).toScheme, ⊤) := fun j ↦ ↑(hu i₀).unit⁻¹ *
      ((Scheme.ΓSpecIso S).inv ≫ (B i₀).ι.appTop) (w i₀ j) with ht
    -- pulling back the ambient ring elements to the piece
    have hplmap : ∀ e : S, (map σ (B i₀).ι).appTop (pl e) =
        (𝔸(σ; (B i₀).toScheme) ↘ (B i₀).toScheme).appTop
          (((Scheme.ΓSpecIso S).inv ≫ (B i₀).ι.appTop) e) := by
      intro e
      simp only [hpl]
      rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, map_over,
        Scheme.Hom.comp_appTop, CommRingCat.comp_apply, CommRingCat.comp_apply]
    -- `x'` satisfies the section equations of the graph over the piece
    have hx' : x' ∈ 𝔸(σ; (B i₀).toScheme).zeroLocus (U := ⊤)
        (Set.range fun j ↦ coord (B i₀).toScheme j -
          (𝔸(σ; (B i₀).toScheme) ↘ (B i₀).toScheme).appTop (t j)) := by
      rw [Scheme.mem_zeroLocus_iff]
      rintro - ⟨j, rfl⟩
      intro hmem
      beta_reduce at hmem
      have hsection : coord (B i₀).toScheme j -
          (𝔸(σ; (B i₀).toScheme) ↘ (B i₀).toScheme).appTop (t j) =
          (𝔸(σ; (B i₀).toScheme) ↘ (B i₀).toScheme).appTop ((↑(hu i₀).unit⁻¹ :
            Γ((B i₀).toScheme, ⊤))) * (map σ (B i₀).ι).appTop (E i₀ j) := by
        have hX12 : (𝔸(σ; (B i₀).toScheme) ↘ (B i₀).toScheme).appTop
            ((↑(hu i₀).unit⁻¹ : Γ((B i₀).toScheme, ⊤))) *
            (𝔸(σ; (B i₀).toScheme) ↘ (B i₀).toScheme).appTop
              (((Scheme.ΓSpecIso S).inv ≫ (B i₀).ι.appTop) (v i₀)) = 1 := by
          rw [← map_mul, IsUnit.val_inv_mul, map_one]
        simp only [hE, map_sub, map_mul, ht]
        rw [map_appTop_coord, hplmap (v i₀), hplmap (w i₀ j), mul_sub, ← mul_assoc,
          hX12, one_mul]
      rw [hsection, Scheme.basicOpen_mul] at hmem
      have h2 : x' ∈ (map σ (B i₀).ι) ⁻¹ᵁ 𝔸(σ; Spec S).basicOpen (E i₀ j) := by
        rw [Scheme.preimage_basicOpen_top]
        exact hmem.2
      exact hx (E i₀ j) (Set.mem_iUnion.mpr ⟨i₀, Set.mem_range_self j⟩) h2
    obtain ⟨z, hz⟩ := zeroLocus_subset_range_homOfVector t hx'
    -- the graph section composed with the chart inclusion is `γ`
    have hσγ : homOfVector (𝟙 (B i₀).toScheme) t ≫ map σ (B i₀).ι =
        (Spec S).homOfLE (hB i₀) ≫ γ := by
      apply hom_ext
      · rw [Category.assoc, map_over, homOfVector_over_assoc, Category.id_comp,
          Category.assoc, hγ, Scheme.homOfLE_ι]
      · intro j
        rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, map_appTop_coord,
          homOfVector_appTop_coord]
        simp only [ht]
        calc ↑(hu i₀).unit⁻¹ * ((Scheme.ΓSpecIso S).inv ≫ (B i₀).ι.appTop) (w i₀ j)
            = ↑(hu i₀).unit⁻¹ * (((Spec S).homOfLE (hB i₀) ≫ γ).appTop
                (coord (Spec S) j) *
                ((Scheme.ΓSpecIso S).inv ≫ (B i₀).ι.appTop) (v i₀)) := by
              rw [hcoord i₀ j]
          _ = (↑(hu i₀).unit⁻¹ * ((Scheme.ΓSpecIso S).inv ≫ (B i₀).ι.appTop) (v i₀)) *
                ((Spec S).homOfLE (hB i₀) ≫ γ).appTop (coord (Spec S) j) := by ring
          _ = ((Spec S).homOfLE (hB i₀) ≫ γ).appTop (coord (Spec S) j) := by
              rw [IsUnit.val_inv_mul, one_mul]
    refine ⟨(Spec S).homOfLE (hB i₀) z, ?_⟩
    calc γ ((Spec S).homOfLE (hB i₀) z)
        = ((Spec S).homOfLE (hB i₀) ≫ γ) z := (Scheme.Hom.comp_apply _ _ _).symm
      _ = (homOfVector (𝟙 (B i₀).toScheme) t ≫ map σ (B i₀).ι) z := by rw [hσγ]
      _ = map σ (B i₀).ι (homOfVector (𝟙 (B i₀).toScheme) t z) :=
          Scheme.Hom.comp_apply _ _ _
      _ = map σ (B i₀).ι x' := by rw [hz]

end AffineSpace

end GraphClosedness

end AlgebraicGeometry
