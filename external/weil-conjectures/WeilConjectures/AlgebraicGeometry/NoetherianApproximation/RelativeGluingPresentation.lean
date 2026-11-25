/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.AlgebraicGeometry.OpensGlueData
public import WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit

/-!
# The selected finite relative affine presentation

Let `{Dⱼ}` be a cofiltered system of schemes with limit cone `c` and let `g : X ⟶ lim Dⱼ` be a
morphism from a quasi-compact scheme. A finite relative affine presentation of `X` over
`lim Dⱼ` (`AlgebraicGeometry.RelativeAffinePresentation`) consists of a stage `D_{i₀}`, finitely
many affine opens `Vₐ ⊆ D_{i₀}` and affine opens `Wₐ ⊆ X` covering `X` with `Wₐ` lying over `Vₐ`.
The preimages of the `Vₐ` in `lim Dⱼ` are affine opens whose rings are the filtered colimits
of the rings of the preimages of `Vₐ` at the later stages, and the charts `Wₐ` are finitely
presented over them when `g` is locally of finite presentation.

The overlaps `Wₐ ∩ W_b`, recorded as opens of `Wₐ`, together with both directions of the
overlap isomorphisms, form gluing data along opens
(`AlgebraicGeometry.RelativeAffinePresentation.glueData`), which records the finitely many
identity, inverse and cocycle equations.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

variable {I : Type u} [Category.{u} I] {D : I ⥤ Scheme.{u}} (c : Cone D)

/-- A finite relative affine presentation `R_X` of `g : X ⟶ lim Dⱼ`: a stage `i₀`, finitely
many affine opens `base a` of `D_{i₀}` and affine opens `chart a` covering `X`, with `chart a`
mapping into `base a`. -/
structure RelativeAffinePresentation {X : Scheme.{u}} (g : X ⟶ c.pt) where
  /-- The stage `i₀` over which the base charts are chosen. -/
  stage : I
  /-- The finite index type of the charts. -/
  J : Type u
  /-- There are finitely many charts. -/
  finite : Finite J
  /-- The affine base charts of `D_{i₀}`. -/
  base (a : J) : (D.obj stage).Opens
  /-- The base charts are affine. -/
  isAffineOpen_base (a : J) : IsAffineOpen (base a)
  /-- The affine charts of `X`. -/
  chart (a : J) : X.Opens
  /-- The charts of `X` are affine. -/
  isAffineOpen_chart (a : J) : IsAffineOpen (chart a)
  /-- Each chart of `X` maps into the corresponding base chart. -/
  chart_le (a : J) : chart a ≤ (g ≫ c.π.app stage) ⁻¹ᵁ base a
  /-- The charts cover `X`. -/
  iSup_chart : ⨆ a, chart a = ⊤

namespace RelativeAffinePresentation

attribute [instance] RelativeAffinePresentation.finite

variable {c} {X : Scheme.{u}} {g : X ⟶ c.pt} (R : RelativeAffinePresentation c g)

/-- The overlap `Wₐ ∩ W_b`, as an open of the chart `Wₐ`. -/
noncomputable def overlap (a b : R.J) : (R.chart a).toScheme.Opens :=
  (R.chart a).ι ⁻¹ᵁ R.chart b

lemma opensRange_overlap_ι_comp (a b : R.J) :
    ((R.overlap a b).ι ≫ (R.chart a).ι).opensRange = R.chart a ⊓ R.chart b := by
  rw [Scheme.Hom.opensRange_comp, Scheme.Opens.opensRange_ι, overlap,
    Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]

/-- The overlaps are quasi-compact if `X` is quasi-separated. -/
lemma isCompact_overlap [QuasiSeparatedSpace X] (a b : R.J) :
    IsCompact (R.overlap a b : Set (R.chart a).toScheme) := by
  have e : (R.overlap a b : Set (R.chart a).toScheme) =
      (R.chart a).ι ⁻¹' ((R.chart a : Set X) ∩ R.chart b) := by
    ext x
    simp [overlap, Scheme.Opens.ι_apply]
  rw [e, (R.chart a).ι.isOpenEmbedding.isInducing.isCompact_preimage_iff (by
    rw [Scheme.Opens.range_ι]
    exact Set.inter_subset_left)]
  exact QuasiSeparatedSpace.inter_isCompact _ _ (R.chart a).2
    (R.isAffineOpen_chart a).isCompact (R.chart b).2 (R.isAffineOpen_chart b).isCompact

/-- The overlap isomorphism `Wₐ ∩ W_b ⟶ W_b ∩ Wₐ`, from the overlap in `Wₐ` to the overlap in
`W_b`. -/
noncomputable def overlapMap (a b : R.J) : (R.overlap a b).toScheme ⟶ (R.overlap b a).toScheme :=
  IsOpenImmersion.lift ((R.overlap b a).ι ≫ (R.chart b).ι) ((R.overlap a b).ι ≫ (R.chart a).ι)
    (by
      have h₁ := congrArg (fun U : X.Opens ↦ (U : Set X)) (R.opensRange_overlap_ι_comp a b)
      have h₂ := congrArg (fun U : X.Opens ↦ (U : Set X)) (R.opensRange_overlap_ι_comp b a)
      simp only [Scheme.Hom.coe_opensRange, TopologicalSpace.Opens.coe_inf] at h₁ h₂
      rw [h₁, h₂, Set.inter_comm])

@[reassoc (attr := simp)]
lemma overlapMap_ι_ι (a b : R.J) :
    R.overlapMap a b ≫ (R.overlap b a).ι ≫ (R.chart b).ι = (R.overlap a b).ι ≫ (R.chart a).ι :=
  IsOpenImmersion.lift_fac _ _ _

lemma overlapMap_apply_val_val (a b : R.J) (x : R.overlap a b) :
    ((R.overlapMap a b x).1).1 = x.1.1 := by
  have := congrArg (fun f ↦ f x) (R.overlapMap_ι_ι a b)
  simp only [Scheme.Hom.comp_apply, Scheme.Opens.ι_apply] at this
  exact this

/-- The overlaps and overlap isomorphisms of `R_X`, together with their identity, inverse and
cocycle equations, as gluing data along opens. -/
noncomputable def glueData : Scheme.OpensGlueData.{u} where
  J := R.J
  U a := (R.chart a).toScheme
  V := R.overlap
  V_self a := Scheme.Opens.ι_preimage_self _
  t := R.overlapMap
  t_self a := by
    rw [← cancel_mono ((R.overlap a a).ι ≫ (R.chart a).ι), overlapMap_ι_ι, Category.id_comp]
  t_mem a b c x hx := by
    have hx' : x.1.1 ∈ R.chart c := hx
    have h : ((R.overlapMap a b x).1).1 ∈ R.chart c := by rwa [overlapMap_apply_val_val]
    exact h
  cocycle a b c := by
    rw [← cancel_mono (R.chart c).ι]
    simp only [Category.assoc, overlapMap_ι_ι, IsOpenImmersion.lift_fac_assoc]
    rw [Scheme.homOfLE_ι_assoc, Scheme.homOfLE_ι_assoc]

/-- The charts are of finite presentation over the limit. -/
instance locallyOfFinitePresentation_chart [LocallyOfFinitePresentation g] (a : R.J) :
    LocallyOfFinitePresentation ((R.chart a).ι ≫ g) :=
  inferInstance

end RelativeAffinePresentation

variable {c}

/-- A quasi-compact scheme over the limit of a nonempty system has a finite relative affine
presentation. -/
theorem nonempty_relativeAffinePresentation [Nonempty I] {X : Scheme.{u}} (g : X ⟶ c.pt)
    [CompactSpace X] : Nonempty (RelativeAffinePresentation c g) := by
  obtain ⟨i₀⟩ := ‹Nonempty I›
  obtain ⟨Us, hUsB, hUsfin, hUs⟩ :=
    (isBasis_affineOpens_le_preimage (g ≫ c.π.app i₀)).exists_finite_of_isCompact
      (U := ⊤) (by simpa using isCompact_univ)
  choose V hV hle using fun W : Us ↦ (hUsB W.2).2
  exact ⟨{
    stage := i₀
    J := Us
    finite := hUsfin.to_subtype
    base := V
    isAffineOpen_base := hV
    chart W := W.1
    isAffineOpen_chart W := (hUsB W.2).1
    chart_le := hle
    iSup_chart := by rw [hUs, sSup_eq_iSup'] }⟩

/-- The selected finite relative affine presentation `R_X` of a quasi-compact scheme over the
limit of a nonempty system. -/
noncomputable def relativeAffinePresentation [Nonempty I] {X : Scheme.{u}} (g : X ⟶ c.pt)
    [CompactSpace X] : RelativeAffinePresentation c g :=
  Classical.choice (nonempty_relativeAffinePresentation g)

end AlgebraicGeometry
