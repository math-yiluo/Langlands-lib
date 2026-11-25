/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.ChartSections
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.OfInvertible
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.TransitionUnits
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme

/-!
# The boundary of a standard chart of projective space

The ratio `Tⱼ / Tᵢ` on the standard open `D₊(Tᵢ)` of `ℙ(n; S)` is invertible exactly on
`D₊(Tᵢ) ∩ D₊(Tⱼ)`. Hence, when `D₊(Tᵢ)` and `D₊(Tⱼ)` cover `ℙ(n; S)` (e.g. for the projective
line), the zero locus of `Tⱼ / Tᵢ` in `D₊(Tᵢ)` is the closed complement of `D₊(Tⱼ)`, and its
inclusion into `ℙ(n; S)` is a closed immersion. For the projective line `ℙ(Option n; S)` with
`n` a singleton and `j = none`, this is the section at infinity, the complement of the standard
chart `𝔸¹_S ⟶ ℙ¹_S`.

## Main definitions

- `AlgebraicGeometry.ProjectiveSpace.chartBoundaryι`: the inclusion of the zero locus of
  `Tⱼ / Tᵢ` in `D₊(Tᵢ)` into `ℙ(n; S)`.

## Main statements

- `AlgebraicGeometry.ProjectiveSpace.basicOpen_coordRatio`: `D(Tⱼ / Tᵢ) = D₊(Tᵢ) ∩ D₊(Tⱼ)`.
- `AlgebraicGeometry.ProjectiveSpace.range_chartBoundaryι`: its range is the complement of
  `D₊(Tⱼ)` if `D₊(Tᵢ) ∪ D₊(Tⱼ) = ℙ(n; S)`.
-/

@[expose] public section

universe u

open CategoryTheory Limits MvPolynomial

noncomputable section

namespace AlgebraicGeometry

/-- The zero locus of a function `r` on an open `U` of `X`, included into `X`, has range
`U ∖ D(r)`. -/
lemma Scheme.range_zeroLocusSubschemeι_comp_ι {X : Scheme.{u}} (U : X.Opens) (r : Γ(X, U)) :
    Set.range (U.toScheme.zeroLocusSubschemeι {U.topIso.inv r} ≫ U.ι).base =
      (U : Set X) \ X.basicOpen r := by
  rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
    range_zeroLocusSubschemeι_singleton, Scheme.Opens.range_ι]
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨y.2, fun h ↦ hy ?_⟩
    rw [← Scheme.Opens.ι_image_basicOpen_topIso_inv] at h
    obtain ⟨z, hz, hzy⟩ := h
    rwa [U.ι.isOpenEmbedding.injective hzy] at hz
  · rintro ⟨hx, hx'⟩
    refine ⟨⟨x, hx⟩, fun h ↦ hx' ?_, rfl⟩
    rw [← Scheme.Opens.ι_image_basicOpen_topIso_inv]
    exact ⟨_, h, rfl⟩

namespace ProjectiveSpace

attribute [local instance] MvPolynomial.gradedAlgebra

variable {n : Type u} (S : Scheme.{u})

/-- The ratio `Tⱼ / Tᵢ` on `D₊(Tᵢ)`, restricted to `D₊(Tⱼ) ∩ D₊(Tᵢ)`, is the ratio `xⱼ / xᵢ` of
`AlgebraicGeometry.ProjectiveSpace.ratio`. -/
lemma map_coordRatio_eq_ratio (i j : n) :
    ℙ(n; S).presheaf.map (homOfLE (inf_le_right :
        standardOpen n S j ⊓ standardOpen n S i ≤ standardOpen n S i)).op
      (coordRatio n S i j) = ratio n S j i := by
  rfl

/-- **The ratio `Tⱼ / Tᵢ` is invertible exactly on `D₊(Tᵢ) ∩ D₊(Tⱼ)`.** -/
lemma basicOpen_coordRatio (i j : n) :
    ℙ(n; S).basicOpen (coordRatio n S i j) = standardOpen n S i ⊓ standardOpen n S j := by
  refine le_antisymm (le_inf (ℙ(n; S).basicOpen_le _) (basicOpen_coordRatio_le S i j)) ?_
  have h := ℙ(n; S).basicOpen_res (coordRatio n S i j) (homOfLE (inf_le_right :
    standardOpen n S j ⊓ standardOpen n S i ≤ standardOpen n S i)).op
  have hu : IsUnit (ratio n S j i) := (ratioUnit n S j i).isUnit
  rw [map_coordRatio_eq_ratio, Scheme.basicOpen_of_isUnit _ hu] at h
  rw [inf_comm, h]
  exact inf_le_right

/-- The inclusion into `ℙ(n; S)` of the zero locus of `Tⱼ / Tᵢ` in the standard open
`D₊(Tᵢ)`. -/
abbrev chartBoundaryι (i j : n) :
    (standardOpen n S i).toScheme.zeroLocusSubscheme
        {(standardOpen n S i).topIso.inv (coordRatio n S i j)} ⟶ ℙ(n; S) :=
  (standardOpen n S i).toScheme.zeroLocusSubschemeι _ ≫ (standardOpen n S i).ι

/-- If `D₊(Tᵢ)` and `D₊(Tⱼ)` cover `ℙ(n; S)`, the zero locus of `Tⱼ / Tᵢ` in `D₊(Tᵢ)` is the
complement of `D₊(Tⱼ)`. -/
lemma range_chartBoundaryι {i j : n} (h : standardOpen n S i ⊔ standardOpen n S j = ⊤) :
    Set.range (chartBoundaryι S i j).base = (standardOpen n S j : Set ℙ(n; S))ᶜ := by
  rw [chartBoundaryι, Scheme.range_zeroLocusSubschemeι_comp_ι, basicOpen_coordRatio]
  ext x
  have hx : x ∈ standardOpen n S i ⊔ standardOpen n S j := h ▸ trivial
  simp only [TopologicalSpace.Opens.coe_inf, Set.mem_sdiff, Set.mem_inter_iff,
    Set.mem_compl_iff, SetLike.mem_coe]
  rcases hx with hx | hx <;> tauto

/-- If `D₊(Tᵢ)` and `D₊(Tⱼ)` cover `ℙ(n; S)`, the zero locus of `Tⱼ / Tᵢ` in `D₊(Tᵢ)` is a
closed subscheme of `ℙ(n; S)`. -/
lemma isClosedImmersion_chartBoundaryι {i j : n}
    (h : standardOpen n S i ⊔ standardOpen n S j = ⊤) :
    IsClosedImmersion (chartBoundaryι S i j) := by
  have : IsPreimmersion (chartBoundaryι S i j) := by
    rw [chartBoundaryι]
    infer_instance
  refine .of_isPreimmersion _ ?_
  rw [range_chartBoundaryι S h]
  exact (standardOpen n S j).isOpen.isClosed_compl

/-- The two standard opens of the projective line `ℙ(Option n; S)`, `n` a singleton, cover
it. -/
lemma standardOpen_some_sup_standardOpen_none [Subsingleton n] (a : n) :
    standardOpen (Option n) S (some a) ⊔ standardOpen (Option n) S none = ⊤ := by
  refine eq_top_iff.2 fun x _ ↦ ?_
  have hx : x ∈ ⨆ k, standardOpen (Option n) S k := by
    rw [iSup_standardOpen]
    trivial
  obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 hx
  rcases k with _ | b
  · exact Or.inr hk
  · exact Or.inl (Subsingleton.elim b a ▸ hk)

/-- The section at infinity of the projective line `ℙ(Option n; S)`, `n` a singleton: the zero
locus of `T_∞ / T_a` in the chart `D₊(T_a)` at infinity, a closed subscheme of `ℙ(Option n; S)`
complementary to the standard chart `D₊(T_∞)` (the image of `𝔸(n; S)`). -/
instance isClosedImmersion_chartBoundaryι_none [Subsingleton n] (a : n) :
    IsClosedImmersion (chartBoundaryι S (some a) none) :=
  isClosedImmersion_chartBoundaryι S (standardOpen_some_sup_standardOpen_none S a)

end ProjectiveSpace

end AlgebraicGeometry
