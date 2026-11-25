/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Modules.DifferentialsSections
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.ChartSections
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.SmallAffineZariski

/-!
# The standard charts of projective space over a ring are polynomial rings

Let `A` be a commutative ring and `Uᵢ = D₊(xᵢ)` a standard open of `ℙ(n; Spec A)`. The ring of
functions `Γ(Uᵢ)` is the polynomial ring over `A` in the ratios `x_k / xᵢ`, `k ≠ i`.

## Main declarations

- `AlgebraicGeometry.ProjectiveSpace.homOfSections_coord_eq`: the morphism
  `𝔸({k // k ≠ i}; S) ⟶ ℙ(n; S)` given by the coordinates and `1` in position `i` is the inverse
  of the chart isomorphism `D₊(xᵢ) ≅ 𝔸({k // k ≠ i}; S)` followed by the inclusion.
- `AlgebraicGeometry.ProjectiveSpace.chartRingEquiv`: `A[x_k / xᵢ: k ≠ i] ≃ Γ(D₊(xᵢ))`.
-/

@[expose] public section

universe u

open CategoryTheory Limits MvPolynomial

noncomputable section

namespace AlgebraicGeometry.ProjectiveSpace

variable {n : Type u} (S : Scheme.{u}) (i : n)

/-- The family of sections `(w_k)` of `𝔸({k // k ≠ i}; S)`: the coordinates, and `1` in
position `i`. -/
def coordOne : n → Γ(𝔸({k : n // k ≠ i}; S), ⊤) := by
  classical
  exact fun a ↦ if h : a = i then 1 else AffineSpace.coord S ⟨a, h⟩

lemma coordOne_self : coordOne S i i = 1 := by
  simp [coordOne]

lemma coordOne_of_ne (k : {k : n // k ≠ i}) : coordOne S i k.1 = AffineSpace.coord S k := by
  simp [coordOne, k.2]

lemma span_range_coordOne : Ideal.span (Set.range (coordOne S i)) = ⊤ :=
  Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span ⟨i, rfl⟩)
    (by rw [coordOne_self]; exact isUnit_one)

/-- **The inverse chart.** The morphism `𝔸({k // k ≠ i}; S) ⟶ ℙ(n; S)` given by the coordinates
and `1` in position `i` is the inverse of the chart isomorphism followed by the inclusion of
`D₊(xᵢ)`. -/
theorem homOfSections_coord_eq :
    homOfSections (𝔸({k : n // k ≠ i}; S) ↘ S) (coordOne S i) (span_range_coordOne S i) =
      (standardOpenIso n S i).inv ≫ (standardOpen n S i).ι := by
  set Y := 𝔸({k : n // k ≠ i}; S)
  have hw := span_range_coordOne S i
  set H := homOfSections (Y ↘ S) (coordOne S i) hw
  set B := Y.basicOpen (coordOne S i i)
  have hB : B = ⊤ := by
    simp only [B, coordOne_self]
    exact Y.basicOpen_one
  have hle : B ≤ H ⁻¹ᵁ standardOpen n S i :=
    (homOfSections_preimage_standardOpen _ (coordOne S i) hw i).ge
  have : IsIso B.ι := Scheme.Opens.isIso_ι_of_eq_top hB
  have h2 : H.resLE (standardOpen n S i) B hle ≫ (standardOpenIso n S i).hom = B.ι := by
    refine (homOfSections_resLE_standardOpenIso_hom (Y ↘ S) (coordOne S i) hw i).trans ?_
    refine AffineSpace.hom_ext (by simp) fun j ↦ ?_
    rw [AffineSpace.homOfVector_appTop_coord]
    symm
    refine Y.eq_divBasicOpen ?_
    have h1 : ∀ x : Γ(Y, ⊤), x = 1 → (Y.basicOpen (coordOne S i i)).ι.appTop x = 1 := by
      rintro x rfl
      exact map_one _
    rw [h1 _ (coordOne_self S i), mul_one, coordOne_of_ne]
  have h3 : B.ι ≫ H = B.ι ≫ (standardOpenIso n S i).inv ≫ (standardOpen n S i).ι := by
    rw [← Scheme.Hom.resLE_comp_ι H hle, ← h2, Category.assoc, Iso.hom_inv_id_assoc]
  exact (cancel_epi B.ι).mp h3

variable (n) (A : Type u) [CommRing A] {i}

/-- The inverse chart `Spec A[x_k / xᵢ : k ≠ i] ≅ D₊(xᵢ) ⊆ ℙ(n; Spec A)`. -/
def chartMap (i : n) : Spec (.of (MvPolynomial {k : n // k ≠ i} A)) ⟶ ℙ(n; Spec (.of A)) :=
  (AffineSpace.SpecIso {k : n // k ≠ i} (.of A)).inv ≫ (standardOpenIso n _ i).inv ≫
    (standardOpen n _ i).ι

lemma top_le_chartMap_preimage (i : n) : ⊤ ≤ chartMap n A i ⁻¹ᵁ standardOpen n _ i := by
  simp [chartMap, Scheme.Opens.ι_preimage_self]

/-- The ring map `Γ(D₊(xᵢ)) → A[x_k / xᵢ : k ≠ i]` of the inverse chart. -/
def chartToPoly (i : n) :
    Γ(ℙ(n; Spec (.of A)), standardOpen n _ i) →+* MvPolynomial {k : n // k ≠ i} A :=
  ((chartMap n A i).appLE _ ⊤ (top_le_chartMap_preimage n A i) ≫ (Scheme.ΓSpecIso _).hom).hom

lemma bijective_chartToPoly (i : n) : Function.Bijective (chartToPoly n A i) := by
  have e : (chartMap n A i).appLE _ ⊤ (top_le_chartMap_preimage n A i) =
      (standardOpen n _ i).ι.appLE _ ⊤ (standardOpen n _ i).ι_preimage_self.ge ≫
        ((AffineSpace.SpecIso {k : n // k ≠ i} (.of A)).inv ≫
          (standardOpenIso n _ i).inv).appLE ⊤ ⊤ le_top := by
    rw [Scheme.Hom.appLE_comp_appLE]
    exact Scheme.Hom.appLE_congr_hom (Category.assoc _ _ _).symm _ _ _ _
  rw [chartToPoly, e, Scheme.Hom.appLE_top_top]
  exact ConcreteCategory.bijective_of_isIso _
lemma chartToPoly_coordRatio (i : n) (k : {k : n // k ≠ i}) :
    chartToPoly n A i (coordRatio n _ i k) = X k := by
  have hH := homOfSections_coord_eq (Spec (.of A)) i
  have hle : ⊤ ≤ homOfSections (𝔸({k : n // k ≠ i}; Spec (.of A)) ↘ Spec (.of A))
      (coordOne _ i) (span_range_coordOne _ i) ⁻¹ᵁ standardOpen n _ i := by
    rw [hH]
    simp [Scheme.Opens.ι_preimage_self]
  have e : (chartMap n A i).appLE _ ⊤ (top_le_chartMap_preimage n A i) =
      (homOfSections (𝔸({k : n // k ≠ i}; Spec (.of A)) ↘ Spec (.of A))
        (coordOne _ i) (span_range_coordOne _ i)).appLE _ ⊤ hle ≫
        (AffineSpace.SpecIso {k : n // k ≠ i} (.of A)).inv.appLE ⊤ ⊤ le_top := by
    rw [Scheme.Hom.appLE_comp_appLE]
    refine Scheme.Hom.appLE_congr_hom ?_ _ _ _ _
    rw [hH, chartMap]
  rw [chartToPoly, e, Scheme.Hom.appLE_top_top, CommRingCat.hom_comp, CommRingCat.hom_comp,
    RingHom.comp_apply, RingHom.comp_apply, homOfSections_appLE_coordRatio _ _ _
      (coordOne_self _ i), coordOne_of_ne, AffineSpace.SpecIso_inv_appTop_coord,
    Iso.inv_hom_id_apply]

lemma chartToPoly_specStructureMap (i : n) (a : A) :
    chartToPoly n A i ((ℙ(n; Spec (.of A)) ↘ Spec (.of A)).specStructureMap _ a) = C a := by
  have e : (Scheme.ΓSpecIso (.of A)).inv ≫
      (ℙ(n; Spec (.of A)) ↘ Spec (.of A)).appLE ⊤ (standardOpen n _ i) le_top ≫
      (chartMap n A i).appLE _ ⊤ (top_le_chartMap_preimage n A i) ≫ (Scheme.ΓSpecIso _).hom =
      CommRingCat.ofHom C := by
    rw [Scheme.Hom.appLE_comp_appLE_assoc]
    have h : chartMap n A i ≫ (ℙ(n; Spec (.of A)) ↘ Spec (.of A)) =
        Spec.map (CommRingCat.ofHom C) := by
      rw [chartMap, Category.assoc, Category.assoc, standardOpenIso_inv_ι_over,
        AffineSpace.SpecIso_inv_over]
    rw [Scheme.Hom.appLE_congr_hom h _ _ _ le_top, Scheme.Hom.appLE_top_top,
      Scheme.ΓSpecIso_naturality, Iso.inv_hom_id_assoc]
  have h := ConcreteCategory.congr_hom e a
  rw [chartToPoly, Scheme.Hom.specStructureMap, CommRingCat.hom_comp, RingHom.comp_apply,
    CommRingCat.comp_apply]
  exact h

/-- **The standard chart of projective space over a ring is a polynomial ring**: the ring
isomorphism `A[x_k / xᵢ : k ≠ i] ≃ Γ(D₊(xᵢ))` sending the variable `X k` to the ratio
`x_k / xᵢ` (`chartRingEquiv_X`) and the constants to the functions pulled back from `Spec A`
(`chartRingEquiv_C`). -/
def chartRingEquiv (i : n) :
    MvPolynomial {k : n // k ≠ i} A ≃+* Γ(ℙ(n; Spec (.of A)), standardOpen n _ i) :=
  (RingEquiv.ofBijective _ (bijective_chartToPoly n A i)).symm

@[simp]
lemma chartRingEquiv_X (i : n) (k : {k : n // k ≠ i}) :
    chartRingEquiv n A i (X k) = coordRatio n _ i k := by
  rw [chartRingEquiv, RingEquiv.symm_apply_eq, RingEquiv.ofBijective_apply,
    chartToPoly_coordRatio]

@[simp]
lemma chartRingEquiv_C (i : n) (a : A) :
    chartRingEquiv n A i (C a) =
      (ℙ(n; Spec (.of A)) ↘ Spec (.of A)).specStructureMap _ a := by
  rw [chartRingEquiv, RingEquiv.symm_apply_eq, RingEquiv.ofBijective_apply,
    chartToPoly_specStructureMap]

end AlgebraicGeometry.ProjectiveSpace
