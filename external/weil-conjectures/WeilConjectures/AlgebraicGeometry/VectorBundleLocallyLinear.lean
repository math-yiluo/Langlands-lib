/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.VectorBundleLinearFunctions

/-!
# Locally linear functions and the independence of the chart

For `q : T ⟶ P` and functions `σ₁, …, σ_c` on `T`, a function `s` on `T` is *locally linear* in
the `σₗ` (`AlgebraicGeometry.Scheme.Hom.IsLocallyLinear`) if locally on `P` it is a combination
`∑ q^*(aₗ) σₗ`. These functions form a `Γ(P, ⊤)`-submodule
(`AlgebraicGeometry.Scheme.Hom.locallyLinearSubmodule`). For a linear atlas of a vector bundle,
over the overlap `Vᵢ ×_Z Vⱼ` the coordinates of the chart `j` are locally linear in those of the
chart `i` (the `linear` field), hence so is their whole span
(`AlgebraicGeometry.Scheme.Hom.VectorBundleAtlas.span_chart_coord_le_locallyLinear`): the
fibrewise linear functions do not depend on the chart.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.Hom

variable {c : ℕ} {T P : Scheme.{u}} (q : T ⟶ P) (σ : Fin c → Γ(T, ⊤))

/-- `s` is locally on `P` of the form `∑ q^*(aₗ) σₗ`. -/
def IsLocallyLinear (s : Γ(T, ⊤)) : Prop :=
  ∀ y : P, ∃ (U : P.Opens) (_ : y ∈ U) (a : Fin c → Γ(P, U)),
    T.presheaf.map (homOfLE (le_top : q ⁻¹ᵁ U ≤ ⊤)).op s =
      ∑ l, q.app U (a l) * T.presheaf.map (homOfLE (le_top : q ⁻¹ᵁ U ≤ ⊤)).op (σ l)

variable {q σ}

/-- A linear relation over `U` restricts to a linear relation over `V ≤ U`. -/
lemma linearRelation_restrict {U V : P.Opens} (hVU : V ≤ U) (s : Γ(T, ⊤)) (a : Fin c → Γ(P, U))
    (h : T.presheaf.map (homOfLE (le_top : q ⁻¹ᵁ U ≤ ⊤)).op s =
      ∑ l, q.app U (a l) * T.presheaf.map (homOfLE (le_top : q ⁻¹ᵁ U ≤ ⊤)).op (σ l)) :
    T.presheaf.map (homOfLE (le_top : q ⁻¹ᵁ V ≤ ⊤)).op s =
      ∑ l, q.app V (P.presheaf.map (homOfLE hVU).op (a l)) *
        T.presheaf.map (homOfLE (le_top : q ⁻¹ᵁ V ≤ ⊤)).op (σ l) := by
  have hres (x : Γ(T, ⊤)) : T.presheaf.map (homOfLE (le_top : q ⁻¹ᵁ V ≤ ⊤)).op x =
      T.presheaf.map (homOfLE (q.preimage_mono hVU)).op
        (T.presheaf.map (homOfLE (le_top : q ⁻¹ᵁ U ≤ ⊤)).op x) := by
    rw [← CommRingCat.comp_apply, ← Functor.map_comp]
    rfl
  have hnat (b : Γ(P, U)) : q.app V (P.presheaf.map (homOfLE hVU).op b) =
      T.presheaf.map (homOfLE (q.preimage_mono hVU)).op (q.app U b) := by
    have := congr($(q.naturality (homOfLE hVU).op) b)
    simp only [CommRingCat.comp_apply] at this
    exact this
  rw [hres, h, map_sum]
  refine Finset.sum_congr rfl fun l _ ↦ ?_
  rw [map_mul, hnat, hres]

lemma IsLocallyLinear.of_mem (k : Fin c) : IsLocallyLinear q σ (σ k) := by
  classical
  intro y
  refine ⟨⊤, trivial, Pi.single k 1, ?_⟩
  rw [Finset.sum_eq_single k (fun j _ hj ↦ by rw [Pi.single_eq_of_ne hj, map_zero, zero_mul])
    (fun h' ↦ absurd (Finset.mem_univ k) h'), Pi.single_eq_same, map_one, one_mul]

lemma IsLocallyLinear.zero : IsLocallyLinear q σ 0 := by
  intro y
  refine ⟨⊤, trivial, 0, ?_⟩
  rw [map_zero]
  exact (Finset.sum_eq_zero fun l _ ↦ by rw [Pi.zero_apply, map_zero, zero_mul]).symm

lemma IsLocallyLinear.add {s t : Γ(T, ⊤)} (hs : IsLocallyLinear q σ s)
    (ht : IsLocallyLinear q σ t) : IsLocallyLinear q σ (s + t) := by
  intro y
  obtain ⟨U₁, hy₁, a₁, h₁⟩ := hs y
  obtain ⟨U₂, hy₂, a₂, h₂⟩ := ht y
  refine ⟨U₁ ⊓ U₂, ⟨hy₁, hy₂⟩, fun l ↦ P.presheaf.map (homOfLE inf_le_left).op (a₁ l) +
    P.presheaf.map (homOfLE inf_le_right).op (a₂ l), ?_⟩
  rw [map_add, linearRelation_restrict inf_le_left s a₁ h₁,
    linearRelation_restrict inf_le_right t a₂ h₂, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun l _ ↦ ?_
  rw [map_add, add_mul]

lemma IsLocallyLinear.mul_left (b : Γ(P, ⊤)) {s : Γ(T, ⊤)} (hs : IsLocallyLinear q σ s) :
    IsLocallyLinear q σ (q.appTop b * s) := by
  intro y
  obtain ⟨U, hy, a, h⟩ := hs y
  refine ⟨U, hy, fun l ↦ P.presheaf.map (homOfLE le_top).op b * a l, ?_⟩
  have hnat : T.presheaf.map (homOfLE (le_top : q ⁻¹ᵁ U ≤ ⊤)).op (q.appTop b) =
      q.app U (P.presheaf.map (homOfLE le_top).op b) := by
    have := congr($(q.naturality (homOfLE (le_top : U ≤ ⊤)).op) b)
    simp only [CommRingCat.comp_apply] at this
    exact this.symm
  rw [map_mul, h, hnat, Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ ↦ ?_
  rw [map_mul, mul_assoc]

/-- The locally linear functions, a `Γ(P, ⊤)`-submodule of `Γ(T, ⊤)`. -/
noncomputable def locallyLinearSubmodule (q : T ⟶ P) (σ : Fin c → Γ(T, ⊤)) :
    letI := q.appTop.hom.toAlgebra
    Submodule Γ(P, ⊤) Γ(T, ⊤) :=
  letI := q.appTop.hom.toAlgebra
  { carrier := {s | IsLocallyLinear q σ s}
    add_mem' := fun hs ht ↦ hs.add ht
    zero_mem' := IsLocallyLinear.zero
    smul_mem' := fun b _ hs ↦ by
      rw [Algebra.smul_def]
      exact hs.mul_left b }

lemma span_le_locallyLinearSubmodule {ι : Type*} (τ : ι → Γ(T, ⊤))
    (hτ : ∀ k, IsLocallyLinear q σ (τ k)) :
    letI := q.appTop.hom.toAlgebra
    Submodule.span Γ(P, ⊤) (Set.range τ) ≤ locallyLinearSubmodule q σ := by
  let := q.appTop.hom.toAlgebra
  rw [Submodule.span_le]
  rintro _ ⟨k, rfl⟩
  exact hτ k

namespace VectorBundleAtlas

variable {E Z : Scheme.{u}} {p : E ⟶ Z} {z : Z ⟶ E}

/-- The coordinates of the chart `i`, pulled back to `E ×_Z (Vᵢ ×_Z Vⱼ)`. -/
noncomputable def overlapCoordFst (A : VectorBundleAtlas c p z) (i j : A.ι) (l : Fin c) :
    Γ(pullback p (pullback.fst (A.v i) (A.v j) ≫ A.v i), ⊤) :=
  (pullback.map p (pullback.fst (A.v i) (A.v j) ≫ A.v i) p (A.v i) (𝟙 E)
    (pullback.fst (A.v i) (A.v j)) (𝟙 Z) (by simp) (by simp)).appTop
    ((A.chart i).hom.appTop (AffineSpace.coord (A.V i) (ULift.up l)))

/-- The coordinates of the chart `j`, pulled back to `E ×_Z (Vᵢ ×_Z Vⱼ)`. -/
noncomputable def overlapCoordSnd (A : VectorBundleAtlas c p z) (i j : A.ι) (k : Fin c) :
    Γ(pullback p (pullback.fst (A.v i) (A.v j) ≫ A.v i), ⊤) :=
  (pullback.map p (pullback.fst (A.v i) (A.v j) ≫ A.v i) p (A.v j) (𝟙 E)
    (pullback.snd (A.v i) (A.v j)) (𝟙 Z) (by simp) (by simp [pullback.condition])).appTop
    ((A.chart j).hom.appTop (AffineSpace.coord (A.V j) (ULift.up k)))

/-- Over the overlap `Vᵢ ×_Z Vⱼ`, the coordinates of the chart `j` are locally linear in those of
the chart `i`. -/
lemma isLocallyLinear_overlapCoordSnd (A : VectorBundleAtlas c p z) (i j : A.ι) (k : Fin c) :
    IsLocallyLinear (pullback.snd p (pullback.fst (A.v i) (A.v j) ≫ A.v i))
      (A.overlapCoordFst i j) (A.overlapCoordSnd i j k) :=
  fun y ↦ A.linear i j k y

/-- Blueprint `proposition-purity-vector-bundles`: Vector bundle with zero section

**The fibrewise linear functions do not depend on the chart.** Over `Vᵢ ×_Z Vⱼ`, every function in
the span of the coordinates of the chart `j` is locally a linear combination of the coordinates
of the chart `i`. -/
theorem span_chart_coord_le_locallyLinear (A : VectorBundleAtlas c p z) (i j : A.ι) :
    letI := (pullback.snd p (pullback.fst (A.v i) (A.v j) ≫ A.v i)).appTop.hom.toAlgebra
    Submodule.span Γ(pullback (A.v i) (A.v j), ⊤) (Set.range (A.overlapCoordSnd i j)) ≤
      locallyLinearSubmodule (pullback.snd p (pullback.fst (A.v i) (A.v j) ≫ A.v i))
        (A.overlapCoordFst i j) :=
  span_le_locallyLinearSubmodule _ (A.isLocallyLinear_overlapCoordSnd i j)

end VectorBundleAtlas

end AlgebraicGeometry.Scheme.Hom
