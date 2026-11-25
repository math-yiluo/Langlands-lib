/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import WeilConjectures.AlgebraicGeometry.Morphisms.PuncturedCompletionMatchingSections
public import WeilConjectures.RingTheory.FormalGlueingH0
import WeilConjectures.AlgebraicGeometry.Morphisms.PuncturedCompletionAffineChartRealization

/-! # Formal glueing data from finite affine charts

## References

* Stacks Project, Tag 0BLH, first two proof paragraphs
* Stacks Project, Tag 05EL (the module `H⁰`)
-/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme.CompletionGluingData
/-- Finite affine chart sections give local matching families for formal glueing data. -/
theorem exists_formalGlueingData_prime
    {A : Type u} [CommRing A] [IsLocalRing A]
    {U : (Spec (.of A)).Opens}
    (hU : ∀ x : Spec (.of A), x ∈ U ↔ x ≠ IsLocalRing.closedPoint A)
    {Y : Scheme.{u}} {q : Y ⟶ U.toScheme} [IsFinite q]
    {E : Scheme.{u}} {s : E ⟶ Spec
      (.of (AdicCompletion (IsLocalRing.maximalIdeal A) A))} [IsFinite s]
    (D : CompletionGluingData A U q E s) (t : ℕ) (f : Fin t → A)
    (hgen : Ideal.span (Set.range f) = IsLocalRing.maximalIdeal A) :
    let C := AdicCompletion (IsLocalRing.maximalIdeal A) A
    let φ := algebraMap A C
    let g : CommRingCat.of C ⟶ Γ(E, ⊤) := (ΓSpecIso (.of C)).inv ≫ s.appTop
    letI : Module C Γ(E, ⊤) := Module.compHom _ g.hom
    let O := pullback q (completionSpecMap A ∣_ U)
    let p : O ⟶ Y := pullback.fst q (completionSpecMap A ∣_ U)
    ∃ (X : FormalGlueing.Data.{u, u, u} φ f) (e : X.M' ≃ₗ[C] Γ(E, ⊤))
      (V : Fin t → Y.Opens), ⊤ ≤ iSup V ∧
      ∃ (r : ∀ i, FormalGlueing.h0 φ f X → Γ(Y, V i)),
        (∀ h, Y.presheaf.IsCompatible V (fun i ↦ r i h)) ∧
        ∀ h i, p.app (V i) (r i h) =
          O.presheaf.map (homOfLE (le_top : p ⁻¹ᵁ V i ≤ ⊤)).op
            (D.toCompleted.appTop (e h.val.1)) := by
  classical
  dsimp only
  let C := AdicCompletion (IsLocalRing.maximalIdeal A) A
  let φ := algebraMap A C
  let : Algebra A C := φ.toAlgebra
  let g : CommRingCat.of C ⟶ Γ(E, ⊤) := (ΓSpecIso (.of C)).inv ≫ s.appTop
  let : Module C Γ(E, ⊤) := Module.compHom _ g.hom
  let V := fun i ↦ (q ≫ U.ι) ⁻¹ᵁ PrimeSpectrum.basicOpen (f i)
  have hf : ∀ i, PrimeSpectrum.basicOpen (f i) ≤ U := by
    intro i x hx
    apply (hU x).mpr
    intro heq
    have hfi : f i ∈ IsLocalRing.maximalIdeal A := by
      rw [← hgen]
      exact Ideal.subset_span (Set.mem_range_self i)
    exact hx (heq ▸ hfi)
  have hcover : ⊤ ≤ iSup V := by
    intro y _
    apply TopologicalSpace.Opens.mem_iSup.mpr
    by_contra hn
    have hall : ∀ i, f i ∈ ((q ≫ U.ι) y).asIdeal := by
      intro i
      by_contra hi
      exact hn ⟨i, hi⟩
    have hm : IsLocalRing.maximalIdeal A ≤ ((q ≫ U.ι) y).asIdeal := by
      rw [← hgen]
      exact Ideal.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact hall i)
    have heq : (q ≫ U.ι) y = IsLocalRing.closedPoint A := by
      apply PrimeSpectrum.ext
      exact le_antisymm (IsLocalRing.le_maximalIdeal Ideal.IsPrime.ne_top') hm
    exact ((hU ((q ≫ U.ι) y)).mp (q y).property) heq
  obtain ⟨X, e, c, b, d, hb₁, hb₂, hd₁, hd₂⟩ :=
    exists_affine_chart_realization D t f hf
  refine ⟨X, e, V, hcover, fun i h ↦ c i (h.val.2 i), ?_, ?_⟩
  · intro h i j
    have hh := h.property
    change h.val ∈ _ ⊓ _ at hh
    simp only [Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker,
      LinearMap.sub_apply, sub_eq_zero, LinearMap.comp_apply,
      LinearMap.fst_apply, LinearMap.snd_apply, LinearMap.proj_apply,
      LocalizedModule.mkLinearMap_apply, LinearEquiv.coe_coe] at hh
    calc
      _ = b i j (X.alpha_overlap i j (LocalizedModule.mk (h.val.2 i) 1)) :=
        (hb₁ i j (h.val.2 i)).symm
      _ = b i j (LocalizedModule.mk (h.val.2 j) 1) := congrArg (b i j) (hh.2 i j)
      _ = _ := hb₂ i j (h.val.2 j)
  · intro h i
    have hh := h.property
    change h.val ∈ _ ⊓ _ at hh
    simp only [Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker,
      LinearMap.sub_apply, sub_eq_zero, LinearMap.comp_apply,
      LinearMap.fst_apply, LinearMap.snd_apply, LinearMap.proj_apply,
      LocalizedModule.mkLinearMap_apply, LinearEquiv.coe_coe] at hh
    calc
      _ = d i (TensorProduct.tmul A (1 : C) (h.val.2 i)) := (hd₂ i (h.val.2 i)).symm
      _ = d i (X.alpha i (LocalizedModule.mk h.val.1 1)) := congrArg (d i) (hh.1 i).symm
      _ = _ := hd₁ i h.val.1
end AlgebraicGeometry.Scheme.CompletionGluingData
