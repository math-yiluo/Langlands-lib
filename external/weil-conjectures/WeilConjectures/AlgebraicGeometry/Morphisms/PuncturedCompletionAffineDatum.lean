/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Morphisms.PuncturedCompletionMatchingSections
public import WeilConjectures.RingTheory.FormalGlueingH0
import WeilConjectures.AlgebraicGeometry.Morphisms.PuncturedCompletionAffineCoordinateSquares

/-! # Affine section presentation of the local compatibility equations

## References

* Stacks Project, Tag 0BLH, first two proof paragraphs
* Tag 05EL, H0
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme.CompletionGluingData

private theorem punctured_chart_cover
    {A : Type u} [CommRing A] [IsLocalRing A]
    {U : (Spec (.of A)).Opens}
    (hU : ∀ x : Spec (.of A), x ∈ U ↔ x ≠ IsLocalRing.closedPoint A)
    {Y : Scheme.{u}} (q : Y ⟶ U.toScheme) (t : ℕ) (g : Fin t → A)
    (hgen : Ideal.span (Set.range g) = IsLocalRing.maximalIdeal A) :
    ⊤ ≤ ⨆ j, (q ≫ U.ι) ⁻¹ᵁ PrimeSpectrum.basicOpen (g j) := by
  classical
  intro y _
  apply TopologicalSpace.Opens.mem_iSup.mpr
  by_contra hn
  have hg : ∀ j, g j ∈ ((q ≫ U.ι) y).asIdeal := by
    intro j
    by_contra hj
    exact hn ⟨j, hj⟩
  have hm : IsLocalRing.maximalIdeal A ≤ ((q ≫ U.ι) y).asIdeal := by
    rw [← hgen]
    exact Ideal.span_le.mpr (by rintro _ ⟨j, rfl⟩; exact hg j)
  have he : (q ≫ U.ι) y = IsLocalRing.closedPoint A := by
    apply PrimeSpectrum.ext
    exact le_antisymm (IsLocalRing.le_maximalIdeal_of_isPrime _) hm
  exact (hU ((q ≫ U.ι) y)).mp (q y).property he

/-- The affine datum identifies its ambient coordinates with actual chart sections;
its compatibility equations are precisely local sheaf compatibility and local overlap agreement. -/
theorem exists_formalGlueingData_affine_datum
    {A : Type u} [CommRing A] [IsLocalRing A]
    {U : (Spec (.of A)).Opens}
    (hU : ∀ x : Spec (.of A), x ∈ U ↔ x ≠ IsLocalRing.closedPoint A)
    {Y : Scheme.{u}} {q : Y ⟶ U.toScheme} [IsFinite q]
    {E : Scheme.{u}} {s : E ⟶ Spec
      (.of (AdicCompletion (IsLocalRing.maximalIdeal A) A))} [IsFinite s]
    (D : CompletionGluingData A U q E s) (t : ℕ) (g : Fin t → A)
    (hgen : Ideal.span (Set.range g) = IsLocalRing.maximalIdeal A) :
    let C := AdicCompletion (IsLocalRing.maximalIdeal A) A
    let φ := algebraMap A C
    let V : Fin t → Y.Opens := fun j ↦ (q ≫ U.ι) ⁻¹ᵁ PrimeSpectrum.basicOpen (g j)
    let aY := ((ΓSpecIso (.of A)).inv ≫ (q ≫ U.ι).appTop).hom
    let aE := ((ΓSpecIso (.of A)).inv ≫ (s ≫ completionSpecMap A).appTop).hom
    letI : Algebra A Γ(Y, ⊤) := aY.toAlgebra
    letI : Algebra A Γ(E, ⊤) := aE.toAlgebra
    letI : ∀ j, Algebra A Γ(Y, V j) := fun j ↦
      ((Y.presheaf.map (homOfLE (le_top : V j ≤ ⊤)).op).hom.comp aY).toAlgebra
    let O := pullback q (completionSpecMap A ∣_ U)
    let p : O ⟶ Y := pullback.fst q (completionSpecMap A ∣_ U)
    ⊤ ≤ iSup V ∧
    ∃ (X : FormalGlueing.Data.{u, u, u} φ g)
      (e : FormalGlueing.restrict φ X.M' ≃ₗ[A] Γ(E, ⊤))
      (d : ∀ j, FormalGlueing.piece (g j) (X.M j) ≃ₗ[A] Γ(Y, V j)),
      ∀ x : FormalGlueing.restrict φ X.M' ×
          ∀ j, FormalGlueing.piece (g j) (X.M j),
        x ∈ FormalGlueing.h0 φ g X ↔
          Y.presheaf.IsCompatible V (fun j ↦ d j (x.2 j)) ∧
          ∀ j, p.app (V j) (d j (x.2 j)) =
            O.presheaf.map (homOfLE (le_top : p ⁻¹ᵁ V j ≤ ⊤)).op
              (D.toCompleted.appTop (e x.1)) := by
  dsimp only
  refine ⟨punctured_chart_cover hU q t g hgen, ?_⟩
  have hcharts : ∀ j, PrimeSpectrum.basicOpen (g j) ≤ U := by
    intro j z hz
    apply (hU z).mpr
    intro he
    have hg : g j ∈ IsLocalRing.maximalIdeal A := by
      rw [← hgen]
      exact Ideal.subset_span ⟨j, rfl⟩
    exact hz (he ▸ hg)
  obtain ⟨X, e, d, b, c, hprime, hchart, hleft, hright⟩ :=
    exists_affine_coordinate_squares D t g hcharts
  refine ⟨X, e, d, ?_⟩
  intro x
  let C := AdicCompletion (IsLocalRing.maximalIdeal A) A
  let φ := algebraMap A C
  let : Algebra A C := φ.toAlgebra
  have hh : x ∈ FormalGlueing.h0 φ g X ↔
      (∀ j, X.alpha j (LocalizedModule.mk x.1 1) =
        TensorProduct.tmul A (1 : C) (x.2 j)) ∧
      (∀ i j, X.alpha_overlap i j (LocalizedModule.mk (x.2 i) 1) =
        LocalizedModule.mk (x.2 j) 1) := by
    simp only [FormalGlueing.h0, Submodule.mem_inf, Submodule.mem_iInf,
      LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero, LinearMap.comp_apply,
      LinearMap.proj_apply,
      LocalizedModule.mkLinearMap_apply, LinearEquiv.coe_coe]
    rfl
  rw [hh]
  constructor
  · rintro ⟨hp, hc⟩
    constructor
    · intro i j
      have he := congrArg (c i j) (hc i j)
      simpa only [hleft, hright, TopologicalSpace.Opens.infLELeft,
        TopologicalSpace.Opens.infLERight] using he
    · intro j
      have he := congrArg (b j) (hp j)
      rw [hprime, hchart] at he
      exact he.symm
  · rintro ⟨hc, hp⟩
    constructor
    · intro j
      apply (b j).injective
      rw [hprime, hchart]
      exact (hp j).symm
    · intro i j
      apply (c i j).injective
      rw [hleft, hright]
      simpa only [TopologicalSpace.Opens.infLELeft,
        TopologicalSpace.Opens.infLERight] using hc i j

end AlgebraicGeometry.Scheme.CompletionGluingData
