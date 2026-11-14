import Langlands.Geometry.Building.IntegerValuationBuildingComparison
import Langlands.Geometry.Building.UnramifiedSemilinearMetricActionStatement

/-! # Transporting one metric and a whole semilinear action together -/

noncomputable section

universe u

namespace Langlands.Geometry.Metric.KP

/-- A single complete NPC metric, an isometric existing action, and a coherent
isometric semilinear action with finite orbits. -/
def HasFiniteSemilinearMetricAction (A Γ X : Type*) [Monoid Γ] [SMul A X]
    (τ : Γ → A → A) : Prop :=
  ∃ m : MetricSpace X,
    letI := m
    CompleteSpace X ∧ IsNonpositivelyCurved X ∧ IsIsometricSMul A X ∧
    ∃ ρ : Γ →* Equiv.Perm X,
      (∀ (σ : Γ) (g : A) (x : X), ρ σ (g • x) = τ σ g • ρ σ x) ∧
      (∀ σ, Isometry (ρ σ)) ∧
      ∀ x : X, (Set.range (fun σ => ρ σ x)).Finite

namespace HasFiniteSemilinearMetricAction

variable {A Γ X Y : Type*} [Monoid Γ] [SMul A X] [SMul A Y]
    {τ : Γ → A → A}

/-- Pull the metric through one equivariant equivalence and conjugate the
entire homomorphism through that same equivalence. -/
theorem transport (h : HasFiniteSemilinearMetricAction A Γ X τ)
    (e : X ≃ Y) (he : ∀ (g : A) (x : X), e (g • x) = g • e x) :
    HasFiniteSemilinearMetricAction A Γ Y τ := by
  obtain ⟨m, hc, hnpc, hi, ρ, hsemi, hρi, hfin⟩ := h
  let := m
  let := hc
  let := hi
  let mY : MetricSpace Y := MetricSpace.induced e.symm e.symm.injective m
  let := mY
  let E : Y ≃ᵢ X :=
    { e.symm with
      isometry_toFun := MetricSpace.isometry_induced e.symm e.symm.injective }
  have hes (g : A) (y : Y) : e.symm (g • y) = g • e.symm y := by
    apply e.injective
    rw [e.apply_symm_apply, he, e.apply_symm_apply]
  let ρY : Γ →* Equiv.Perm Y := e.permCongrHom.toMonoidHom.comp ρ
  refine ⟨mY, E.completeSpace, ?_, ?_, ρY, ?_, ?_, ?_⟩
  · intro x y
    obtain ⟨p, hp⟩ := hnpc (e.symm x) (e.symm y)
    refine ⟨e p, fun z => ?_⟩
    change 2 * dist (e.symm (e p)) (e.symm z) ^ 2 +
      (1 / 2) * dist (e.symm x) (e.symm y) ^ 2 ≤
        dist (e.symm x) (e.symm z) ^ 2 + dist (e.symm y) (e.symm z) ^ 2
    simpa only [e.symm_apply_apply] using hp (e.symm z)
  · constructor
    intro g
    apply Isometry.of_dist_eq
    intro x y
    change dist (e.symm (g • x)) (e.symm (g • y)) =
      dist (e.symm x) (e.symm y)
    rw [hes, hes, dist_smul]
  · intro σ g y
    change e (ρ σ (e.symm (g • y))) = τ σ g • e (ρ σ (e.symm y))
    rw [hes, hsemi, he]
  · intro σ
    apply Isometry.of_dist_eq
    intro x y
    change dist (e.symm (e (ρ σ (e.symm x))))
      (e.symm (e (ρ σ (e.symm y)))) = dist (e.symm x) (e.symm y)
    simpa only [e.symm_apply_apply] using (hρi σ).dist_eq (e.symm x) (e.symm y)
  · intro y
    change (Set.range (fun σ => e (ρ σ (e.symm y)))).Finite
    rw [Set.range_comp']
    exact (hfin (e.symm y)).image e

end HasFiniteSemilinearMetricAction
end Langlands.Geometry.Metric.KP

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.GroupScheme.GaloisPointComparison
open Langlands.LocalGalois.Separable

namespace Langlands.Geometry.Building

private instance transportExtendedAffine
    {F : Type u} [Field F] {K : Type u} [Field K] [Algebra F K]
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom] :
    IsAffineHom (baseChanged F K G).X.hom := by
  change IsAffineHom (Limits.pullback.snd G.X.hom (baseMap F K))
  infer_instance

/-- The complete simultaneous metric/action package does not depend on the
choice of full-V6 building datum over the actual maximal unramified field. -/
theorem unramifiedSemilinearMetricAction_iff_of_sameGroup
    (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom]
    (C C' : MaximalUnramified.BuildingData F (baseChanged F (inertiaFixedField F) G)) :
    Metric.KP.HasFiniteSemilinearMetricAction
        (rationalPoints (baseChanged F (inertiaFixedField F) G))
        (inertiaFixedField F ≃ₐ[F] inertiaFixedField F) C.ReducedBuilding
        (fun σ g => rationalConjugate F (inertiaFixedField F) G σ g) ↔
      Metric.KP.HasFiniteSemilinearMetricAction
        (rationalPoints (baseChanged F (inertiaFixedField F) G))
        (inertiaFixedField F ≃ₐ[F] inertiaFixedField F) C'.ReducedBuilding
        (fun σ g => rationalConjugate F (inertiaFixedField F) G σ g) := by
  obtain ⟨e, he, _⟩ := integerValuationBuildingSameGroupComparison
    (inertiaFixedField F) (MaximalUnramified.valuation F)
    (baseChanged F (inertiaFixedField F) G) C C'
  refine ⟨fun h => h.transport e he, fun h => h.transport e.symm ?_⟩
  intro g y
  apply e.injective
  rw [e.apply_symm_apply, he, e.apply_symm_apply]

/-- For each group, constructing one full datum with all the metric/action
witnesses suffices for the published every-datum statement. -/
theorem unramifiedSemilinearMetricAction_of_oneDatum
    (h : ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
      [IsNonarchimedeanLocalField F]
      (G : GroupScheme (Spec (CommRingCat.of F))) (hG : IsConnectedReductive G),
      letI : IsAffineHom G.X.hom := hG.isAffineHom
      ∃ C : MaximalUnramified.BuildingData F (baseChanged F (inertiaFixedField F) G),
        Metric.KP.HasFiniteSemilinearMetricAction
          (rationalPoints (baseChanged F (inertiaFixedField F) G))
          (inertiaFixedField F ≃ₐ[F] inertiaFixedField F) C.ReducedBuilding
          (fun σ g => rationalConjugate F (inertiaFixedField F) G σ g)) :
    UnramifiedSemilinearMetricActionStatement.{u} := by
  intro F _ _ _ _ G hG
  let : IsAffineHom G.X.hom := hG.isAffineHom
  intro C
  obtain ⟨C₀, h₀⟩ := h F G hG
  exact (unramifiedSemilinearMetricAction_iff_of_sameGroup F G C₀ C).mp h₀

end Langlands.Geometry.Building
