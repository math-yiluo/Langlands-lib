import Langlands.Cohomology.Continuous.FiniteQuotientComparisonProof

universe u

open CategoryTheory

namespace Langlands.Continuous

attribute [local instance] continuousToOrdinary_isIso

variable {k G Q : Type u} [CommRing k] [TopologicalSpace k]
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q] [DiscreteTopology Q]

/-- A genuine discrete-stage class maps into continuous cohomology through a continuous group map. -/
noncomputable def discreteStageToContinuous (B : TopRep.{u} k Q) (A : TopRep.{u} k G)
    (φ : G →ₜ* Q) (f : TopRep.res φ B ⟶ A) (q : ℕ) :
    groupCohomology (Rep.of B.ρ.toRepresentation) q ⟶
      (forget₂ (TopModuleCat.{u} k) (ModuleCat.{u} k)).obj (continuousCohomology q A) :=
  inv (continuousToOrdinary B q) ≫
    (forget₂ (TopModuleCat.{u} k) (ModuleCat.{u} k)).map (ContinuousCohomology.map φ f q)

theorem comparison_comp_discreteStageToContinuous (B : TopRep.{u} k Q)
    (A : TopRep.{u} k G) (φ : G →ₜ* Q) (f : TopRep.res φ B ⟶ A) (q : ℕ) :
    continuousToOrdinary B q ≫ discreteStageToContinuous B A φ f q =
      (forget₂ (TopModuleCat.{u} k) (ModuleCat.{u} k)).map
        (ContinuousCohomology.map φ f q) := by
  unfold discreteStageToContinuous
  rw [← Category.assoc, IsIso.hom_inv_id, Category.id_comp]

/-- An ordinary representation acquires the discrete coefficient topology over a discrete ring. -/
noncomputable def discreteTopRep [DiscreteTopology k] (B : Rep.{u} k Q) : TopRep.{u} k Q := by
  let : TopologicalSpace B := ⊥
  let : DiscreteTopology B := ⟨rfl⟩
  let : ContinuousSMul k B := ⟨continuous_of_discreteTopology⟩
  exact TopRep.of <| ContRepresentation.ofMonoidHom
    { toFun g := ⟨B.ρ g, continuous_of_discreteTopology⟩
      map_one' := by
        apply ContinuousLinearMap.ext
        intro x
        exact LinearMap.congr_fun (map_one B.ρ) x
      map_mul' g h := by
        apply ContinuousLinearMap.ext
        intro x
        exact LinearMap.congr_fun (map_mul B.ρ g h) x }

omit [TopologicalSpace Q] [IsTopologicalGroup Q] [DiscreteTopology Q] in
/-- The preceding construction forgets to exactly the supplied ordinary representation. -/
theorem discreteTopRep_toRep [DiscreteTopology k] (B : Rep.{u} k Q) :
    Rep.of (discreteTopRep B).ρ.toRepresentation = B := rfl

/-- Ordinary discrete-group cohomology, with a concrete compatible coefficient map, enters
actual continuous cohomology in every degree, in particular degree two. -/
noncomputable def ordinaryDiscreteStageToContinuous [DiscreteTopology k]
    (B : Rep.{u} k Q) (A : TopRep.{u} k G)
    (φ : G →ₜ* Q) (f : TopRep.res φ (discreteTopRep B) ⟶ A) (q : ℕ) :
    groupCohomology B q ⟶
      (forget₂ (TopModuleCat.{u} k) (ModuleCat.{u} k)).obj (continuousCohomology q A) :=
  discreteStageToContinuous (discreteTopRep B) A φ f q

section LiftedIntegers

variable (M : Type u) [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
  [DistribMulAction G M] [ContinuousSMul G M] [CompactSpace G] [T2Space G]

/-- An explicit arbitrary-universe instance of the comparison over lifted integers. -/
noncomputable def additiveActionComparisonLinearEquiv (q : ℕ) :
    finiteQuotientCohomology (DiscreteModule.ofAdditiveAction (G := G) M).toRep q ≃ₗ[ULift.{u} ℤ]
      continuousCohomology q (DiscreteModule.ofAdditiveAction (G := G) M).toTopRep :=
  finiteQuotientComparisonLinearEquiv (DiscreteModule.ofAdditiveAction (G := G) M) q

end LiftedIntegers

end Langlands.Continuous
