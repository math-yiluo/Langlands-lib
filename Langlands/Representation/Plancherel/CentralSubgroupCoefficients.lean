import Langlands.Representation.Twist.UnitaryModCenterProof
import Langlands.Representation.Classification.Essential
import Mathlib.Topology.Algebra.ContinuousMonoidHom

/-!
# Matrix coefficients modulo a prescribed central subgroup

The quotient subgroup is explicit. The Waldspurger specialization must use the
actual rational points of the maximal split central torus.
-/

noncomputable section

namespace Langlands.Plancherel

universe uG uV uW

variable {G : Type uG} [Group G] [TopologicalSpace G]
variable (A : Subgroup G) [A.Normal] (hA : A ≤ Subgroup.center G)

/-- The actual projection from the smaller central quotient to the full one. -/
def centralQuotientProjection : (G ⧸ A) →ₜ* (G ⧸ Subgroup.center G) where
  toMonoidHom := QuotientGroup.map A (Subgroup.center G) (MonoidHom.id G) hA
  continuous_toFun := by
    apply (QuotientGroup.isQuotientMap_mk A).continuous_iff.mpr
    exact QuotientGroup.continuous_mk

@[simp]
theorem centralQuotientProjection_mk (g : G) :
    centralQuotientProjection A hA (QuotientGroup.mk g) = QuotientGroup.mk g := rfl

variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
variable {W : Type uW} [AddCommGroup W] [Module ℂ W]
variable {ρ : Representation ℂ G V} {σ : Representation ℂ G W}

/-- The norm of the actual matrix coefficient on `G/A`, obtained by pulling
back its norm on `G/Z(G)` along the actual quotient projection. -/
def centralSubgroupCoefficientNorm (c : UnitaryCentralCharacter ρ)
    (ℓ : Module.Dual ℂ V) (v : V) : G ⧸ A → ℝ :=
  c.coefficientNorm ℓ v ∘ centralQuotientProjection A hA

@[simp]
theorem centralSubgroupCoefficientNorm_mk (c : UnitaryCentralCharacter ρ)
    (ℓ : Module.Dual ℂ V) (v : V) (g : G) :
    centralSubgroupCoefficientNorm A hA c ℓ v (QuotientGroup.mk g) =
      ‖matrixCoefficient ρ ℓ v g‖ := rfl

theorem centralSubgroupCoefficientNorm_eq (c d : UnitaryCentralCharacter ρ)
    (ℓ : Module.Dual ℂ V) (v : V) :
    centralSubgroupCoefficientNorm A hA c ℓ v =
      centralSubgroupCoefficientNorm A hA d ℓ v := by
  unfold centralSubgroupCoefficientNorm
  rw [c.coefficientNorm_eq d]

theorem centralSubgroupCoefficientNorm_ofEquiv (c : UnitaryCentralCharacter ρ)
    (e : ρ.Equiv σ) (ℓ : Module.Dual ℂ W) (w : W) :
    centralSubgroupCoefficientNorm A hA (c.ofEquiv e) ℓ w =
      centralSubgroupCoefficientNorm A hA c
        (ℓ.comp e.toLinearEquiv.toLinearMap) (e.symm w) := by
  unfold centralSubgroupCoefficientNorm
  rw [c.coefficientNorm_ofEquiv e]

variable [IsTopologicalGroup G]

/-- Norms of the coefficient functions on the prescribed quotient are unchanged
by a norm-one smooth twist. -/
theorem centralSubgroupCoefficientNorm_unitaryTwist (c : UnitaryCentralCharacter ρ)
    (χ : G →* ℂˣ) (hχ : IsOpen (χ.ker : Set G))
    (hu : ∀ g : G, ‖(χ g : ℂ)‖ = 1) (ℓ : Module.Dual ℂ V) (v : V) :
    centralSubgroupCoefficientNorm A hA (c.unitaryTwist χ hχ hu) ℓ v =
      centralSubgroupCoefficientNorm A hA c ℓ v := by
  unfold centralSubgroupCoefficientNorm
  rw [c.coefficientNorm_unitaryTwist χ hχ hu]

variable [MeasurableSpace (G ⧸ A)]

/-- Square-integrability of all smooth-dual matrix coefficients modulo the
specified actual central subgroup, for an admissible representation with a
unitary character of the full center. -/
def IsSquareIntegrableModCentralSubgroup (ρ : Representation ℂ G V)
    (μ : MeasureTheory.Measure (G ⧸ A)) [MeasureTheory.Measure.IsHaarMeasure μ] : Prop :=
  IsAdmissible ρ ∧ ∃ c : UnitaryCentralCharacter ρ,
    ∀ (ℓ : SmoothDual ρ) (v : V),
      MeasureTheory.MemLp (centralSubgroupCoefficientNorm A hA c ℓ v) 2 μ

theorem isSquareIntegrableModCentralSubgroup_of_equiv (e : ρ.Equiv σ)
    (μ : MeasureTheory.Measure (G ⧸ A)) [MeasureTheory.Measure.IsHaarMeasure μ]
    (hρ : IsSquareIntegrableModCentralSubgroup A hA ρ μ) :
    IsSquareIntegrableModCentralSubgroup A hA σ μ := by
  obtain ⟨hρ, c, hc⟩ := hρ
  refine ⟨isAdmissible_of_equiv e hρ, c.ofEquiv e, ?_⟩
  intro ℓ w
  rw [centralSubgroupCoefficientNorm_ofEquiv]
  exact hc (contragredientMap e.toIntertwiningMap ℓ) (e.symm w)

theorem isSquareIntegrableModCentralSubgroup_iff_of_equiv (e : ρ.Equiv σ)
    (μ : MeasureTheory.Measure (G ⧸ A)) [MeasureTheory.Measure.IsHaarMeasure μ] :
    IsSquareIntegrableModCentralSubgroup A hA ρ μ ↔
      IsSquareIntegrableModCentralSubgroup A hA σ μ :=
  ⟨isSquareIntegrableModCentralSubgroup_of_equiv A hA e μ,
    isSquareIntegrableModCentralSubgroup_of_equiv A hA e.symm μ⟩

theorem isSquareIntegrableModCentralSubgroup_unitaryTwist
    (χ : G →* ℂˣ) (hχ : IsOpen (χ.ker : Set G))
    (hu : ∀ g : G, ‖(χ g : ℂ)‖ = 1)
    (μ : MeasureTheory.Measure (G ⧸ A)) [MeasureTheory.Measure.IsHaarMeasure μ]
    (hρ : IsSquareIntegrableModCentralSubgroup A hA ρ μ) :
    IsSquareIntegrableModCentralSubgroup A hA (twist χ ρ) μ := by
  obtain ⟨hρ, c, hc⟩ := hρ
  refine ⟨(isAdmissible_twist_iff χ ρ hχ).mpr hρ, c.unitaryTwist χ hχ hu, ?_⟩
  intro ℓ v
  rw [centralSubgroupCoefficientNorm_unitaryTwist]
  exact hc (smoothContragredientTwistEquiv χ ρ hχ ℓ) v

end Langlands.Plancherel
