import Langlands.GroupTheory.CocycleMap
import Mathlib.Algebra.Module.ULift

/-! # Normalized multiplicative cocycles and actual group cohomology -/

noncomputable section

namespace Langlands.NormalizedTwoCocycle

universe u

/-- The integers lifted to the universe required by Mathlib's cohomology category. -/
abbrev CoefficientScalars := ULift.{u} ℤ

/-- The scalar ring is explicitly isomorphic to the ordinary integers. -/
def coefficientScalarsEquiv : CoefficientScalars.{u} ≃+* ℤ := ULift.ringEquiv

variable (G A : Type u) [Group G] [CommGroup A] [MulDistribMulAction G A]

/-- The actual additive coefficient module for the given multiplicative action. -/
def coefficientRepresentation : Rep.{u} CoefficientScalars.{u} G :=
  Rep.of
    { toFun g := ((Rep.ofMulDistribMulAction G A).ρ g).restrictScalars
        CoefficientScalars.{u}
      map_one' := by
        ext a
        exact LinearMap.congr_fun (map_one (Rep.ofMulDistribMulAction G A).ρ) a
      map_mul' g h := by
        ext a
        exact LinearMap.congr_fun (map_mul (Rep.ofMulDistribMulAction G A).ρ g h) a }

@[simp] theorem coefficientRepresentation_apply (g : G) (a : Additive A) :
    (coefficientRepresentation G A).ρ g a = Additive.ofMul (g • a.toMul) := rfl

/-- The one-cochain differential agrees exactly with the multiplicative convention. -/
theorem differential₁₂ (b : G → A) (g h : G) :
    groupCohomology.d₁₂ (coefficientRepresentation G A) (Additive.ofMul ∘ b) (g, h) =
      Additive.ofMul ((g • b h) / b (g * h) * b g) := rfl

/-- The two-cochain differential agrees exactly with the multiplicative convention. -/
theorem differential₂₃ (f : G × G → A) (g h j : G) :
    groupCohomology.d₂₃ (coefficientRepresentation G A) (Additive.ofMul ∘ f) (g, h, j) =
      Additive.ofMul ((g • f (h, j)) / f (g * h, j) * f (g, h * j) / f (g, h)) := rfl

theorem mem_cocycles₂_iff (f : G × G → A) :
    (Additive.ofMul ∘ f) ∈ groupCohomology.cocycles₂ (coefficientRepresentation G A) ↔
      groupCohomology.IsMulCocycle₂ f :=
  groupCohomology.mem_cocycles₂_iff _

variable {G A}

/-- A normalized multiplicative cocycle as an actual cocycle of the additive complex. -/
def toCocycle₂ (c : NormalizedTwoCocycle G A) :
    groupCohomology.cocycles₂ (coefficientRepresentation G A) :=
  ⟨Additive.ofMul ∘ c, (mem_cocycles₂_iff G A c).2 c.cocycle⟩

@[simp] theorem toCocycle₂_apply (c : NormalizedTwoCocycle G A) (g h : G) :
    toCocycle₂ c (g, h) = Additive.ofMul (c (g, h)) := rfl

/-- The class in Mathlib's second group cohomology, with no arithmetic class selected. -/
def cohomologyClass (c : NormalizedTwoCocycle G A) :
    groupCohomology (coefficientRepresentation G A) 2 :=
  groupCohomology.H2π (coefficientRepresentation G A) (toCocycle₂ c)

/-- Normalize an actual additive cocycle by subtracting the boundary of its constant cochain. -/
def normalizedRepresentative
    (f : groupCohomology.cocycles₂ (coefficientRepresentation G A)) :
    NormalizedTwoCocycle G A where
  toFun gh := @Additive.toMul A ((f -
    ⟨groupCohomology.d₁₂ (coefficientRepresentation G A) (fun _ => f (1, 1)),
      groupCohomology.d₁₂_apply_mem_cocycles₂ _⟩) gh)
  cocycle := by
    let f' : groupCohomology.cocycles₂ (coefficientRepresentation G A) :=
      f - ⟨groupCohomology.d₁₂ (coefficientRepresentation G A) (fun _ => f (1, 1)),
        groupCohomology.d₁₂_apply_mem_cocycles₂ _⟩
    intro g h j
    exact (groupCohomology.mem_cocycles₂_iff f').1 f'.property g h j
  normalized := by
    change f (1, 1) -
      groupCohomology.d₁₂ (coefficientRepresentation G A) (fun _ => f (1, 1)) (1, 1) = 0
    simp [groupCohomology.d₁₂_hom_apply]

theorem normalizedRepresentative_apply
    (f : groupCohomology.cocycles₂ (coefficientRepresentation G A)) (g h : G) :
    normalizedRepresentative f (g, h) =
      @Additive.toMul A (f (g, h)) /
        (g • @Additive.toMul A (f (1, 1))) := by
  change @Additive.toMul A (f (g, h) -
    ((coefficientRepresentation G A).ρ g (f (1, 1)) - f (1, 1) + f (1, 1)) :
      Additive A) = _
  rw [sub_add_cancel]
  rfl

theorem cohomologyClass_normalizedRepresentative
    (f : groupCohomology.cocycles₂ (coefficientRepresentation G A)) :
    cohomologyClass (normalizedRepresentative f) =
      groupCohomology.H2π (coefficientRepresentation G A) f := by
  change groupCohomology.H2π (coefficientRepresentation G A)
    (f - ⟨groupCohomology.d₁₂ (coefficientRepresentation G A) (fun _ => f (1, 1)),
      groupCohomology.d₁₂_apply_mem_cocycles₂ _⟩) = _
  rw [map_sub]
  have hb : groupCohomology.H2π (coefficientRepresentation G A)
      ⟨groupCohomology.d₁₂ (coefficientRepresentation G A) (fun _ => f (1, 1)),
        groupCohomology.d₁₂_apply_mem_cocycles₂ _⟩ = 0 :=
    (groupCohomology.H2π_eq_zero_iff _).2 ⟨fun _ => f (1, 1), rfl⟩
  rw [hb, sub_zero]

/-- Every actual second cohomology class admits a normalized multiplicative representative. -/
theorem cohomologyClass_surjective :
    Function.Surjective (cohomologyClass (G := G) (A := A)) := by
  intro x
  induction x using groupCohomology.H2_induction_on with
  | h f =>
    exact ⟨normalizedRepresentative f, cohomologyClass_normalizedRepresentative f⟩

/-- The explicit cochain equation implies equality of the actual cohomology classes. -/
theorem cohomologyClass_eq_of_cochain (c d : NormalizedTwoCocycle G A)
    (b : G → A)
    (hb : ∀ g h, c (g, h) * b (g * h) = b g * (g • b h) * d (g, h)) :
    cohomologyClass c = cohomologyClass d := by
  apply (groupCohomology.H2π_eq_iff _ _).2
  refine ⟨Additive.ofMul ∘ b, ?_⟩
  funext ⟨g, h⟩
  change Additive.ofMul ((g • b h) / b (g * h) * b g) =
    Additive.ofMul (c (g, h) / d (g, h))
  apply congrArg Additive.ofMul
  apply eq_div_iff_mul_eq'.2
  have he := hb g h
  calc
    (g • b h) / b (g * h) * b g * d (g, h) =
        (b g * (g • b h) * d (g, h)) / b (g * h) := by
          simp only [div_eq_mul_inv]
          ac_rfl
    _ = c (g, h) := by rw [← he, mul_div_cancel_right]

namespace MapData

/-- The existing identity-component extension map data give the same cohomology class. -/
theorem cohomologyClass_eq {c d : NormalizedTwoCocycle G A}
    (m : MapData c d (MonoidHom.id A) (MonoidHom.id G)) :
    cohomologyClass c = cohomologyClass d :=
  cohomologyClass_eq_of_cochain c d m.cochain m.compatible

end MapData

end Langlands.NormalizedTwoCocycle
