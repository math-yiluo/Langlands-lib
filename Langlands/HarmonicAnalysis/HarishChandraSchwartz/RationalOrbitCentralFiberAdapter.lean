import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalOrbitCentralProjection
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.CentralProjection
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.DiscreteSeriesOrbitFiniteness
import Langlands.Representation.Plancherel.SplitComponentLatticeBridge
import Langlands.GroupScheme.Rational.CentralSplitTorusCharacterProof

/-! # Adapters from the VIII.4 targets to the actual orbit central-character fiber

The published VIII.4 targets use a continuous unitary character `χ : A_G →* ℂˣ`, the
predicate `classActsByCharacter` and a split component `s`. The `M = G` packet calculation
of `RationalOrbitCentralProjection` uses a circle-valued character, the orbit fiber
`rationalOrbitCentralFiber` and the finite-index premise on the split valuation image.
This module supplies the three conversions.
-/

noncomputable section

open MeasureTheory

namespace Langlands.HarishChandraSchwartz

universe u uV uG

open Langlands.Plancherel

section Character

variable {A : Type*} [Group A]

/-- A unitary character `A →* ℂˣ` viewed as a character with values in the unit circle. -/
def unitaryCircleCharacter (χ : A →* ℂˣ) (hχ : ∀ a, ‖(χ a : ℂ)‖ = 1) : A →* Circle where
  toFun a := ⟨(χ a : ℂ), by
    change (χ a : ℂ) ∈ Metric.sphere 0 1
    exact mem_sphere_zero_iff_norm.mpr (hχ a)⟩
  map_one' := by
    apply Circle.ext
    simp
  map_mul' a b := by
    apply Circle.ext
    change (χ (a * b) : ℂ) = (χ a : ℂ) * (χ b : ℂ)
    simp

@[simp]
theorem coe_unitaryCircleCharacter (χ : A →* ℂˣ) (hχ : ∀ a, ‖(χ a : ℂ)‖ = 1) (a : A) :
    ((unitaryCircleCharacter χ hχ a : Circle) : ℂ) = (χ a : ℂ) :=
  rfl

theorem continuous_unitaryCircleCharacter [TopologicalSpace A] {χ : A →* ℂˣ}
    (hχ : ∀ a, ‖(χ a : ℂ)‖ = 1) (hc : Continuous χ) :
    Continuous (unitaryCircleCharacter χ hχ) :=
  (Units.continuous_val.comp hc).subtype_mk _

end Character

section Projection

variable {Γ : Type uG} [Group Γ] {A : Subgroup Γ} [MeasurableSpace A]

/-- Waldspurger's `p_χ` written with the circle-valued character, in the form used by
`integral_central_rationalOrbitWavePacket`. -/
theorem centralProjection_eq_integral_unitaryCircleCharacter (μA : Measure A)
    (χ : A →* ℂˣ) (hχ : IsUnitaryCharacter χ) (f : Γ → ℂ) (g : Γ) :
    centralProjection μA χ f g =
      ∫ a, ((unitaryCircleCharacter χ hχ.norm_eq_one a⁻¹ : Circle) : ℂ) * f ((a : Γ) * g)
        ∂μA := by
  unfold centralProjection
  congr 1
  funext a
  rw [coe_unitaryCircleCharacter, map_inv]

end Projection

section Classes

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (A : Subgroup G) [A.Normal] (hA : A ≤ Subgroup.center G)
  [MeasurableSpace (G ⧸ A)] (μ : Measure (G ⧸ A)) [μ.IsHaarMeasure]

/-- The actual central character of a discrete-series class, restricted to `A`, is the
circle character of `χ` exactly when `A` acts on the class by `χ`. -/
theorem discreteSeriesCentralRestriction_eq_unitaryCircleCharacter_iff
    (ω : DiscreteSeriesClass.{uG, uV} A hA μ) (χ : A →* ℂˣ)
    (hχ : ∀ a, ‖(χ a : ℂ)‖ = 1) :
    discreteSeriesCentralRestriction A hA μ A hA ω = unitaryCircleCharacter χ hχ ↔
      classActsByCharacter A χ ω.val := by
  have hc := discreteSeriesCentralCharacter_hasCentralCharacter A hA μ ω
  rcases ω with ⟨ω, hω⟩
  induction ω using Quotient.inductionOn with
  | h π =>
    change ∀ (z : Subgroup.center G) (v : π.obj),
      π.obj.representation (z : G) v =
        (discreteSeriesCentralCharacter A hA μ ⟨Quotient.mk _ π, hω⟩ z : ℂ) • v at hc
    change _ ↔ ∀ (a : A) (v : π.obj), π.obj.representation (a : G) v = (χ a : ℂ) • v
    constructor
    · intro h a v
      have ha := congrArg (fun φ : A →* Circle => ((φ a : Circle) : ℂ)) h
      change (discreteSeriesCentralCharacter A hA μ ⟨Quotient.mk _ π, hω⟩
        (Subgroup.inclusion hA a) : ℂ) = (χ a : ℂ) at ha
      rw [← ha]
      exact hc (Subgroup.inclusion hA a) v
    · intro h
      have : Nontrivial π.obj := by
        have hirr : Representation.IsIrreducible π.obj.representation := π.property.1
        have : IsSimpleModule (MonoidAlgebra ℂ G) π.obj.representation.asModule :=
          (Representation.irreducible_iff_isSimpleModule_asModule _).mp hirr
        exact IsSimpleModule.nontrivial (MonoidAlgebra ℂ G) π.obj.representation.asModule
      obtain ⟨v, hv⟩ := exists_ne (0 : π.obj)
      ext a
      change (discreteSeriesCentralCharacter A hA μ ⟨Quotient.mk _ π, hω⟩
        (Subgroup.inclusion hA a) : ℂ) = (χ a : ℂ)
      have h1 := hc (Subgroup.inclusion hA a) v
      have h2 := h a v
      change π.obj.representation (a : G) v = _ at h1
      rw [h2] at h1
      exact (smul_left_injective ℂ hv h1).symm

end Classes

section Rational

open _root_.CategoryTheory _root_.AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology
open scoped CategoryTheory.MonObj

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
variable {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffine G.X.left]
  [LocallyOfFiniteType G.X.hom]

local instance instRationalOrbitCentralFiberAdapter1 :
    TopologicalSpace (GroupScheme.rationalPoints G) :=
  rationalPointTopology F G.X
local instance instRationalOrbitCentralFiberAdapter2 :
    NonarchimedeanGroup (GroupScheme.rationalPoints G) :=
  rationalPoints_nonarchimedeanGroup G

variable {T : CommGroupScheme (Spec (CommRingCat.of F))}
  (s : T.toGrp ⟶ G) (hs : GroupScheme.IsCentral s)
  [MeasurableSpace (GroupScheme.rationalPoints G ⧸ (GroupScheme.rationalPoints.map s).range)]
  (mu : Measure (GroupScheme.rationalPoints G ⧸ (GroupScheme.rationalPoints.map s).range))

/-- A class of the orbit lies in the fiber of the circle character of `χ` exactly when the
split-component image acts on it by `χ`. -/
theorem mem_rationalOrbitCentralFiber_unitaryCircleCharacter_iff :
    letI := (GroupScheme.rationalPoints.map s).range.normal_of_le_center hs.range_le_center
    ∀ [Measure.IsHaarMeasure mu]
      (omega : DiscreteSeriesClass.{u, uV}
        (GroupScheme.rationalPoints.map s).range hs.range_le_center mu)
      (χ : (GroupScheme.rationalPoints.map s).range →* ℂˣ) (hχ : ∀ a, ‖(χ a : ℂ)‖ = 1)
      (x : discreteSeriesOrbit (GroupScheme.rationalPoints.map s).range hs.range_le_center mu
        (fun psi => (rationalNormCharacters G psi).toMul) omega),
      x ∈ rationalOrbitCentralFiber s hs mu omega (unitaryCircleCharacter χ hχ) ↔
        classActsByCharacter (GroupScheme.rationalPoints.map s).range χ x.val.val := by
  let := (GroupScheme.rationalPoints.map s).range.normal_of_le_center hs.range_le_center
  intro _ omega χ hχ x
  exact discreteSeriesCentralRestriction_eq_unitaryCircleCharacter_iff
    (GroupScheme.rationalPoints.map s).range hs.range_le_center mu x.val χ hχ

/-- The base class of its own orbit lies in the fiber of `χ` exactly when the split-component
image acts on it by `χ`. -/
theorem self_mem_rationalOrbitCentralFiber_unitaryCircleCharacter_iff :
    letI := (GroupScheme.rationalPoints.map s).range.normal_of_le_center hs.range_le_center
    ∀ [Measure.IsHaarMeasure mu]
      (omega : DiscreteSeriesClass.{u, uV}
        (GroupScheme.rationalPoints.map s).range hs.range_le_center mu)
      (χ : (GroupScheme.rationalPoints.map s).range →* ℂˣ) (hχ : ∀ a, ‖(χ a : ℂ)‖ = 1),
      (⟨omega, MulAction.mem_orbit_self omega⟩ :
          discreteSeriesOrbit (GroupScheme.rationalPoints.map s).range hs.range_le_center mu
            (fun psi => (rationalNormCharacters G psi).toMul) omega) ∈
          rationalOrbitCentralFiber s hs mu omega (unitaryCircleCharacter χ hχ) ↔
        classActsByCharacter (GroupScheme.rationalPoints.map s).range χ omega.val := by
  let := (GroupScheme.rationalPoints.map s).range.normal_of_le_center hs.range_le_center
  intro _ omega χ hχ
  exact mem_rationalOrbitCentralFiber_unitaryCircleCharacter_iff s hs mu omega χ hχ _

end Rational

section Index

open _root_.CategoryTheory _root_.AlgebraicGeometry
open Langlands.GroupScheme

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} {T : CommGroupScheme (Spec (CommRingCat.of F))}

/-- The finite-index premise of the actual orbit calculations holds for every split
component of a connected reductive group: rational-character restriction to a split
component is injective by the published central split torus character theorem. -/
theorem finiteIndex_splitValuationImage_of_isSplitComponent
    (hG : IsConnectedReductive G) (s : T.toGrp ⟶ G) (hs : IsSplitComponent s) :
    (RenardCartan.splitValuationImage s).FiniteIndex :=
  RenardCartan.finiteIndex_splitValuationImage_of_injective hG s hs
    (characterRestrict_injective_of_centralSplitTorusCharacter centralSplitTorusCharacter hG hs)

end Index

end Langlands.HarishChandraSchwartz
