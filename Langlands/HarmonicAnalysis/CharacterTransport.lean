import Langlands.HarmonicAnalysis.Basic
import Langlands.LocalField.Definitions
import Mathlib.RingTheory.Trace.Basic
import Mathlib.Topology.Algebra.Module.ModuleTopology

/-!
# Character transport and Haar scaling for local constants

Trace pullback and scalar change use the existing nontrivial unitary additive
characters. All continuity and nontriviality certificates are proved.
-/

noncomputable section

universe uF uE uD

namespace Langlands.HarmonicAnalysis.UnitaryAdditiveCharacter

section Additive

variable {F : Type uF} {E : Type uE} {D : Type uD}
  [AddGroup F] [AddGroup E] [AddGroup D]
  [TopologicalSpace F] [TopologicalSpace E] [TopologicalSpace D]

@[ext]
theorem ext {ψ χ : UnitaryAdditiveCharacter F} (h : ∀ x, ψ x = χ x) : ψ = χ := by
  have h' : ψ.toAddChar = χ.toAddChar := AddChar.ext _ _ h
  cases ψ
  cases χ
  cases h'
  rfl

/-- Pullback along an actual continuous surjective additive map preserves
nontriviality. No character is chosen from an existence proposition. -/
def comapSurjective (ψ : UnitaryAdditiveCharacter F) (f : E →+ F)
    (hf : Continuous f) (hsurj : Function.Surjective f) :
    UnitaryAdditiveCharacter E where
  toAddChar := ψ.toAddChar.compAddMonoidHom f
  continuous_toFun := ψ.continuous_toFun.comp hf
  nontrivial := by
    intro h
    apply ψ.nontrivial
    apply AddChar.ext
    intro x
    obtain ⟨y, rfl⟩ := hsurj x
    exact DFunLike.congr_fun h y

@[simp]
theorem comapSurjective_apply (ψ : UnitaryAdditiveCharacter F) (f : E →+ F)
    (hf : Continuous f) (hsurj : Function.Surjective f) (x : E) :
    ψ.comapSurjective f hf hsurj x = ψ (f x) := rfl

@[simp]
theorem comapSurjective_id (ψ : UnitaryAdditiveCharacter F) :
    ψ.comapSurjective (AddMonoidHom.id F) continuous_id Function.surjective_id = ψ := by
  ext x
  rfl

/-- Iterated pullback is pullback along the actual composite. -/
theorem comapSurjective_comp (ψ : UnitaryAdditiveCharacter F)
    (f : E →+ F) (hf : Continuous f) (hsurj : Function.Surjective f)
    (g : D →+ E) (hg : Continuous g) (gsurj : Function.Surjective g) :
    (ψ.comapSurjective f hf hsurj).comapSurjective g hg gsurj =
      ψ.comapSurjective (f.comp g) (hf.comp hg) (hsurj.comp gsurj) := by
  ext x
  rfl

end Additive

section Scalar

variable {F : Type uF} [Field F] [TopologicalSpace F] [IsTopologicalRing F]

/-- The character `x ↦ ψ(a*x)` for an actual nonzero field scalar. -/
def scale (ψ : UnitaryAdditiveCharacter F) (a : Fˣ) :
    UnitaryAdditiveCharacter F :=
  ψ.comapSurjective (AddMonoidHom.mulLeft (a : F))
    (continuous_const.mul continuous_id)
    (fun y => ⟨(↑a⁻¹ : F) * y, by simp⟩)

@[simp]
theorem scale_apply (ψ : UnitaryAdditiveCharacter F) (a : Fˣ) (x : F) :
    ψ.scale a x = ψ ((a : F) * x) := rfl

@[simp]
theorem scale_one (ψ : UnitaryAdditiveCharacter F) : ψ.scale 1 = ψ := by
  ext x
  simp

theorem scale_scale (ψ : UnitaryAdditiveCharacter F) (a b : Fˣ) :
    (ψ.scale a).scale b = ψ.scale (a * b) := by
  ext x
  simp only [scale_apply, Units.val_mul, mul_assoc]

end Scalar

section Trace

variable {F : Type uF} {E : Type uE} [Field F] [Field E] [Algebra F E]
  [FiniteDimensional F E] [Algebra.IsSeparable F E]
  [TopologicalSpace F] [TopologicalSpace E] [IsTopologicalRing F]
  [IsModuleTopology F E]

/-- The actual field-trace pullback of a nontrivial unitary additive character.
The finite separable trace is surjective, and module topology proves continuity. -/
def tracePullback (ψ : UnitaryAdditiveCharacter F) : UnitaryAdditiveCharacter E :=
  ψ.comapSurjective (Algebra.trace F E).toAddMonoidHom
    (IsModuleTopology.continuous_of_linearMap (Algebra.trace F E))
    (Algebra.trace_surjective F E)

@[simp]
theorem tracePullback_apply (ψ : UnitaryAdditiveCharacter F) (x : E) :
    ψ.tracePullback x = ψ (Algebra.trace F E x) := rfl

end Trace

end Langlands.HarmonicAnalysis.UnitaryAdditiveCharacter

namespace Langlands.PadicField.TopologicalData

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} {E : PadicField.{uE} p}
  (TF : F.TopologicalData) (TE : E.TopologicalData)
  [Algebra F.Carrier E.Carrier] [IsScalarTower (Padic p) F.Carrier E.Carrier]

/-- Trace pullback between two actual supplied finite p-adic realizations.
Continuity is proved by restricting scalars to the common p-adic base, so no
additional compatibility of the two supplied topologies is required. -/
def traceCharacter
    (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ TF.topology) :
    @HarmonicAnalysis.UnitaryAdditiveCharacter E.Carrier _ TE.topology := by
  letI := TF.topology
  letI := TE.topology
  letI := TF.valuativeRel
  letI := TE.valuativeRel
  letI := TF.localField
  letI := TE.localField
  letI := TF.moduleTopology
  letI := TE.moduleTopology
  letI : FiniteDimensional F.Carrier E.Carrier :=
    Module.Finite.right (Padic p) F.Carrier E.Carrier
  letI : CharZero F.Carrier := Algebra.charZero_of_charZero (Padic p) F.Carrier
  exact ψ.comapSurjective (Algebra.trace F.Carrier E.Carrier).toAddMonoidHom
    (IsModuleTopology.continuous_of_linearMap
      ((Algebra.trace F.Carrier E.Carrier).restrictScalars (Padic p)))
    (Algebra.trace_surjective F.Carrier E.Carrier)

@[simp]
theorem traceCharacter_apply
    (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ TF.topology) (x : E.Carrier) :
    TF.traceCharacter TE ψ x = ψ (Algebra.trace F.Carrier E.Carrier x) := rfl

end Langlands.PadicField.TopologicalData

namespace Langlands.HarmonicAnalysis.AdditiveHaarMeasure

variable {F : Type uF} [AddGroup F] [TopologicalSpace F] [MeasurableSpace F]

@[ext]
theorem ext {μ ν : AdditiveHaarMeasure F} (h : μ.measure = ν.measure) : μ = ν := by
  cases μ
  cases ν
  cases h
  rfl

variable [IsTopologicalAddGroup F] [BorelSpace F]

/-- Positive finite scaling preserves the actual regular additive Haar measure. -/
def scale (μ : AdditiveHaarMeasure F) (c : NNReal) (hc : 0 < c) :
    AdditiveHaarMeasure F where
  measure := c • μ.measure
  isAddHaar := MeasureTheory.Measure.IsAddHaarMeasure.nnreal_smul μ.measure hc.ne'
  regular := inferInstance

@[simp]
theorem scale_measure (μ : AdditiveHaarMeasure F) (c : NNReal) (hc : 0 < c) :
    (μ.scale c hc).measure = c • μ.measure := rfl

@[simp]
theorem scale_one (μ : AdditiveHaarMeasure F) : μ.scale 1 zero_lt_one = μ := by
  apply ext
  exact one_smul _ _

theorem scale_scale (μ : AdditiveHaarMeasure F) (c d : NNReal) (hc : 0 < c) (hd : 0 < d) :
    (μ.scale c hc).scale d hd = μ.scale (d * c) (mul_pos hd hc) := by
  apply ext
  exact smul_smul _ _ _

end Langlands.HarmonicAnalysis.AdditiveHaarMeasure
