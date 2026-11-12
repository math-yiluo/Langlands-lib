import Langlands.Representation.Hecke.HomomorphismRight
import Langlands.Representation.Induction.Definitions
import Langlands.Topology.Nonarchimedean.Subgroup

/-! # The actual compact-induction models in Renard III.2.6

The relative modular character and both functors compared by (III.2.6.2).
-/

noncomputable section

open CategoryTheory MeasureTheory MulOpposite

namespace Langlands.Hecke.Homomorphism

open Langlands.Algebra

universe uG uH v

section Character

variable {G : Type uG} [Group G] [TopologicalSpace G]
  [NonarchimedeanGroup G] [LocallyCompactSpace G]
  {H : Type uH} [Group H] [TopologicalSpace H]
  [NonarchimedeanGroup H] [LocallyCompactSpace H]
  (φ : H →* G) (hφ : Continuous φ)

/-- The relative character `δG(φ(h))/δH(h) = ΔH(h)/ΔG(φ(h))`.
For a closed subgroup this is Renard's `δ_{H\G}`. -/
def relativeModularCharacter : Induction.SmoothCharacter ℂ H where
  toMonoidHom := (haarScale (G := H)).toHomUnits *
    ((haarScale (G := G)).comp φ).toHomUnits⁻¹
  isOpen_ker := by
    have hlc : IsLocallyConstant
        (fun h : H => haarScale h * haarScale (φ h⁻¹)) :=
      haarScale_locallyConstant.mul
        (haarScale_locallyConstant.comp_continuous (hφ.comp continuous_inv))
    have he : (((haarScale (G := H)).toHomUnits *
        ((haarScale (G := G)).comp φ).toHomUnits⁻¹).ker : Set H) =
        {h | haarScale h * haarScale (φ h⁻¹) = 1} := by
      ext h
      change (_ : ℂˣ) = 1 ↔ _
      exact Units.ext_iff
    rw [he]
    exact hlc.isOpen_fiber 1

@[simp] theorem relativeModularCharacter_apply (h : H) :
    ((relativeModularCharacter φ hφ).toMonoidHom h : ℂ) =
      haarScale h * haarScale (φ h⁻¹) := rfl

end Character

section Models

variable {G : Type uG} [Group G] [TopologicalSpace G] [T2Space G]
  [NonarchimedeanGroup G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
  (μG : Measure G) [μG.IsHaarMeasure]
  (H : Subgroup G) [LocallyCompactSpace H]
  (μH : Measure H) [μH.IsHaarMeasure]

/-- The actual Hecke tensor induction of a smooth representation. -/
abbrev tensorInductionHeckeFunctor :
    Langlands.SmoothRep.{0, uG, v} ℂ H ⥤
      NondegenerateModuleCat.{uG, max uG v} (HeckeAlgebra μG) :=
  heckeNondegenerateModuleFunctor μH ⋙ P μG μH H.subtype continuous_subtype_val

/-- Actual compact function induction with the precise relative modular twist,
followed by the existing Hecke functor. -/
abbrev compactModularHeckeFunctor :
    Langlands.SmoothRep.{0, uG, v} ℂ H ⥤
      NondegenerateModuleCat.{uG, max uG v} (HeckeAlgebra μG) :=
  Langlands.SmoothRep.toRep ⋙
    Induction.normalizedCompactInductionFunctor H
      (relativeModularCharacter H.subtype continuous_subtype_val) ⋙
    heckeNondegenerateModuleFunctor μG

/-- The original elementary tensor in the exact balanced quotient used by `P`. -/
def tensorInductionTmul (W : Langlands.SmoothRep.{0, uG, v} ℂ H)
    (T : HeckeAlgebra μG) (w : W) :
    ((tensorInductionHeckeFunctor μG H μH).obj W).obj := by
  letI := rightModule μG μH H.subtype continuous_subtype_val
  letI := heckeNonUnitalModule μH W.representation W.isSmooth
  exact NonUnitalModuleTensor.tmul (HeckeAlgebra μH) (HeckeAlgebra μG) W T w

end Models

end Langlands.Hecke.Homomorphism
