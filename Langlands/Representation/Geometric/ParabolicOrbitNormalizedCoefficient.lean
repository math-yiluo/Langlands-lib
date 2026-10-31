import Langlands.Representation.Geometric.ParabolicOrbitNormalization
import Langlands.Representation.Geometric.ParabolicOrbitNestedAction

/-! The actual normalized orbit coefficient is the refined induction coefficient. -/

noncomputable section
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.Geometric

open GeneralLinear
universe uF uV uW

variable (F : Type uF) [CommRing F] {n : ℕ} (B C : BlockShape n)
  (w : Equiv.Perm (Fin n)) (S : BlockRefinement B) (R : BlockRefinement C)
  (hS : sourceLevi F B C w = refinedLevi F B S)
  (hR : sourceLevi F C B w⁻¹ = refinedLevi F C R)
  {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- The actual inverse-conjugation transport, in the supplied refined Levi coordinates. -/
def refinedIntersectionTransport (ρ : Representation ℂ (refinedLevi F B S) V) :
    Representation ℂ (refinedLevi F C R) V :=
  (intersectionTransport F B C w
    (ρ.comp (MulEquiv.subgroupCongr hS).toMonoidHom)).comp
      (MulEquiv.subgroupCongr hR.symm).toMonoidHom

/-- Transport retains each original linear intertwiner. -/
def refinedIntersectionTransportMap
    {W : Type uW} [AddCommGroup W] [Module ℂ W]
    {ρ : Representation ℂ (refinedLevi F B S) V}
    {τ : Representation ℂ (refinedLevi F B S) W} (f : ρ.IntertwiningMap τ) :
    (refinedIntersectionTransport F B C w S R hS hR ρ).IntertwiningMap
      (refinedIntersectionTransport F B C w S R hS hR τ) where
  toLinearMap := f.toLinearMap
  isIntertwining' m := f.isIntertwining'
    (MulEquiv.subgroupCongr hS
      ((intersectionLeviConjugation F B C w).symm
        (MulEquiv.subgroupCongr hR.symm m)))

end Langlands.Geometric

namespace Langlands.PadicField.TopologicalData

open GeneralLinear Geometric
universe uF uV uW

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
  (T : F.TopologicalData) {n : ℕ} (B C : BlockShape n)
  (w : MinimalRepresentatives B C) (S : BlockRefinement B) (R : BlockRefinement C)
  (hS : IsIntersectionRefinement (F := F.Carrier) B C w.val S)
  (hR : IsIntersectionRefinement (F := F.Carrier) C B w.val⁻¹ R)
  {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- The actual coefficient after quotient integration and target normalization. -/
abbrev parabolicOrbitNormalizedNestedCoefficient
    (ρ : Representation ℂ (B.Levi F.Carrier) V) :=
  letI := T.topology
  letI := T.valuativeRel
  letI := T.localField
  letI := T.fieldT2
  letI := T.generalLinearLocallyCompactSpace n
  twist ((Jacquet.inverseHalfCharacter (T.leviModulus C)).comp
      (parabolicOrbitStagesQuotient F.Carrier B C w.val).subtype)
    (twist (Jacquet.complexCharacter (parabolicOrbitStagesHaarRatio F.Carrier B C w.val))
      (parabolicOrbitNestedCoefficientAction F.Carrier B C w.val (T.leviHalfModulus B) ρ))

/-- The normalized nested coefficient is exactly the pulled-back refined induction
coefficient, with no residual character. -/
def parabolicOrbitNormalizedNestedCoefficientEquiv
    (ρ : Representation ℂ (B.Levi F.Carrier) V) :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    letI := T.fieldT2
    letI := T.generalLinearLocallyCompactSpace n
    (T.parabolicOrbitNormalizedNestedCoefficient B C w ρ).Equiv
      ((twist (T.refinedParabolicHalfModulus C R)
        ((refinedIntersectionTransport F.Carrier B C w.val S R hS.2.1 hR.2.1
          (T.normalizedRefinedJacquet B S ρ)).comp
            (refinedLeviProjection F.Carrier C R))).comp
              (parabolicOrbitStagesRefinedEquiv F.Carrier B C w.val R hR).toMonoidHom) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.fieldT2
  let := T.generalLinearLocallyCompactSpace n
  let e := T.parabolicOrbitNestedRefinedCoefficientActionEquiv B C w.val S R hS hR ρ
  refine { toLinearEquiv := e.toLinearEquiv, isIntertwining' := ?_ }
  intro l
  apply LinearMap.ext
  intro z
  change e ((Jacquet.inverseHalfCharacter (T.leviModulus C) l.val : ℂ) •
      ((Jacquet.complexCharacter (parabolicOrbitStagesHaarRatio F.Carrier B C w.val) l : ℂ) •
        parabolicOrbitNestedCoefficientAction F.Carrier B C w.val (T.leviHalfModulus B) ρ l z)) =
    (T.refinedParabolicHalfModulus C R
      (parabolicOrbitStagesRefinedEquiv F.Carrier B C w.val R hR l) : ℂ) •
        T.normalizedRefinedJacquet B S ρ
          (parabolicOrbitSourceRefinedCoordinate F.Carrier B C w.val R hR S hS l) (e z)
  rw [map_smul, map_smul]
  have he := congrArg (fun f => f z) (e.isIntertwining' l)
  change e (parabolicOrbitNestedCoefficientAction F.Carrier B C w.val
      (T.leviHalfModulus B) ρ l z) =
    (T.parabolicOrbitSectionCharacter B C w.val S R hS hR l : ℂ) •
      T.normalizedRefinedJacquet B S ρ
        (parabolicOrbitSourceRefinedCoordinate F.Carrier B C w.val R hR S hS l) (e z) at he
  rw [he, smul_smul, smul_smul]
  have hc := congrArg (fun a : ℂˣ => (a : ℂ))
    (T.parabolicOrbitNormalization_cancel B C w S R hS hR l)
  simp only [Units.val_mul] at hc
  rw [hc]

@[simp] theorem parabolicOrbitNormalizedNestedCoefficientEquiv_mk
    (ρ : Representation ℂ (B.Levi F.Carrier) V) (v : V) :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    letI := T.fieldT2
    letI := T.generalLinearLocallyCompactSpace n
    T.parabolicOrbitNormalizedNestedCoefficientEquiv B C w S R hS hR ρ
      (Representation.Coinvariants.mk
        (parabolicOrbitNestedCoefficient F.Carrier B C w.val (T.leviHalfModulus B) ρ) v) =
      refinedJacquetMk B S ρ v := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.fieldT2
  let := T.generalLinearLocallyCompactSpace n
  exact T.parabolicOrbitNestedRefinedCoefficientActionEquiv_mk B C w.val S R hS hR ρ v

/-- This coefficient equivalence commutes with every source intertwiner. -/
theorem parabolicOrbitNormalizedNestedCoefficientEquiv_natural
    {W : Type uW} [AddCommGroup W] [Module ℂ W]
    {ρ : Representation ℂ (B.Levi F.Carrier) V}
    {τ : Representation ℂ (B.Levi F.Carrier) W} (f : ρ.IntertwiningMap τ) :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    letI := T.fieldT2
    letI := T.generalLinearLocallyCompactSpace n
    ∀ z : Representation.Coinvariants
      (parabolicOrbitNestedCoefficient F.Carrier B C w.val (T.leviHalfModulus B) ρ),
    T.parabolicOrbitNormalizedNestedCoefficientEquiv B C w S R hS hR τ
      (Representation.Coinvariants.map _ _
        (parabolicOrbitNestedCoefficientMap F.Carrier B C w.val (T.leviHalfModulus B) f) z) =
      T.normalizedRefinedJacquetMap B S f
        (T.parabolicOrbitNormalizedNestedCoefficientEquiv B C w S R hS hR ρ z) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.fieldT2
  let := T.generalLinearLocallyCompactSpace n
  exact T.parabolicOrbitNestedRefinedCoefficientActionEquiv_natural B C w.val S R hS hR f

end Langlands.PadicField.TopologicalData
