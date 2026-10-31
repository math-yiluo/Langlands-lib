import Langlands.Representation.Geometric.ParabolicOrbitSectionComparison
import Langlands.Representation.Induction.SplitKernelCovariance

/-! The actual nested section action and its refined coefficient comparison. -/

noncomputable section

namespace Langlands.Geometric

open GeneralLinear Induction

universe uF uV uW

variable (F : Type uF) [CommRing F] [TopologicalSpace F] [IsTopologicalRing F]
  {n : ℕ} (B C : BlockShape n) (w : Equiv.Perm (Fin n))

omit [TopologicalSpace F] [IsTopologicalRing F] in
/-- The full section takes values in the actual nested stabilizer. -/
theorem parabolicOrbitNestedSection_mem (l : parabolicOrbitStagesQuotient F B C w) :
    (C.leviInParabolic F).subgroupComap (parabolicOrbitStages F B C w) l ∈
      parabolicOrbitNestedStabilizer F B C w :=
  parabolicOrbitStages_section_mem F B C w l

variable {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- The genuine action supplied by section covariance of the inner quotient integral. -/
abbrev parabolicOrbitNestedCoefficientAction (χ : B.Levi F →* ℂˣ)
    (ρ : Representation ℂ (B.Levi F) V) :
    Representation ℂ (parabolicOrbitStagesQuotient F B C w)
      (Representation.Coinvariants (parabolicOrbitNestedCoefficient F B C w χ ρ)) :=
  splitKernelCoefficientAction (parabolicOrbitStagesRetraction F B C w)
    ((C.leviInParabolic F).subgroupComap (parabolicOrbitStages F B C w))
    (parabolicOrbitNestedStabilizer F B C w)
    (parabolicOrbitNestedSection_mem F B C w)
    ((parabolicOrbitCoefficient F B C w χ ρ).comp
      (parabolicOrbitNestedInclusion F B C w))

@[simp] theorem parabolicOrbitNestedCoefficientAction_mk (χ : B.Levi F →* ℂˣ)
    (ρ : Representation ℂ (B.Levi F) V)
    (l : parabolicOrbitStagesQuotient F B C w) (v : V) :
    parabolicOrbitNestedCoefficientAction F B C w χ ρ l
        (Representation.Coinvariants.mk (parabolicOrbitNestedCoefficient F B C w χ ρ) v) =
      Representation.Coinvariants.mk (parabolicOrbitNestedCoefficient F B C w χ ρ)
        (parabolicOrbitCoefficient F B C w χ ρ
          (parabolicOrbitStagesSection F B C w l) v) := rfl

/-- Removing intermediate subgroup inclusions intertwines the actual section actions. -/
def parabolicOrbitNestedFullCoefficientActionEquiv (χ : B.Levi F →* ℂˣ)
    (ρ : Representation ℂ (B.Levi F) V) :
    (parabolicOrbitNestedCoefficientAction F B C w χ ρ).Equiv
      (parabolicOrbitFullCoefficientAction F B C w χ ρ) where
  toLinearEquiv := splitStagesCoefficientEquiv
    (C.leviProjection F) (C.leviInParabolic F) (C.leviProjection_section F)
    (parabolicOrbitStages F B C w) (parabolicOrbitStabilizer F B C w)
    (parabolicOrbitStages_kernel_le F B C w)
    (parabolicOrbitStabilizer_le_stages F B C w)
    (parabolicOrbitCoefficient F B C w χ ρ)
  isIntertwining' l := by
    apply Representation.Coinvariants.hom_ext
    ext v
    rfl

@[simp] theorem parabolicOrbitNestedFullCoefficientActionEquiv_mk
    (χ : B.Levi F →* ℂˣ) (ρ : Representation ℂ (B.Levi F) V) (v : V) :
    parabolicOrbitNestedFullCoefficientActionEquiv F B C w χ ρ
        (Representation.Coinvariants.mk (parabolicOrbitNestedCoefficient F B C w χ ρ) v) =
      Jacquet.mk (parabolicOrbitCoefficient F B C w χ ρ)
        (parabolicOrbitCoefficientRadical F B C w) v := rfl

/-- Every original coefficient map commutes with the actual nested section action. -/
theorem parabolicOrbitNestedCoefficientAction_natural
    {W : Type uW} [AddCommGroup W] [Module ℂ W]
    (χ : B.Levi F →* ℂˣ)
    {ρ : Representation ℂ (B.Levi F) V} {τ : Representation ℂ (B.Levi F) W}
    (f : ρ.IntertwiningMap τ) (l : parabolicOrbitStagesQuotient F B C w)
    (z : Representation.Coinvariants (parabolicOrbitNestedCoefficient F B C w χ ρ)) :
    Representation.Coinvariants.map _ _ (parabolicOrbitNestedCoefficientMap F B C w χ f)
        (parabolicOrbitNestedCoefficientAction F B C w χ ρ l z) =
      parabolicOrbitNestedCoefficientAction F B C w χ τ l
        (Representation.Coinvariants.map _ _
          (parabolicOrbitNestedCoefficientMap F B C w χ f) z) := by
  induction z using Representation.Coinvariants.induction_on with
  | h v =>
    change Representation.Coinvariants.mk (parabolicOrbitNestedCoefficient F B C w χ τ)
        (f (parabolicOrbitCoefficient F B C w χ ρ (parabolicOrbitStagesSection F B C w l) v)) =
      Representation.Coinvariants.mk (parabolicOrbitNestedCoefficient F B C w χ τ)
        (parabolicOrbitCoefficient F B C w χ τ (parabolicOrbitStagesSection F B C w l) (f v))
    exact congrArg (Representation.Coinvariants.mk _)
      (Representation.IntertwiningMap.isIntertwining _ _
        (parabolicOrbitCoefficientMap F B C w χ f) (parabolicOrbitStagesSection F B C w l) v)

end Langlands.Geometric

namespace Langlands.PadicField.TopologicalData

open GeneralLinear Geometric Induction

universe uF uV uW

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
  (T : F.TopologicalData) {n : ℕ} (B C : BlockShape n)
  (w : Equiv.Perm (Fin n)) (S : BlockRefinement B) (R : BlockRefinement C)
  (hS : IsIntersectionRefinement (F := F.Carrier) B C w S)
  (hR : IsIntersectionRefinement (F := F.Carrier) C B w⁻¹ R)
  {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- The action on the actual nested quotient is projected normalized refined
Jacquet with the two explicit positive source half moduli. -/
def parabolicOrbitNestedRefinedCoefficientActionEquiv
    (ρ : Representation ℂ (B.Levi F.Carrier) V) :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    (parabolicOrbitNestedCoefficientAction F.Carrier B C w (T.leviHalfModulus B) ρ).Equiv
      (twist (T.parabolicOrbitSectionCharacter B C w S R hS hR)
        ((T.normalizedRefinedJacquet B S ρ).comp
          (parabolicOrbitSourceRefinedCoordinate F.Carrier B C w R hR S hS))) := by
  letI := T.topology
  letI := T.valuativeRel
  letI := T.localField
  exact (parabolicOrbitNestedFullCoefficientActionEquiv F.Carrier B C w
    (T.leviHalfModulus B) ρ).trans
      (T.parabolicOrbitFullRefinedCoefficientActionEquiv B C w S R hS hR ρ)

@[simp] theorem parabolicOrbitNestedRefinedCoefficientActionEquiv_mk
    (ρ : Representation ℂ (B.Levi F.Carrier) V) (v : V) :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    T.parabolicOrbitNestedRefinedCoefficientActionEquiv B C w S R hS hR ρ
        (Representation.Coinvariants.mk
          (parabolicOrbitNestedCoefficient F.Carrier B C w (T.leviHalfModulus B) ρ) v) =
      refinedJacquetMk B S ρ v := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  change T.parabolicOrbitFullRefinedCoefficientActionEquiv B C w S R hS hR ρ
    (Jacquet.mk _ _ v) = _
  exact T.parabolicOrbitFullRefinedCoefficientActionEquiv_mk B C w S R hS hR ρ v

/-- The normalized action equivalence is natural for all original coefficient maps. -/
theorem parabolicOrbitNestedRefinedCoefficientActionEquiv_natural
    {W : Type uW} [AddCommGroup W] [Module ℂ W]
    {ρ : Representation ℂ (B.Levi F.Carrier) V}
    {τ : Representation ℂ (B.Levi F.Carrier) W}
    (f : ρ.IntertwiningMap τ) :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    ∀ z : Representation.Coinvariants
      (parabolicOrbitNestedCoefficient F.Carrier B C w (T.leviHalfModulus B) ρ),
    T.parabolicOrbitNestedRefinedCoefficientActionEquiv B C w S R hS hR τ
        (Representation.Coinvariants.map _ _
          (parabolicOrbitNestedCoefficientMap F.Carrier B C w (T.leviHalfModulus B) f) z) =
      T.normalizedRefinedJacquetMap B S f
        (T.parabolicOrbitNestedRefinedCoefficientActionEquiv B C w S R hS hR ρ z) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  exact T.parabolicOrbitNestedRefinedCoefficientEquiv_natural B C w S hS f

end Langlands.PadicField.TopologicalData
