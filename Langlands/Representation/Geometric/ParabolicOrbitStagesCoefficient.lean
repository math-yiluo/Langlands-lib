import Langlands.Representation.Induction.SplitStagesRetraction
import Langlands.Representation.Geometric.ParabolicOrbitCoefficientComparison

/-! Actual nested coefficient quotients for the parabolic orbit stages. -/

noncomputable section

namespace Langlands.Geometric

open GeneralLinear Induction

universe uF uV uW

variable (F : Type uF) [CommRing F] {n : ℕ}
  (B C : BlockShape n) (w : Equiv.Perm (Fin n))

/-- The restricted target Levi projection on the actual stages subgroup. -/
abbrev parabolicOrbitStagesRetraction :=
  splitStagesRetraction (C.leviProjection F) (C.leviInParabolic F)
    (C.leviProjection_section F) (parabolicOrbitStages F B C w)
    (parabolicOrbitStages_kernel_le F B C w)

/-- The actual quotient subgroup of the intermediate stages. -/
abbrev parabolicOrbitStagesQuotient : Subgroup (C.Levi F) :=
  (parabolicOrbitStages F B C w).comap (C.leviInParabolic F)

/-- The stabilizer with the intermediate subgroup retained. -/
abbrev parabolicOrbitNestedStabilizer : Subgroup (parabolicOrbitStages F B C w) :=
  (parabolicOrbitStabilizer F B C w).subgroupOf (parabolicOrbitStages F B C w)

/-- The inclusion with the intermediate stages removed. -/
abbrev parabolicOrbitNestedInclusion :
    parabolicOrbitNestedStabilizer F B C w →* parabolicOrbitStabilizer F B C w :=
  (Subgroup.subgroupOfEquivOfLe (parabolicOrbitStabilizer_le_stages F B C w)).toMonoidHom

/-- The actual radical intersection used by the inner quotient integral. -/
abbrev parabolicOrbitNestedIntersection :
    Subgroup (parabolicOrbitStagesRetraction F B C w).ker :=
  (parabolicOrbitNestedStabilizer F B C w).comap
    (parabolicOrbitStagesRetraction F B C w).ker.subtype

/-- The restricted radical-intersection inclusion into the nested stabilizer. -/
abbrev parabolicOrbitNestedIntersectionInclusion :
    parabolicOrbitNestedIntersection F B C w →* parabolicOrbitNestedStabilizer F B C w :=
  (parabolicOrbitStagesRetraction F B C w).ker.subtype.subgroupComap
    (parabolicOrbitNestedStabilizer F B C w)

variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]

/-- The original inducing coefficient restricted to the actual nested intersection. -/
abbrev parabolicOrbitNestedCoefficient (χ : B.Levi F →* ℂˣ)
    (ρ : Representation ℂ (B.Levi F) V) :
    Representation ℂ (parabolicOrbitNestedIntersection F B C w) V :=
  ((parabolicOrbitCoefficient F B C w χ ρ).comp
    (parabolicOrbitNestedInclusion F B C w)).comp
      (parabolicOrbitNestedIntersectionInclusion F B C w)

/-- Removing the intermediate stages identifies the actual nested quotient. -/
def parabolicOrbitNestedCoefficientEquiv (χ : B.Levi F →* ℂˣ)
    (ρ : Representation ℂ (B.Levi F) V)
    (hχ : sourceUnipotent F B C w ≤ χ.ker) :
    Representation.Coinvariants (parabolicOrbitNestedCoefficient F B C w χ ρ) ≃ₗ[ℂ]
      Jacquet.Coinvariants ρ (sourceUnipotent F B C w) :=
  (splitStagesCoefficientEquiv (C.leviProjection F) (C.leviInParabolic F)
    (C.leviProjection_section F) (parabolicOrbitStages F B C w)
    (parabolicOrbitStabilizer F B C w) (parabolicOrbitStages_kernel_le F B C w)
    (parabolicOrbitStabilizer_le_stages F B C w)
    (parabolicOrbitCoefficient F B C w χ ρ)).trans
      (parabolicOrbitCoefficientEquiv F B C w χ ρ hχ)

@[simp] theorem parabolicOrbitNestedCoefficientEquiv_mk (χ : B.Levi F →* ℂˣ)
    (ρ : Representation ℂ (B.Levi F) V)
    (hχ : sourceUnipotent F B C w ≤ χ.ker) (v : V) :
    parabolicOrbitNestedCoefficientEquiv F B C w χ ρ hχ
        (Representation.Coinvariants.mk (parabolicOrbitNestedCoefficient F B C w χ ρ) v) =
      Jacquet.mk ρ (sourceUnipotent F B C w) v :=
  parabolicOrbitCoefficientEquiv_mk F B C w χ ρ hχ v

@[simp] theorem parabolicOrbitNestedCoefficientEquiv_symm_mk (χ : B.Levi F →* ℂˣ)
    (ρ : Representation ℂ (B.Levi F) V)
    (hχ : sourceUnipotent F B C w ≤ χ.ker) (v : V) :
    (parabolicOrbitNestedCoefficientEquiv F B C w χ ρ hχ).symm
        (Jacquet.mk ρ (sourceUnipotent F B C w) v) =
      Representation.Coinvariants.mk (parabolicOrbitNestedCoefficient F B C w χ ρ) v := by
  apply (parabolicOrbitNestedCoefficientEquiv F B C w χ ρ hχ).injective
  rw [LinearEquiv.apply_symm_apply, parabolicOrbitNestedCoefficientEquiv_mk]

/-- The nested intersection restriction of an arbitrary coefficient intertwiner. -/
def parabolicOrbitNestedCoefficientMap (χ : B.Levi F →* ℂˣ)
    {ρ : Representation ℂ (B.Levi F) V} {τ : Representation ℂ (B.Levi F) W}
    (f : ρ.IntertwiningMap τ) :
    (parabolicOrbitNestedCoefficient F B C w χ ρ).IntertwiningMap
      (parabolicOrbitNestedCoefficient F B C w χ τ) :=
  splitStagesIntersectionMap (C.leviProjection F) (C.leviInParabolic F)
    (C.leviProjection_section F) (parabolicOrbitStages F B C w)
    (parabolicOrbitStabilizer F B C w) (parabolicOrbitStages_kernel_le F B C w)
    (parabolicOrbitStabilizer_le_stages F B C w)
    (parabolicOrbitCoefficientMap F B C w χ f)

/-- The nested coefficient identification is natural in all coefficient intertwiners. -/
theorem parabolicOrbitNestedCoefficientEquiv_natural (χ : B.Levi F →* ℂˣ)
    {ρ : Representation ℂ (B.Levi F) V} {τ : Representation ℂ (B.Levi F) W}
    (hχ : sourceUnipotent F B C w ≤ χ.ker) (f : ρ.IntertwiningMap τ)
    (z : Representation.Coinvariants (parabolicOrbitNestedCoefficient F B C w χ ρ)) :
    parabolicOrbitNestedCoefficientEquiv F B C w χ τ hχ
        (Representation.Coinvariants.map _ _ (parabolicOrbitNestedCoefficientMap F B C w χ f) z) =
      Representation.Coinvariants.map _ _ (Jacquet.restrictMap f (sourceUnipotent F B C w))
        (parabolicOrbitNestedCoefficientEquiv F B C w χ ρ hχ z) := by
  induction z using Representation.Coinvariants.induction_on with
  | h v =>
    change parabolicOrbitNestedCoefficientEquiv F B C w χ τ hχ
      (Representation.Coinvariants.mk _ (f v)) = _
    rw [parabolicOrbitNestedCoefficientEquiv_mk, parabolicOrbitNestedCoefficientEquiv_mk]
    rfl

/-- The actual target section with values in the inducing stabilizer. -/
abbrev parabolicOrbitStagesSection :
    parabolicOrbitStagesQuotient F B C w →* parabolicOrbitStabilizer F B C w :=
  splitStagesInducingSection (C.leviInParabolic F) (parabolicOrbitStages F B C w)
    (parabolicOrbitStabilizer F B C w) (parabolicOrbitStages_section_mem F B C w)

/-- The full intermediate section formula retains the original source character. -/
theorem parabolicOrbitNestedCoefficientEquiv_section_mk (χ : B.Levi F →* ℂˣ)
    (ρ : Representation ℂ (B.Levi F) V)
    (hχ : sourceUnipotent F B C w ≤ χ.ker)
    (l : parabolicOrbitStagesQuotient F B C w) (v : V) :
    parabolicOrbitNestedCoefficientEquiv F B C w χ ρ hχ
        (Representation.Coinvariants.mk (parabolicOrbitNestedCoefficient F B C w χ ρ)
          (parabolicOrbitCoefficient F B C w χ ρ (parabolicOrbitStagesSection F B C w l) v)) =
      (χ (parabolicOrbitToSourceLevi F B C w (parabolicOrbitStagesSection F B C w l)) : ℂ) •
        Jacquet.mk ρ (sourceUnipotent F B C w)
          (ρ (parabolicOrbitToSourceLevi F B C w (parabolicOrbitStagesSection F B C w l)) v) := by
  rw [parabolicOrbitNestedCoefficientEquiv_mk]
  exact map_smul (Jacquet.mk ρ (sourceUnipotent F B C w)) _ _

end Langlands.Geometric

namespace Langlands.PadicField.TopologicalData

open GeneralLinear Geometric Induction

universe uF uV uW

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
  (T : F.TopologicalData) {n : ℕ} (B C : BlockShape n)
  (w : Equiv.Perm (Fin n)) (S : BlockRefinement B)
  (hS : IsIntersectionRefinement (F := F.Carrier) B C w S)
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]

/-- The actual nested positive-half coefficient quotient is the refined Jacquet carrier. -/
def parabolicOrbitNestedRefinedCoefficientEquiv
    (ρ : Representation ℂ (B.Levi F.Carrier) V) :
    Representation.Coinvariants
        (parabolicOrbitNestedCoefficient F.Carrier B C w (T.leviHalfModulus B) ρ) ≃ₗ[ℂ]
      RefinedJacquetModule B S ρ :=
  (splitStagesCoefficientEquiv (C.leviProjection F.Carrier) (C.leviInParabolic F.Carrier)
    (C.leviProjection_section F.Carrier) (parabolicOrbitStages F.Carrier B C w)
    (parabolicOrbitStabilizer F.Carrier B C w) (parabolicOrbitStages_kernel_le F.Carrier B C w)
    (parabolicOrbitStabilizer_le_stages F.Carrier B C w)
    (parabolicOrbitCoefficient F.Carrier B C w (T.leviHalfModulus B) ρ)).trans
      (T.parabolicOrbitRefinedCoefficientEquiv B C w S hS ρ)

@[simp] theorem parabolicOrbitNestedRefinedCoefficientEquiv_mk
    (ρ : Representation ℂ (B.Levi F.Carrier) V) (v : V) :
    T.parabolicOrbitNestedRefinedCoefficientEquiv B C w S hS ρ
        (Representation.Coinvariants.mk
          (parabolicOrbitNestedCoefficient F.Carrier B C w (T.leviHalfModulus B) ρ) v) =
      refinedJacquetMk B S ρ v :=
  T.parabolicOrbitRefinedCoefficientEquiv_mk B C w S hS ρ v

@[simp] theorem parabolicOrbitNestedRefinedCoefficientEquiv_symm_mk
    (ρ : Representation ℂ (B.Levi F.Carrier) V) (v : V) :
    (T.parabolicOrbitNestedRefinedCoefficientEquiv B C w S hS ρ).symm
        (refinedJacquetMk B S ρ v) =
      Representation.Coinvariants.mk
        (parabolicOrbitNestedCoefficient F.Carrier B C w (T.leviHalfModulus B) ρ) v := by
  apply (T.parabolicOrbitNestedRefinedCoefficientEquiv B C w S hS ρ).injective
  rw [LinearEquiv.apply_symm_apply, parabolicOrbitNestedRefinedCoefficientEquiv_mk]

/-- The nested refined quotient comparison commutes with every normalized Jacquet map. -/
theorem parabolicOrbitNestedRefinedCoefficientEquiv_natural
    {ρ : Representation ℂ (B.Levi F.Carrier) V}
    {τ : Representation ℂ (B.Levi F.Carrier) W}
    (f : ρ.IntertwiningMap τ)
    (z : Representation.Coinvariants
      (parabolicOrbitNestedCoefficient F.Carrier B C w (T.leviHalfModulus B) ρ)) :
    T.parabolicOrbitNestedRefinedCoefficientEquiv B C w S hS τ
        (Representation.Coinvariants.map _ _
          (parabolicOrbitNestedCoefficientMap F.Carrier B C w (T.leviHalfModulus B) f) z) =
      T.normalizedRefinedJacquetMap B S f
        (T.parabolicOrbitNestedRefinedCoefficientEquiv B C w S hS ρ z) := by
  induction z using Representation.Coinvariants.induction_on with
  | h v =>
    change T.parabolicOrbitNestedRefinedCoefficientEquiv B C w S hS τ
      (Representation.Coinvariants.mk _ (f v)) = _
    rw [parabolicOrbitNestedRefinedCoefficientEquiv_mk,
      parabolicOrbitNestedRefinedCoefficientEquiv_mk]
    rfl

/-- The full intermediate section retains the positive source half and its actual action. -/
theorem parabolicOrbitNestedRefinedCoefficientEquiv_section_mk
    (ρ : Representation ℂ (B.Levi F.Carrier) V)
    (l : parabolicOrbitStagesQuotient F.Carrier B C w) (v : V) :
    T.parabolicOrbitNestedRefinedCoefficientEquiv B C w S hS ρ
        (Representation.Coinvariants.mk
          (parabolicOrbitNestedCoefficient F.Carrier B C w (T.leviHalfModulus B) ρ)
          (parabolicOrbitCoefficient F.Carrier B C w (T.leviHalfModulus B) ρ
            (parabolicOrbitStagesSection F.Carrier B C w l) v)) =
      (T.leviHalfModulus B (parabolicOrbitToSourceLevi F.Carrier B C w
        (parabolicOrbitStagesSection F.Carrier B C w l)) : ℂ) •
        refinedJacquetMk B S ρ
          (ρ (parabolicOrbitToSourceLevi F.Carrier B C w
            (parabolicOrbitStagesSection F.Carrier B C w l)) v) := by
  rw [parabolicOrbitNestedRefinedCoefficientEquiv_mk]
  exact map_smul (refinedJacquetMk B S ρ) _ _

end Langlands.PadicField.TopologicalData
