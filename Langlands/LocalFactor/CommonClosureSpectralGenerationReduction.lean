import Langlands.LocalFactor.CommonClosureSpectralAnalyticStatement
import Langlands.LocalFactor.NonabelianUniquenessStatement
import Langlands.VirtualRepresentation.ExactInductionTwist
import Mathlib.Analysis.Analytic.Constructions

/-!
# Reduction of common-closure spectral analyticity to rank one

Spectral twisting commutes with actual common-closure induction. Degree-zero
generation and the induction law then extend analyticity from the rank-one
classes to every exact virtual class.
-/

noncomputable section

universe uF uV

namespace Langlands.LocalFactor.CommonClosureSpectralAnalytic

open CommonClosure CommonClosureSpectral VirtualRepresentation NonabelianSystem

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

section Induction

variable (E L : Extension F) (h : E.field ≤ L.field)

/-- The two spectral characters agree on the nested subgroup: both use the
base-field degree of the same Weil group element. -/
theorem character_nestedWeilEquiv (s : ℂ) :
    (character F L s).comp (nestedWeilEquiv F E L h : _ →ₜ* _) =
      (character F E s).comp
        ⟨((weilSubgroup F L).subgroupOf (weilSubgroup F E)).subtype,
          continuous_subtype_val⟩ := by
  ext w
  rfl

/-- Actual common-closure induction commutes with the spectral twist. -/
theorem virtualTwist_induce (s : ℂ) (x : Virtual.{uF, uV} F L) :
    virtualTwist F E s (induce F E L h x) = induce F E L h (virtualTwist F L s x) := by
  change ExactGrothendieckGroup.continuousTwist (character F E s)
      (ExactGrothendieckGroup.continuousInduce _ (nestedWeil_open F E L)
        (ExactGrothendieckGroup.continuousRestrict
          (nestedWeilEquiv F E L h : _ →ₜ* _) x)) =
    ExactGrothendieckGroup.continuousInduce _ (nestedWeil_open F E L)
      (ExactGrothendieckGroup.continuousRestrict
        (nestedWeilEquiv F E L h : _ →ₜ* _)
        (ExactGrothendieckGroup.continuousTwist (character F L s) x))
  rw [ExactGrothendieckGroup.continuousRestrict_continuousTwist,
    character_nestedWeilEquiv,
    ExactGrothendieckGroup.continuousInduce_continuousTwist]

end Induction

section Generation

variable {F}

theorem haarMeasure_nonempty (E : Extension F) :
    Nonempty (HaarMeasure F E) := by
  let := (fieldData F E).topology
  let := (fieldData F E).valuativeRel
  let := (fieldData F E).localField
  let : MeasurableSpace E.field := borel E.field
  let : BorelSpace E.field := ⟨rfl⟩
  let := (fieldData F E).fieldT2
  obtain ⟨K⟩ : Nonempty (TopologicalSpace.PositiveCompacts E.field) := inferInstance
  exact ⟨HarmonicAnalysis.normalizedAdditiveHaar E.field K⟩

/-- Analyticity of every spectral value on the continuous characters of every
intermediate field. -/
def RankOneAnalytic (ε : Assignment.{uF, uV} F) : Prop :=
  ∀ (L : Extension F) (ψ : AdditiveCharacter F L) (μ : HaarMeasure F L)
    (χ : weilSubgroup F L →ₜ* ℂˣ) (s : ℂ),
    AnalyticAt ℂ (fun z : ℂ =>
      (ε L ψ μ (virtualTwist F L z (ExactGrothendieckGroup.characterClass χ)) : ℂ)) s

variable {e : ReciprocityFamily F} {ε : Assignment.{uF, uV} F}

/-- The exact virtual classes whose spectral value is analytic everywhere. -/
def analyticSubgroup (hε : IsSystem F e ε) (E : Extension F)
    (ψ : AdditiveCharacter F E) (μ : HaarMeasure F E) :
    AddSubgroup (Virtual.{uF, uV} F E) where
  carrier := {x | ∀ s : ℂ, AnalyticAt ℂ (fun z : ℂ =>
    (conditionalDeligneValue F e ε hε E ψ μ x z : ℂ)) s}
  zero_mem' := by
    intro s
    simp only [conditionalDeligneValue, map_zero, value_zero hε.2.1]
    exact analyticAt_const
  add_mem' := by
    intro x y hx hy s
    have hfun : (fun z : ℂ => (conditionalDeligneValue F e ε hε E ψ μ (x + y) z : ℂ)) =
        fun z : ℂ => (conditionalDeligneValue F e ε hε E ψ μ x z : ℂ) *
          (conditionalDeligneValue F e ε hε E ψ μ y z : ℂ) := by
      funext z
      simp only [conditionalDeligneValue, map_add, hε.2.1 E ψ μ, Units.val_mul]
    rw [hfun]
    exact AnalyticAt.mul (hx s) (hy s)
  neg_mem' := by
    intro x hx s
    have hfun : (fun z : ℂ => (conditionalDeligneValue F e ε hε E ψ μ (-x) z : ℂ)) =
        fun z : ℂ => (conditionalDeligneValue F e ε hε E ψ μ x z : ℂ)⁻¹ := by
      funext z
      simp only [conditionalDeligneValue, map_neg, value_neg hε.2.1, Units.val_inv_eq_inv_val]
    rw [hfun]
    exact AnalyticAt.inv (hx s) (Units.ne_zero _)

theorem mem_analyticSubgroup {hε : IsSystem F e ε} {E : Extension F}
    {ψ : AdditiveCharacter F E} {μ : HaarMeasure F E} {x : Virtual.{uF, uV} F E} :
    x ∈ analyticSubgroup hε E ψ μ ↔ ∀ s : ℂ, AnalyticAt ℂ (fun z : ℂ =>
      (conditionalDeligneValue F e ε hε E ψ μ x z : ℂ)) s :=
  Iff.rfl

/-- Every displayed generator of the degree-zero group has analytic spectral
value: twisting passes through induction, the induction law moves the value to
the larger field, and there it is a quotient of two rank-one values. -/
theorem generators_subset_analyticSubgroup (hε : IsSystem F e ε)
    (hrank : RankOneAnalytic ε) (E : Extension F)
    (ψ : AdditiveCharacter F E) (μ : HaarMeasure F E) :
    characterDifferenceInductionGenerators.{uF, uV} F E ⊆
      (analyticSubgroup hε E ψ μ : Set (Virtual.{uF, uV} F E)) := by
  rintro y ⟨L, h, χ, χ', rfl⟩ s
  obtain ⟨μL⟩ := haarMeasure_nonempty L
  have hfun : (fun z : ℂ => (conditionalDeligneValue F e ε hε E ψ μ
        (induce F E L h (ExactGrothendieckGroup.characterClass χ -
          ExactGrothendieckGroup.characterClass χ')) z : ℂ)) =
      fun z : ℂ =>
        (ε L (traceCharacter F E L h ψ) μL
            (virtualTwist F L z (ExactGrothendieckGroup.characterClass χ)) : ℂ) *
          (ε L (traceCharacter F E L h ψ) μL
            (virtualTwist F L z (ExactGrothendieckGroup.characterClass χ')) : ℂ)⁻¹ := by
    funext z
    let w : DegreeZero.{uF, uV} F L :=
      ⟨virtualTwist F L z (ExactGrothendieckGroup.characterClass χ -
          ExactGrothendieckGroup.characterClass χ'), by
        change degree F L _ = 0
        rw [degree_virtualTwist, map_sub, ExactGrothendieckGroup.degree_characterClass,
          ExactGrothendieckGroup.degree_characterClass, sub_self]⟩
    change (ε E ψ μ (virtualTwist F E z (induce F E L h _)) : ℂ) = _
    rw [virtualTwist_induce]
    change (ε E ψ μ (induce F E L h w.val) : ℂ) = _
    rw [hε.2.2.2.1 E L h ψ μ μL w]
    change (ε L (traceCharacter F E L h ψ) μL
      (virtualTwist F L z (ExactGrothendieckGroup.characterClass χ -
        ExactGrothendieckGroup.characterClass χ')) : ℂ) = _
    rw [map_sub, sub_eq_add_neg, hε.2.1, value_neg hε.2.1, Units.val_mul,
      Units.val_inv_eq_inv_val]
  rw [hfun]
  exact AnalyticAt.mul (hrank L _ μL χ s) (AnalyticAt.inv (hrank L _ μL χ' s) (Units.ne_zero _))

/-- Degree-zero generation and rank-one analyticity give analyticity of every
spectral value over every intermediate field. -/
theorem analyticAt_of_generation (hgen : CommonClosureDegreeZeroGeneration.{uF, uV} F)
    (hε : IsSystem F e ε) (hrank : RankOneAnalytic ε)
    (E : Extension F) (ψ : AdditiveCharacter F E) (μ : HaarMeasure F E)
    (x : Virtual.{uF, uV} F E) (s : ℂ) :
    AnalyticAt ℂ (fun z : ℂ => (conditionalDeligneValue F e ε hε E ψ μ x z : ℂ)) s := by
  let S := analyticSubgroup hε E ψ μ
  have hzero : DegreeZero.{uF, uV} F E ≤ AddSubgroup.toIntSubmodule S := by
    rw [← hgen E]
    exact Submodule.span_le.mpr (generators_subset_analyticSubgroup hε hrank E ψ μ)
  let t : Virtual.{uF, uV} F E :=
    ExactGrothendieckGroup.characterClass (1 : weilSubgroup F E →ₜ* ℂˣ)
  have ht : t ∈ S := fun s => hrank E ψ μ 1 s
  have hy : x - degree F E x • t ∈ S := by
    apply hzero
    change degree F E (x - degree F E x • t) = 0
    simp [t]
  have hx : x ∈ S := by
    have := S.add_mem hy (S.zsmul_mem ht (degree F E x))
    rwa [sub_add_cancel] at this
  exact hx s

end Generation

end Langlands.LocalFactor.CommonClosureSpectralAnalytic
