import Langlands.LocalFactor.DeligneHenniartWitnessAlgebra

/-! # Signed composition and cosets of Deligne--Henniart witnesses -/

noncomputable section

universe uF uV uA

namespace Langlands.LocalFactor.NonabelianSystem.DeligneHenniart

open CommonClosure VirtualRepresentation Weil.Local
open LocalWeil.Ramification

/-- Elements annihilated by some power of `p`. The exponent is local to the
element; addition uses a common exponent without asserting uniformity. -/
def pPowerTorsion (p : ℕ) (A : Type uA) [AddCommGroup A] : AddSubgroup A where
  carrier := {x | ∃ n : ℕ, (p ^ n) • x = 0}
  zero_mem' := ⟨0, by simp⟩
  add_mem' := by
    rintro x y ⟨m, hm⟩ ⟨n, hn⟩
    refine ⟨m + n, ?_⟩
    have hx : (p ^ (m + n)) • x = 0 := by
      rw [pow_add, mul_nsmul, hm, nsmul_zero]
    have hy : (p ^ (m + n)) • y = 0 := by
      rw [Nat.add_comm m n, pow_add, mul_nsmul, hn, nsmul_zero]
    rw [nsmul_add, hx, hy, add_zero]
  neg_mem' := by
    rintro x ⟨n, hn⟩
    exact ⟨n, by rw [smul_neg, hn, neg_zero]⟩

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

/-- The logarithmic notation here is only the additive type tag on complex
units. This is the actual epsilon/determinant ratio, with no logarithm chosen. -/
def witnessRatio (e : ReciprocityFamily F) (ε : Assignment.{uF, uV} F)
    (hε : AdditiveRelation F ε)
    (ψ : AdditiveCharacter F (baseExtension F)) (μ : HaarMeasure F (baseExtension F))
    (w : LocalWeil.Lattice.{uF, max uF uV} F) :
    (LocalWeil.Lattice.{uF, max uF uV} F ×
      Additive (baseExtension F).fieldˣ) →+ Additive ℂˣ := by
  letI := (fieldData F (baseExtension F)).topology
  exact (tensorValueAddHom F ε hε ψ μ w).comp (AddMonoidHom.fst _ _) -
    ((fieldDeterminant F e _ (realizeAtBase F w)).toMonoidHom.toAdditive).comp
      (AddMonoidHom.snd _ _)

theorem witnessRatio_eq_zero_iff (e : ReciprocityFamily F)
    (ε : Assignment.{uF, uV} F) (hε : AdditiveRelation F ε)
    (ψ : AdditiveCharacter F (baseExtension F)) (μ : HaarMeasure F (baseExtension F))
    (w v : LocalWeil.Lattice.{uF, max uF uV} F) (γ : (baseExtension F).fieldˣ) :
    witnessRatio F e ε hε ψ μ w (v, Additive.ofMul γ) = 0 ↔
      ε _ ψ μ (ExactGrothendieckGroup.continuousTensorSame
        (realizeAtBase F w) (realizeAtBase F v)) =
        fieldDeterminant F e _ (realizeAtBase F w) γ := by
  dsimp only [witnessRatio, AddMonoidHom.sub_apply, AddMonoidHom.comp_apply]
  rw [sub_eq_zero]
  rfl

theorem witnessRatio_mem_pPowerTorsion_iff (e : ReciprocityFamily F)
    (ε : Assignment.{uF, uV} F) (hε : AdditiveRelation F ε)
    (ψ : AdditiveCharacter F (baseExtension F)) (μ : HaarMeasure F (baseExtension F))
    (w v : LocalWeil.Lattice.{uF, max uF uV} F) (γ : (baseExtension F).fieldˣ) :
    witnessRatio F e ε hε ψ μ w (v, Additive.ofMul γ) ∈
      pPowerTorsion p (Additive ℂˣ) ↔
      ∃ n : ℕ,
        ε _ ψ μ (ExactGrothendieckGroup.continuousTensorSame
          (realizeAtBase F w) (realizeAtBase F v)) ^ (p ^ n) =
          fieldDeterminant F e _ (realizeAtBase F w) γ ^ (p ^ n) := by
  change (∃ n : ℕ, (p ^ n) •
    witnessRatio F e ε hε ψ μ w (v, Additive.ofMul γ) = 0) ↔ _
  dsimp only [witnessRatio, AddMonoidHom.sub_apply, AddMonoidHom.comp_apply]
  simp only [nsmul_sub, sub_eq_zero]
  rfl

/-- The exact witness pairs form a subgroup for a fixed bound. The first
coordinate adds signed lattices and the second multiplies field units. -/
def exactWitnessGroup (e : ReciprocityFamily F) (ε : Assignment.{uF, uV} F)
    (hε : AdditiveRelation F ε) (a : ℝ)
    (ψ : AdditiveCharacter F (baseExtension F)) :
    AddSubgroup (LocalWeil.Lattice.{uF, max uF uV} F ×
      Additive (baseExtension F).fieldˣ) where
  carrier := {x | ∀ w : LocalWeil.Lattice.{uF, max uF uV} F,
    LocalWeil.degree F w = 0 → AllBreaksBelow F w (a / 2) →
    ∀ μ : HaarMeasure F (baseExtension F), witnessRatio F e ε hε ψ μ w x = 0}
  zero_mem' := by
    intro w hw ha μ
    exact map_zero _
  add_mem' := by
    intro x y hx hy w hw ha μ
    rw [map_add, hx w hw ha μ, hy w hw ha μ, add_zero]
  neg_mem' := by
    intro x hx w hw ha μ
    rw [map_neg, hx w hw ha μ, neg_zero]

/-- Approximate witness pairs form a subgroup with a separate p-power
exponent for each test and Haar measure. -/
def approximateWitnessGroup (e : ReciprocityFamily F) (ε : Assignment.{uF, uV} F)
    (hε : AdditiveRelation F ε) (a : ℝ)
    (ψ : AdditiveCharacter F (baseExtension F)) :
    AddSubgroup (LocalWeil.Lattice.{uF, max uF uV} F ×
      Additive (baseExtension F).fieldˣ) where
  carrier := {x | ∀ w : LocalWeil.Lattice.{uF, max uF uV} F,
    LocalWeil.degree F w = 0 → AllBreaksBelow F w a →
    ∀ μ : HaarMeasure F (baseExtension F),
      witnessRatio F e ε hε ψ μ w x ∈ pPowerTorsion p (Additive ℂˣ)}
  zero_mem' := by
    intro w hw ha μ
    rw [map_zero]
    exact AddSubgroup.zero_mem _
  add_mem' := by
    intro x y hx hy w hw ha μ
    rw [map_add]
    exact AddSubgroup.add_mem _ (hx w hw ha μ) (hy w hw ha μ)
  neg_mem' := by
    intro x hx w hw ha μ
    rw [map_neg]
    exact AddSubgroup.neg_mem _ (hx w hw ha μ)

theorem mem_exactWitnessGroup_iff (e : ReciprocityFamily F)
    (ε : Assignment.{uF, uV} F) (hε : AdditiveRelation F ε)
    (v : LocalWeil.Lattice.{uF, max uF uV} F) (a : ℝ)
    (ψ : AdditiveCharacter F (baseExtension F)) (γ : (baseExtension F).fieldˣ) :
    (v, Additive.ofMul γ) ∈ exactWitnessGroup F e ε hε a ψ ↔
      ExactWitness F e ε v a ψ γ := by
  rw [exactWitness_iff]
  change (∀ w, LocalWeil.degree F w = 0 → AllBreaksBelow F w (a / 2) →
    ∀ μ, witnessRatio F e ε hε ψ μ w (v, Additive.ofMul γ) = 0) ↔ _
  simp only [witnessRatio_eq_zero_iff]

theorem mem_approximateWitnessGroup_iff (e : ReciprocityFamily F)
    (ε : Assignment.{uF, uV} F) (hε : AdditiveRelation F ε)
    (v : LocalWeil.Lattice.{uF, max uF uV} F) (a : ℝ)
    (ψ : AdditiveCharacter F (baseExtension F)) (γ : (baseExtension F).fieldˣ) :
    (v, Additive.ofMul γ) ∈ approximateWitnessGroup F e ε hε a ψ ↔
      ApproximateWitness F e ε v a ψ γ := by
  rw [approximateWitness_iff]
  change (∀ w, LocalWeil.degree F w = 0 → AllBreaksBelow F w a →
    ∀ μ, witnessRatio F e ε hε ψ μ w (v, Additive.ofMul γ) ∈
      pPowerTorsion p (Additive ℂˣ)) ↔ _
  simp only [witnessRatio_mem_pPowerTorsion_iff]

variable {F} {e : ReciprocityFamily F} {ε : Assignment.{uF, uV} F}
  (hε : AdditiveRelation F ε) {a : ℝ}
  {ψ : AdditiveCharacter F (baseExtension F)}
  {v v' : LocalWeil.Lattice.{uF, max uF uV} F}
  {γ γ' : (baseExtension F).fieldˣ}

include hε

theorem exactWitness_add (h : ExactWitness F e ε v a ψ γ)
    (h' : ExactWitness F e ε v' a ψ γ') :
    ExactWitness F e ε (v + v') a ψ (γ * γ') := by
  apply (mem_exactWitnessGroup_iff F e ε hε _ a ψ _).mp
  have hsum := (exactWitnessGroup F e ε hε a ψ).add_mem
    ((mem_exactWitnessGroup_iff F e ε hε v a ψ γ).mpr h)
    ((mem_exactWitnessGroup_iff F e ε hε v' a ψ γ').mpr h')
  exact hsum

theorem exactWitness_neg (h : ExactWitness F e ε v a ψ γ) :
    ExactWitness F e ε (-v) a ψ γ⁻¹ := by
  apply (mem_exactWitnessGroup_iff F e ε hε _ a ψ _).mp
  have hneg := (exactWitnessGroup F e ε hε a ψ).neg_mem
    ((mem_exactWitnessGroup_iff F e ε hε v a ψ γ).mpr h)
  exact hneg

theorem exactWitness_zsmul (n : ℤ) (h : ExactWitness F e ε v a ψ γ) :
    ExactWitness F e ε (n • v) a ψ (γ ^ n) := by
  apply (mem_exactWitnessGroup_iff F e ε hε _ a ψ _).mp
  exact (exactWitnessGroup F e ε hε a ψ).zsmul_mem
    ((mem_exactWitnessGroup_iff F e ε hε v a ψ γ).mpr h) n

theorem approximateWitness_add (h : ApproximateWitness F e ε v a ψ γ)
    (h' : ApproximateWitness F e ε v' a ψ γ') :
    ApproximateWitness F e ε (v + v') a ψ (γ * γ') := by
  apply (mem_approximateWitnessGroup_iff F e ε hε _ a ψ _).mp
  have hsum := (approximateWitnessGroup F e ε hε a ψ).add_mem
    ((mem_approximateWitnessGroup_iff F e ε hε v a ψ γ).mpr h)
    ((mem_approximateWitnessGroup_iff F e ε hε v' a ψ γ').mpr h')
  exact hsum

theorem approximateWitness_neg (h : ApproximateWitness F e ε v a ψ γ) :
    ApproximateWitness F e ε (-v) a ψ γ⁻¹ := by
  apply (mem_approximateWitnessGroup_iff F e ε hε _ a ψ _).mp
  have hneg := (approximateWitnessGroup F e ε hε a ψ).neg_mem
    ((mem_approximateWitnessGroup_iff F e ε hε v a ψ γ).mpr h)
  exact hneg

theorem approximateWitness_zsmul (n : ℤ)
    (h : ApproximateWitness F e ε v a ψ γ) :
    ApproximateWitness F e ε (n • v) a ψ (γ ^ n) := by
  apply (mem_approximateWitnessGroup_iff F e ε hε _ a ψ _).mp
  exact (approximateWitnessGroup F e ε hε a ψ).zsmul_mem
    ((mem_approximateWitnessGroup_iff F e ε hε v a ψ γ).mpr h) n

/-- Purely algebraic coset description. Identifying the zero-input
annihilator with a principal-unit group is a separate arithmetic assertion. -/
theorem exactWitness_coset (h : ExactWitness F e ε v a ψ γ) :
    ExactWitness F e ε v a ψ γ' ↔
      ExactWitness F e ε 0 a ψ (γ' * γ⁻¹) := by
  constructor
  · intro h'
    simpa using exactWitness_add hε h' (exactWitness_neg hε h)
  · intro h'
    simpa [mul_assoc] using exactWitness_add hε h' h

theorem approximateWitness_coset (h : ApproximateWitness F e ε v a ψ γ) :
    ApproximateWitness F e ε v a ψ γ' ↔
      ApproximateWitness F e ε 0 a ψ (γ' * γ⁻¹) := by
  constructor
  · intro h'
    simpa using approximateWitness_add hε h' (approximateWitness_neg hε h)
  · intro h'
    simpa [mul_assoc] using approximateWitness_add hε h' h

end Langlands.LocalFactor.NonabelianSystem.DeligneHenniart
