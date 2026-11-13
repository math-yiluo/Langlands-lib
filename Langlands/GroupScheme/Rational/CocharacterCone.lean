import Langlands.GroupScheme.Rational.RootAnnihilatorBaseChange
import Langlands.Geometry.Building.CocharacterUniformizerEvaluation
import Mathlib.LinearAlgebra.Quotient.Basic

/-! # Nonnegative cocharacters and their integral annihilator quotient -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme.CocharacterCone

variable {k : Type u} [Field k]
  (T : CommGroupScheme (Spec (CommRingCat.of k)))
  (R : Set (characterLattice T))

/-- Integral cocharacters nonnegative on the selected actual characters. -/
def nonnegative : AddSubmonoid (cocharacterLattice T) where
  carrier := {ν | ∀ α ∈ R, 0 ≤ latticePairing T α ν}
  zero_mem' := by simp
  add_mem' := by
    intro ν μ hν hμ α hα
    simpa only [map_add] using add_nonneg (hν α hα) (hμ α hα)

@[simp] theorem mem_nonnegative (ν : cocharacterLattice T) :
    ν ∈ nonnegative T R ↔ ∀ α ∈ R, 0 ≤ latticePairing T α ν :=
  Iff.rfl

/-- The existing common integral annihilator consists of invertible directions
of the nonnegative monoid. -/
theorem mem_annihilator_iff (ν : cocharacterLattice T) :
    ν ∈ RealTorusSpace.rootAnnihilatorInt T R ↔
      ν ∈ nonnegative T R ∧ -ν ∈ nonnegative T R := by
  rw [RealTorusSpace.mem_rootAnnihilatorInt]
  constructor
  · intro h
    constructor <;> intro α hα <;> simp [h α hα]
  · rintro ⟨hν, hneg⟩ α hα
    have hle : latticePairing T α ν ≤ 0 := by
      simpa only [map_neg, neg_nonneg] using hneg α hα
    exact le_antisymm hle (hν α hα)

/-- Translating by an integral annihilator direction preserves the monoid. -/
theorem add_mem_nonnegative_iff (ν μ : cocharacterLattice T)
    (hμ : μ ∈ RealTorusSpace.rootAnnihilatorInt T R) :
    ν + μ ∈ nonnegative T R ↔ ν ∈ nonnegative T R := by
  have h := (RealTorusSpace.mem_rootAnnihilatorInt R μ).mp hμ
  constructor <;> intro hν α hα <;>
    simpa only [map_add, h α hα, add_zero] using hν α hα

/-- The image of the nonnegative monoid in the quotient of the actual integral
cocharacter lattice by its existing common annihilator. -/
def quotient : AddSubmonoid
    (cocharacterLattice T ⧸ RealTorusSpace.rootAnnihilatorInt T R) :=
  (nonnegative T R).map
    (RealTorusSpace.rootAnnihilatorInt T R).mkQ.toAddMonoidHom

/-- A quotient class belongs to the image precisely when any representative
is nonnegative on the selected characters. -/
@[simp] theorem mkQ_mem_quotient_iff (ν : cocharacterLattice T) :
    (RealTorusSpace.rootAnnihilatorInt T R).mkQ ν ∈ quotient T R ↔
      ν ∈ nonnegative T R := by
  constructor
  · rintro ⟨μ, hμ, heq⟩
    have hdiff : μ - ν ∈ RealTorusSpace.rootAnnihilatorInt T R :=
      (Submodule.Quotient.eq _).mp heq
    have hpair := (RealTorusSpace.mem_rootAnnihilatorInt R (μ - ν)).mp hdiff
    intro α hα
    have he : latticePairing T α μ = latticePairing T α ν :=
      sub_eq_zero.mp (by simpa only [map_sub] using hpair α hα)
    exact he ▸ hμ α hα
  · intro hν
    exact ⟨ν, hν, rfl⟩

section LocalField

variable [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

/-- The common-uniformizer section identifies the nonnegative cocharacters
with the existing lattice cut `C_A^+`. -/
theorem latticeSection_mem_CAplus_iff (ν : cocharacterLattice T) :
    CocharacterUniformizer.latticeSection k T (Multiplicative.ofAdd ν) ∈
        CocharacterUniformizer.CAplus k T R ↔ ν ∈ nonnegative T R := by
  constructor
  · intro h α hα
    have hnorm := h.2 α hα
    rw [CocharacterUniformizer.characterNorm_latticeSection] at hnorm
    have hq : (1 : ℝ) < LocalField.residueCardinality k := by
      exact_mod_cast LocalField.residueCardinality_gt_one k
    exact neg_nonpos.mp ((zpow_le_one_iff_right₀ hq).mp hnorm)
  · intro hν
    refine ⟨⟨Multiplicative.ofAdd ν, rfl⟩, fun α hα => ?_⟩
    rw [CocharacterUniformizer.characterNorm_latticeSection]
    have hq : (1 : ℝ) < LocalField.residueCardinality k := by
      exact_mod_cast LocalField.residueCardinality_gt_one k
    exact (zpow_le_one_iff_right₀ hq).mpr (neg_nonpos.mpr (hν α hα))

end LocalField

end Langlands.GroupScheme.CocharacterCone
