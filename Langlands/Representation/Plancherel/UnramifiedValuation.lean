import Langlands.Representation.Plancherel.UnramifiedCharacters
import Mathlib.Algebra.Group.TypeTags.Hom
import Mathlib.GroupTheory.Abelianization.Defs
import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# Integer valuation of character evaluations

The intended inputs are the actual rational-character evaluation and the
normalized integer valuation on field units. This module constructs their
composite, its image, and the exact quotient without a lattice hypothesis.
-/

noncomputable section

open scoped NNReal

namespace Langlands.Plancherel

universe uG uL uK

variable {G : Type uG} [Group G] {L : Type uL} [AddCommGroup L]
variable {K : Type uK} [CommGroup K]

/-- Compose character evaluation with an integer valuation, additively in
the character index. The inputs may be actual rational-character evaluations. -/
def characterValuationPairing (ε : L →+ Additive (G →* K))
    (v : K →* Multiplicative ℤ) (g : G) : L →+ ℤ where
  toFun χ := (v ((ε χ).toMul g)).toAdd
  map_zero' := by
    rw [map_zero]
    change (v 1).toAdd = 0
    rw [map_one]
    rfl
  map_add' χ ψ := by
    rw [map_add]
    change (v ((ε χ).toMul g * (ε ψ).toMul g)).toAdd = _
    exact v.map_mul _ _

/-- The valuation homomorphism into the integer additive dual of the given
character group, with the target written multiplicatively. -/
def characterValuation (ε : L →+ Additive (G →* K))
    (v : K →* Multiplicative ℤ) : G →* Multiplicative (L →+ ℤ) where
  toFun g := Multiplicative.ofAdd (characterValuationPairing ε v g)
  map_one' := by
    apply AddMonoidHom.ext
    intro χ
    change (v ((ε χ).toMul 1)).toAdd = 0
    rw [map_one, map_one]
    rfl
  map_mul' g h := by
    apply AddMonoidHom.ext
    intro χ
    change (v ((ε χ).toMul (g * h))).toAdd =
      (v ((ε χ).toMul g)).toAdd + (v ((ε χ).toMul h)).toAdd
    rw [map_mul]
    exact v.map_mul _ _

@[simp]
theorem characterValuation_apply (ε : L →+ Additive (G →* K))
    (v : K →* Multiplicative ℤ) (g : G) (χ : L) :
    (characterValuation ε v g).toAdd χ = (v ((ε χ).toMul g)).toAdd := rfl

theorem mem_characterValuation_ker (ε : L →+ Additive (G →* K))
    (v : K →* Multiplicative ℤ) (g : G) :
    g ∈ (characterValuation ε v).ker ↔ ∀ χ, v ((ε χ).toMul g) = 1 := by
  change characterValuationPairing ε v g = 0 ↔ _
  constructor
  · intro h χ
    exact DFunLike.congr_fun h χ
  · intro h
    apply AddMonoidHom.ext
    intro χ
    exact h χ

/-- Absolute values of the given character evaluations, with no replacement
of the underlying evaluation family. -/
def evaluationNormCharacters (ε : L →+ Additive (G →* K)) (n : K →* ℝ≥0ˣ) :
    L →+ Additive (G →* ℝ≥0ˣ) where
  toFun χ := Additive.ofMul (n.comp (ε χ).toMul)
  map_zero' := by
    change n.comp (ε 0).toMul = 1
    rw [map_zero]
    apply MonoidHom.ext
    intro g
    change n 1 = 1
    exact map_one n
  map_add' χ ψ := by
    change n.comp (ε (χ + ψ)).toMul = n.comp (ε χ).toMul * n.comp (ε ψ).toMul
    rw [map_add]
    apply MonoidHom.ext
    intro g
    change n ((ε χ).toMul g * (ε ψ).toMul g) = _
    exact n.map_mul _ _

@[simp]
theorem evaluationNormCharacters_apply (ε : L →+ Additive (G →* K))
    (n : K →* ℝ≥0ˣ) (χ : L) (g : G) :
    (evaluationNormCharacters ε n χ).toMul g = n ((ε χ).toMul g) := rfl

/-- The valuation kernel is the norm-one subgroup when the given valuation
and norm on the value group have the same unit kernel. -/
theorem characterValuation_ker (ε : L →+ Additive (G →* K))
    (v : K →* Multiplicative ℤ) (n : K →* ℝ≥0ˣ)
    (h : ∀ a, v a = 1 ↔ n a = 1) :
    (characterValuation ε v).ker =
      commonNormKernel (fun χ => (evaluationNormCharacters ε n χ).toMul) := by
  ext g
  rw [mem_characterValuation_ker, mem_commonNormKernel]
  exact forall_congr' fun χ => h ((ε χ).toMul g)

/-- The actual image of the valuation composite. No finite-generation or
full-rank assertion is included in this definition. -/
def characterValuationImage (ε : L →+ Additive (G →* K))
    (v : K →* Multiplicative ℤ) : Subgroup (Multiplicative (L →+ ℤ)) :=
  (characterValuation ε v).range

/-- The exact algebraic quotient by the valuation kernel. -/
def characterValuationQuotientEquiv (ε : L →+ Additive (G →* K))
    (v : K →* Multiplicative ℤ) :
    (G ⧸ (characterValuation ε v).ker) ≃* characterValuationImage ε v :=
  QuotientGroup.quotientKerEquivRange (characterValuation ε v)

@[simp]
theorem characterValuationQuotientEquiv_mk (ε : L →+ Additive (G →* K))
    (v : K →* Multiplicative ℤ) (g : G) :
    characterValuationQuotientEquiv ε v (QuotientGroup.mk g) =
      ⟨characterValuation ε v g, g, rfl⟩ := rfl

/-- Identify the quotient already used for unramified characters with the
actual valuation image, under the displayed equality of value kernels. -/
def normKernelValuationQuotientEquiv (ε : L →+ Additive (G →* K))
    (v : K →* Multiplicative ℤ) (n : K →* ℝ≥0ˣ)
    (h : ∀ a, v a = 1 ↔ n a = 1) :
    (G ⧸ commonNormKernel (fun χ => (evaluationNormCharacters ε n χ).toMul)) ≃*
      characterValuationImage ε v :=
  (QuotientGroup.quotientMulEquivOfEq (characterValuation_ker ε v n h).symm).trans
    (characterValuationQuotientEquiv ε v)

@[simp]
theorem normKernelValuationQuotientEquiv_mk (ε : L →+ Additive (G →* K))
    (v : K →* Multiplicative ℤ) (n : K →* ℝ≥0ˣ)
    (h : ∀ a, v a = 1 ↔ n a = 1) (g : G) :
    normKernelValuationQuotientEquiv ε v n h (QuotientGroup.mk g) =
      ⟨characterValuation ε v g, g, rfl⟩ := by
  change characterValuationQuotientEquiv ε v
    (QuotientGroup.quotientMulEquivOfEq (characterValuation_ker ε v n h).symm
      (QuotientGroup.mk g)) = _
  rw [QuotientGroup.quotientMulEquivOfEq_mk]
  rfl

/-- Containment of the abstract group commutator subgroup follows from the
commutative target; no assertion about algebraic derived-group points is used. -/
theorem commutator_le_characterValuation_ker (ε : L →+ Additive (G →* K))
    (v : K →* Multiplicative ℤ) :
    _root_.commutator G ≤ (characterValuation ε v).ker :=
  Abelianization.commutator_subset_ker (characterValuation ε v)

end Langlands.Plancherel
