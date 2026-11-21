import Langlands.Algebra.LocalDivisionCyclicBrauerCarry
import Langlands.ClassFieldTheory.Local.BrauerLocalInvariant
import Langlands.ClassFieldTheory.Local.LocalDivisionSplittingDegree

/-! # Local Brauer invariant of a cyclic division parameter -/

noncomputable section

namespace Langlands.ClassFieldTheory.Local

open Module ValuativeRel CentralDivision CentralSimple _root_.Langlands.Brauer BrauerComparison
open LocalGalois.Separable
open scoped TensorProduct

universe u

variable (K D : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [DivisionRing D] [Algebra K D]
  [FiniteDimensional K D] [Algebra.IsCentral K D]

private def transportCyclicCoordinate {G : Type u} [Group G] {m n : ℕ} (h : m = n)
    (χ : G ≃* Multiplicative (ZMod m)) : G ≃* Multiplicative (ZMod n) :=
  h ▸ χ

private theorem transportCyclicCoordinate_generator {G : Type u} [Group G] {m n : ℕ}
    (h : m = n) (χ : G ≃* Multiplicative (ZMod m)) :
    cyclicCoordinateGenerator (transportCyclicCoordinate h χ) = cyclicCoordinateGenerator χ := by
  cases h
  rfl

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
private theorem transportCyclicCoordinate_class {E : Type u} [Field E] [Algebra K E]
    {m n : ℕ} [NeZero m] [NeZero n] (h : m = n)
    (χ : (E ≃ₐ[K] E) ≃* Multiplicative (ZMod m)) (a : Kˣ) :
    cyclicClass K E (transportCyclicCoordinate h χ).toMonoidHom a =
      cyclicClass K E χ.toMonoidHom a := by
  cases h
  rfl

variable (E : IntermediateField K (SeparableClosure K)) [FiniteDimensional K E] [IsGalois K E]
  (hE : ArithmeticUnramified K E) (ι : E →ₐ[K] D)
  (hdegree : Module.finrank K E = CentralSimple.reducedDegree K D) {j : Dˣ}
  (hj : ∀ a : E, (j : D) * ι a = ι (finiteUnramifiedFrobenius K E hE a) * (j : D))

local notation "d" => CentralSimple.reducedDegree K D
local instance cyclicInvariantDegreeNonzero : NeZero (CentralSimple.reducedDegree K D) :=
  ⟨(CentralSimple.reducedDegree_pos K D).ne'⟩

/-- Arithmetic Frobenius has order equal to the degree of the actual
unramified Galois stage. -/
theorem finiteUnramifiedFrobenius_orderOf :
    orderOf (finiteUnramifiedFrobenius K E hE) = Module.finrank K E := by
  rw [orderOf_eq_card_of_forall_mem_zpowers (finiteUnramifiedFrobenius_generates K E hE),
    IsGalois.card_aut_eq_finrank]

local notation "hσ" => Eq.trans (finiteUnramifiedFrobenius_orderOf K E hE) hdegree
local notation "parameter" => cyclicParameter K D ι hj hdegree hσ

/-- The arithmetic cyclic splitting chart uses the powers of the implementing
unit as the basis for the left action of the actual unramified field. -/
def divisionOppositeArithmeticChart : E ⊗[K] Dᵐᵒᵖ ≃ₐ[E] Matrix (Fin d) (Fin d) E :=
  subfieldOppositeSplittingChart K D ι (implementingUnitBasis K D ι hj hdegree hσ)

/-- The Library invariant of the opposite division algebra is the normalized
order of the central parameter divided by the reduced degree. -/
theorem localBrauerInvariant_opposite_cyclicParameter :
    localBrauerInvariant K (classOf (opposite (divisionAlgebraCSA K D))) =
      rationalClass ((normalizedUnitOrder K (.ofMul parameter) : ℚ) / d) := by
  let χ₀ := finiteUnramifiedCyclicCoordinate K E hE
  let χ := transportCyclicCoordinate hdegree χ₀
  let : NeZero (Module.finrank K E) := ⟨Module.finrank_pos.ne'⟩
  have hgen : cyclicCoordinateGenerator χ = finiteUnramifiedFrobenius K E hE :=
    (transportCyclicCoordinate_generator hdegree χ₀).trans
      (cyclicCoordinateGenerator_finiteUnramified K E hE)
  have hc := subfieldOppositeSplittingChart_relativeClass K D ι
    (implementingUnitBasis K D ι hj hdegree hσ) hj χ hdegree hσ hgen
  let e := divisionOppositeArithmeticChart K D E hE ι hdegree hj
  rw [localBrauerInvariant_at_chart K (opposite (divisionAlgebraCSA K D)) E hE e]
  change spectralUnramifiedInvariant K E hE
    (relativeClass (subfieldOppositeSplittingChart K D ι (implementingUnitBasis K D ι hj hdegree hσ))) = _
  rw [hc, transportCyclicCoordinate_class K hdegree χ₀, spectralUnramifiedInvariant_cyclicClass]
  exact congrArg (fun n : ℕ => rationalClass ((normalizedUnitOrder K (.ofMul parameter) : ℚ) / n)) hdegree

/-- In the Library convention the original division algebra has the negative
of the order fraction for the arithmetic conjugation law. -/
theorem localBrauerInvariant_cyclicParameter :
    localBrauerInvariant K (classOf (divisionAlgebraCSA K D)) =
      -rationalClass ((normalizedUnitOrder K (.ofMul parameter) : ℚ) / d) := by
  have h := localBrauerInvariant_opposite_cyclicParameter K D E hE ι hdegree hj
  rw [classOf_opposite, map_neg] at h
  exact neg_eq_iff_eq_neg.mp h

end Langlands.ClassFieldTheory.Local
