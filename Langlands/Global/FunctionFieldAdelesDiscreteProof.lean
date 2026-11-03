import Langlands.Global.FunctionFieldAdelesDiscreteStatement
import Langlands.Global.FunctionFieldValuationPlaces
import Langlands.Global.CurvePlaceExtension
import Mathlib.RingTheory.Valuation.LocalSubring
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.Topology.Algebra.OpenSubgroup

/-! # Actual arithmetic isolates the function-field adelic diagonal -/

noncomputable section

universe u

open IsDedekindDomain
open scoped Valued RestrictedProduct

namespace Langlands.Global

section Arithmetic

variable (k F : Type u) [Field k] [Field F] [Algebra k F]
  [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F] [FunctionField k F]

/-- An element integral at every actual curve place is integral over the constants. -/
theorem isIntegral_of_forall_mem_curvePlace {x : F}
    (hx : ∀ v : AlgebraicCurve.Place k F, x ∈ v.toValuationSubring) : IsIntegral k x := by
  by_contra hi
  have hn : x ∉ (integralClosure k F).toSubring := hi
  obtain ⟨V, hV, hxV⟩ :=
    Subring.exists_le_valuationSubring_of_isIntegrallyClosedIn hn
  have hK : ∀ a : k, algebraMap k F a ∈ V :=
    fun a => hV ((integralClosure k F).algebraMap_mem a)
  have htop : V ≠ ⊤ := by
    intro he
    exact hxV (he ▸ Set.mem_univ x)
  exact hxV (hx (functionFieldPlaceOfValuationSubring k F V hK htop))

/-- Global integrality and one strict local inequality force an element to vanish. -/
theorem eq_zero_of_forall_mem_curvePlace_of_lt_one
    {x : F} (hx : ∀ v : AlgebraicCurve.Place k F, x ∈ v.toValuationSubring)
    (v : AlgebraicCurve.Place k F) (hv : v.adicValuation x < 1) : x = 0 := by
  by_contra hx0
  exact (Valuation.transcendental_of_ne_one k x hx0 (ne_of_lt hv))
    (isIntegral_of_forall_mem_curvePlace k F hx).isAlgebraic

end Arithmetic

section CurveTopology

variable (k F : Type u) [Field k] [PerfectField k] [Field F] [Algebra k F]
  [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F] [FunctionField k F]

/-- Integral everywhere and strictly inside the unit ball at one actual place. -/
def curvePlaceDiagonalIsolatingSet : Set (CurvePlaceAdeleRing k F) :=
  {a | (∀ v, a v ∈ curvePlaceCompletionIntegers v) ∧
    Valued.v (a (curvePlaceReference k F)) < 1}

omit [PerfectField k] in
theorem isOpen_curvePlaceDiagonalIsolatingSet :
    IsOpen (curvePlaceDiagonalIsolatingSet k F) := by
  have h₁ : IsOpen {a : CurvePlaceAdeleRing k F |
      ∀ v, a v ∈ curvePlaceCompletionIntegers v} :=
    RestrictedProduct.isOpen_forall_mem (fun _ => Valued.isOpen_valuationSubring _)
  have h₂ : IsOpen {a : CurvePlaceAdeleRing k F |
      Valued.v (a (curvePlaceReference k F)) < 1} := by
    have heval : Continuous (fun a : CurvePlaceAdeleRing k F =>
        a (curvePlaceReference k F)) :=
      RestrictedProduct.continuous_eval (curvePlaceReference k F)
    have hball := (Valued.isOpen_ball (curvePlaceCompletion (curvePlaceReference k F)) 1).preimage
      heval
    simpa only [Set.preimage_ofPred_eq, Valuation.restrict_lt_one_iff] using hball
  exact h₁.inter h₂

omit [PerfectField k] in
theorem zero_mem_curvePlaceDiagonalIsolatingSet :
    (0 : CurvePlaceAdeleRing k F) ∈ curvePlaceDiagonalIsolatingSet k F := by
  refine ⟨fun v => (curvePlaceCompletionIntegers v).zero_mem, ?_⟩
  change Valued.v (0 : curvePlaceCompletion (curvePlaceReference k F)) < 1
  simp

theorem curvePlaceDiagonalIsolatingSet_inter_range :
    curvePlaceDiagonalIsolatingSet k F ∩
      ((curvePlaceAdeleDiagonal k F).range : Set (CurvePlaceAdeleRing k F)) = {0} := by
  ext a
  constructor
  · rintro ⟨⟨hint, hstrict⟩, x, rfl⟩
    have hx : x = 0 := by
      apply eq_zero_of_forall_mem_curvePlace_of_lt_one k F
        (fun v => (curvePlaceCompletion_mem_integers_iff v x).mp (hint v))
        (curvePlaceReference k F)
      change Valued.v (algebraMap F
        ((curvePlaceReference k F).heightOneSpectrum.adicCompletion F) x) < 1 at hstrict
      simpa only [HeightOneSpectrum.algebraMap_adicCompletion, Function.comp_apply,
        Algebra.algebraMap_self, RingHom.id_apply,
        HeightOneSpectrum.valuedAdicCompletion_eq_valuation',
        AlgebraicCurve.Place.adicValuation] using hstrict
    simp [hx]
  · rintro rfl
    exact ⟨zero_mem_curvePlaceDiagonalIsolatingSet k F,
      (curvePlaceAdeleDiagonal k F).range.zero_mem⟩

theorem curvePlaceAdeleDiagonal_discreteTopology :
    DiscreteTopology (curvePlaceAdeleDiagonal k F).range := by
  refine discreteTopology_of_isOpen_singleton_zero ?_
  refine isOpen_induced_iff.mpr
    ⟨curvePlaceDiagonalIsolatingSet k F, isOpen_curvePlaceDiagonalIsolatingSet k F, ?_⟩
  ext ⟨a, ha⟩
  have h := Set.ext_iff.mp (curvePlaceDiagonalIsolatingSet_inter_range k F) a
  simp only [Set.mem_inter_iff, SetLike.mem_coe, ha, and_true, Set.mem_singleton_iff] at h
  simp only [Set.mem_preimage, Set.mem_singleton_iff, h]
  constructor
  · rintro rfl
    rfl
  · intro he
    exact congrArg Subtype.val he

theorem curvePlaceAdeleDiagonal_isClosed :
    IsClosed ((curvePlaceAdeleDiagonal k F).range : Set (CurvePlaceAdeleRing k F)) := by
  let : DiscreteTopology (curvePlaceAdeleDiagonal k F).range :=
    curvePlaceAdeleDiagonal_discreteTopology k F
  exact AddSubgroup.isClosed_of_discreteTopology
    (U := (curvePlaceAdeleDiagonal k F).range.toAddSubgroup)

end CurveTopology

section AbsoluteValueTopology

variable (k F : Type u) [Field k] [Field F] [Algebra k F] [Finite k]
  [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F] [FunctionField k F]

private theorem mem_absoluteValueDiagonal_range_iff (a : RealAbsoluteValueAdeleRing k F) :
    a ∈ (realAbsoluteValueAdeleDiagonal k F).range ↔
      functionFieldAbsoluteValueAdeleEquiv k F a ∈ (curvePlaceAdeleDiagonal k F).range := by
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨x, (functionFieldAbsoluteValueAdeleEquiv_diagonal k F x).symm⟩
  · rintro ⟨x, hx⟩
    refine ⟨x, (functionFieldAbsoluteValueAdeleEquiv k F).injective ?_⟩
    rw [functionFieldAbsoluteValueAdeleEquiv_diagonal]
    exact hx

theorem realAbsoluteValueAdeleDiagonal_discreteTopology :
    DiscreteTopology (realAbsoluteValueAdeleDiagonal k F).range := by
  let : DiscreteTopology (curvePlaceAdeleDiagonal k F).range :=
    curvePlaceAdeleDiagonal_discreteTopology k F
  let e : (realAbsoluteValueAdeleDiagonal k F).range ≃ₜ
      (curvePlaceAdeleDiagonal k F).range :=
    (functionFieldAbsoluteValueAdeleHomeomorph k F).subtype
      (mem_absoluteValueDiagonal_range_iff k F)
  exact e.discreteTopology_iff.mpr inferInstance

theorem realAbsoluteValueAdeleDiagonal_isClosed :
    IsClosed ((realAbsoluteValueAdeleDiagonal k F).range :
      Set (RealAbsoluteValueAdeleRing k F)) := by
  convert (curvePlaceAdeleDiagonal_isClosed k F).preimage
    (continuous_functionFieldAbsoluteValueAdeleEquiv k F) using 1
  ext a
  exact mem_absoluteValueDiagonal_range_iff k F a

end AbsoluteValueTopology

theorem functionFieldAdelesDiscrete : FunctionFieldAdelesDiscreteStatement.{u} := by
  constructor
  · intro k F _ _ _ _ _ _ _
    exact ⟨curvePlaceAdeleDiagonal_discreteTopology k F,
      curvePlaceAdeleDiagonal_isClosed k F⟩
  · intro k F _ _ _ _ _ _ _
    exact ⟨realAbsoluteValueAdeleDiagonal_discreteTopology k F,
      realAbsoluteValueAdeleDiagonal_isClosed k F⟩

end Langlands.Global
