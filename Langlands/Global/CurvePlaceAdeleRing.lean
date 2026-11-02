import Langlands.AnthropicFLT.Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing

/-! # Restricted products over actual discrete curve places -/

noncomputable section

universe u

open IsDedekindDomain
open scoped RestrictedProduct

namespace Langlands.Global

variable {k F : Type u} [Field k] [Field F] [Algebra k F]

/-- The completion of `F` at the maximal ideal of an actual discrete curve place. -/
abbrev curvePlaceCompletion (v : AlgebraicCurve.Place k F) :=
  v.heightOneSpectrum.adicCompletion F

/-- The actual valuation subring in the completed field. -/
abbrev curvePlaceCompletionIntegers (v : AlgebraicCurve.Place k F) :=
  v.heightOneSpectrum.adicCompletionIntegers F

variable (k F)

/-- The cofinite restricted product over all actual discrete places trivial on `k`. -/
abbrev CurvePlaceAdeleRing :=
  Πʳ v : AlgebraicCurve.Place k F, [curvePlaceCompletion v, curvePlaceCompletionIntegers v]

instance : IsTopologicalRing (CurvePlaceAdeleRing k F) := by
  have : Fact (∀ v : AlgebraicCurve.Place k F,
      IsOpen (curvePlaceCompletionIntegers v : Set (curvePlaceCompletion v))) :=
    ⟨fun _ => Valued.isOpen_valuationSubring _⟩
  exact RestrictedProduct.isTopologicalRing _

/-- The level subring is integral at every place outside the finite set. -/
def curvePlaceAdeleLevel (S : Finset (AlgebraicCurve.Place k F)) :
    Subring (CurvePlaceAdeleRing k F) where
  carrier := {a | ∀ v, v ∉ S → a v ∈ curvePlaceCompletionIntegers v}
  zero_mem' v _ := (curvePlaceCompletionIntegers v).zero_mem
  one_mem' v _ := (curvePlaceCompletionIntegers v).one_mem
  add_mem' ha hb v hv := (curvePlaceCompletionIntegers v).toSubring.add_mem (ha v hv) (hb v hv)
  mul_mem' ha hb v hv := (curvePlaceCompletionIntegers v).toSubring.mul_mem (ha v hv) (hb v hv)
  neg_mem' ha v hv := (curvePlaceCompletionIntegers v).toSubring.neg_mem (ha v hv)

@[simp]
theorem mem_curvePlaceAdeleLevel (S : Finset (AlgebraicCurve.Place k F))
    (a : CurvePlaceAdeleRing k F) :
    a ∈ curvePlaceAdeleLevel k F S ↔
      ∀ v, v ∉ S → a v ∈ curvePlaceCompletionIntegers v := Iff.rfl

theorem isOpen_curvePlaceAdeleLevel (S : Finset (AlgebraicCurve.Place k F)) :
    IsOpen (curvePlaceAdeleLevel k F S : Set (CurvePlaceAdeleRing k F)) :=
  RestrictedProduct.isOpen_forall_imp_mem
    (fun v : AlgebraicCurve.Place k F => Valued.isOpen_valuationSubring (curvePlaceCompletion v))

theorem curvePlaceAdeleLevel_mono {S T : Finset (AlgebraicCurve.Place k F)} (hST : S ⊆ T) :
    curvePlaceAdeleLevel k F S ≤ curvePlaceAdeleLevel k F T :=
  fun _ ha v hv => ha v (fun h => hv (hST h))

/-- Enlarging the finite set gives the literal inclusion of level rings. -/
def curvePlaceAdeleLevelMap {S T : Finset (AlgebraicCurve.Place k F)} (hST : S ⊆ T) :
    curvePlaceAdeleLevel k F S →+* curvePlaceAdeleLevel k F T :=
  Subring.inclusion (curvePlaceAdeleLevel_mono k F hST)

@[simp]
theorem curvePlaceAdeleLevelMap_coe {S T : Finset (AlgebraicCurve.Place k F)} (hST : S ⊆ T)
    (a : curvePlaceAdeleLevel k F S) :
    (curvePlaceAdeleLevelMap k F hST a : CurvePlaceAdeleRing k F) = a := rfl

/-- The actual elements of `F` integral in every place outside `S`. -/
def curvePlaceSIntegers (S : Finset (AlgebraicCurve.Place k F)) : Subring F where
  carrier := {a | ∀ v, v ∉ S → a ∈ v.toValuationSubring}
  zero_mem' v _ := v.toValuationSubring.zero_mem
  one_mem' v _ := v.toValuationSubring.one_mem
  add_mem' ha hb v hv := v.toValuationSubring.toSubring.add_mem (ha v hv) (hb v hv)
  mul_mem' ha hb v hv := v.toValuationSubring.toSubring.mul_mem (ha v hv) (hb v hv)
  neg_mem' ha v hv := v.toValuationSubring.toSubring.neg_mem (ha v hv)

@[simp]
theorem mem_curvePlaceSIntegers (S : Finset (AlgebraicCurve.Place k F)) (a : F) :
    a ∈ curvePlaceSIntegers k F S ↔ ∀ v, v ∉ S → a ∈ v.toValuationSubring := Iff.rfl

theorem curvePlaceSIntegers_mono {S T : Finset (AlgebraicCurve.Place k F)} (hST : S ⊆ T) :
    curvePlaceSIntegers k F S ≤ curvePlaceSIntegers k F T :=
  fun _ ha v hv => ha v (fun h => hv (hST h))

/-- Constants are integral at every curve place. -/
def curvePlaceSIntegersConstants (S : Finset (AlgebraicCurve.Place k F)) :
    k →+* curvePlaceSIntegers k F S :=
  (algebraMap k F).codRestrict _ (fun a v _ => v.algebraMap_mem' a)

instance (S : Finset (AlgebraicCurve.Place k F)) :
    Algebra k (curvePlaceSIntegers k F S) :=
  (curvePlaceSIntegersConstants k F S).toAlgebra

instance (S : Finset (AlgebraicCurve.Place k F)) :
    IsScalarTower k (curvePlaceSIntegers k F S) F :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

theorem curvePlaceCompletion_integral (v : AlgebraicCurve.Place k F) (a : F)
    (ha : a ∈ v.toValuationSubring) :
    algebraMap F (curvePlaceCompletion v) a ∈ curvePlaceCompletionIntegers v := by
  change Valued.v (algebraMap F (v.heightOneSpectrum.adicCompletion F) a) ≤ 1
  simp only [HeightOneSpectrum.algebraMap_adicCompletion, Function.comp_apply,
    Algebra.algebraMap_self, RingHom.id_apply,
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
  exact v.heightOneSpectrum.valuation_le_one (⟨a, ha⟩ : v.toValuationSubring)

/-- The diagonal on outside-`S` integers, constructed without a full-field diagonal assumption. -/
def curvePlaceAdeleLevelDiagonal (S : Finset (AlgebraicCurve.Place k F)) :
    curvePlaceSIntegers k F S →+* curvePlaceAdeleLevel k F S where
  toFun a := by
    classical
    let f : ∀ v : AlgebraicCurve.Place k F, curvePlaceCompletion v :=
      fun v => algebraMap F (curvePlaceCompletion v) a.val
    have hf (v : AlgebraicCurve.Place k F) (hv : v ∉ S) :
        f v ∈ curvePlaceCompletionIntegers v :=
      curvePlaceCompletion_integral k F v a.val (a.property v hv)
    refine ⟨⟨f, ?_⟩, hf⟩
    apply Filter.eventually_cofinite.mpr
    exact S.finite_toSet.subset (fun v hv => by
      by_contra h
      exact hv (hf v h))
  map_one' := by
    apply Subtype.ext
    apply RestrictedProduct.ext
    intro v
    exact map_one (algebraMap F (curvePlaceCompletion v))
  map_mul' a b := by
    apply Subtype.ext
    apply RestrictedProduct.ext
    intro v
    exact map_mul (algebraMap F (curvePlaceCompletion v)) a.val b.val
  map_zero' := by
    apply Subtype.ext
    apply RestrictedProduct.ext
    intro v
    exact map_zero (algebraMap F (curvePlaceCompletion v))
  map_add' a b := by
    apply Subtype.ext
    apply RestrictedProduct.ext
    intro v
    exact map_add (algebraMap F (curvePlaceCompletion v)) a.val b.val

instance (S : Finset (AlgebraicCurve.Place k F)) :
    Algebra (curvePlaceSIntegers k F S) (curvePlaceAdeleLevel k F S) :=
  (curvePlaceAdeleLevelDiagonal k F S).toAlgebra

@[simp]
theorem curvePlaceAdeleLevelDiagonal_apply (S : Finset (AlgebraicCurve.Place k F))
    (a : curvePlaceSIntegers k F S) (v : AlgebraicCurve.Place k F) :
    (curvePlaceAdeleLevelDiagonal k F S a : CurvePlaceAdeleRing k F) v =
      algebraMap F (curvePlaceCompletion v) a.val := rfl

/-- Reassemble the unrestricted and integral completed coordinates of a level. -/
def curvePlaceAdeleLevelAssemble (S : Finset (AlgebraicCurve.Place k F))
    (p : (∀ v : {v : AlgebraicCurve.Place k F // v ∈ S}, curvePlaceCompletion v.1) ×
      (∀ v : {v : AlgebraicCurve.Place k F // v ∉ S}, curvePlaceCompletionIntegers v.1)) :
    curvePlaceAdeleLevel k F S := by
  classical
  let a : ∀ v : AlgebraicCurve.Place k F, curvePlaceCompletion v :=
    fun v => if h : v ∈ S then p.1 ⟨v, h⟩ else (p.2 ⟨v, h⟩ : curvePlaceCompletion v)
  have ha (v : AlgebraicCurve.Place k F) (hv : v ∉ S) :
      a v ∈ curvePlaceCompletionIntegers v := by
    simp only [a, dite_eq_right hv]
    exact (p.2 ⟨v, hv⟩).property
  refine ⟨⟨a, ?_⟩, ha⟩
  apply Filter.eventually_cofinite.mpr
  exact S.finite_toSet.subset (fun v hv => by
    by_contra h
    exact hv (ha v h))

/-- The explicit ring equivalence from a level to its actual completed local factors. -/
def curvePlaceAdeleLevelProductEquiv (S : Finset (AlgebraicCurve.Place k F)) :
    curvePlaceAdeleLevel k F S ≃+*
      (∀ v : {v : AlgebraicCurve.Place k F // v ∈ S}, curvePlaceCompletion v.1) ×
        (∀ v : {v : AlgebraicCurve.Place k F // v ∉ S}, curvePlaceCompletionIntegers v.1) where
  toFun a :=
    (fun v => (a : CurvePlaceAdeleRing k F) v.1,
      fun v => ⟨(a : CurvePlaceAdeleRing k F) v.1, a.property v.1 v.property⟩)
  invFun := curvePlaceAdeleLevelAssemble k F S
  left_inv a := by
    classical
    apply Subtype.ext
    apply RestrictedProduct.ext
    intro v
    change (if h : v ∈ S then _ else _) = _
    split <;> rfl
  right_inv p := by
    classical
    apply Prod.ext
    · funext v
      change (if h : v.1 ∈ S then _ else _) = _
      simp only [dite_eq_left v.property]
    · funext v
      apply Subtype.ext
      change (if h : v.1 ∈ S then _ else _) = _
      simp only [dite_eq_right v.property]
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

@[simp]
theorem curvePlaceAdeleLevelProductEquiv_fst (S : Finset (AlgebraicCurve.Place k F))
    (a : curvePlaceAdeleLevel k F S) (v : {v : AlgebraicCurve.Place k F // v ∈ S}) :
    (curvePlaceAdeleLevelProductEquiv k F S a).1 v =
      (a : CurvePlaceAdeleRing k F) v.1 := rfl

@[simp]
theorem curvePlaceAdeleLevelProductEquiv_snd (S : Finset (AlgebraicCurve.Place k F))
    (a : curvePlaceAdeleLevel k F S) (v : {v : AlgebraicCurve.Place k F // v ∉ S}) :
    ((curvePlaceAdeleLevelProductEquiv k F S a).2 v : curvePlaceCompletion v.1) =
      (a : CurvePlaceAdeleRing k F) v.1 := rfl

end Langlands.Global
