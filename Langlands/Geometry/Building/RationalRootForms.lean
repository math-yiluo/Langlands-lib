import Langlands.Geometry.Building.KPApartment
import Langlands.Geometry.Building.CocharacterUniformizerProof
import Mathlib.Algebra.Module.LocalizedModule.Int
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.Localization.FractionRing

/-! # Rational character evaluation and reduced apartment root forms -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct
open Langlands.LinearAlgebra.RationalSpan

namespace Langlands.GroupScheme.RealTorusSpace

variable {k : Type u} [Field k]
  (S : CommGroupScheme (Spec (CommRingCat.of k)))

private def integralEval : characterLattice S →ₗ[ℤ] Module.Dual ℝ (V S) :=
  AddMonoidHom.toIntLinearMap
    { toFun := eval S
      map_zero' := by
        rw [eval_eq_pair, TensorProduct.tmul_zero, map_zero]
      map_add' a b := by
        simp only [eval_eq_pair, TensorProduct.tmul_add, map_add] }

/-- Evaluation of a rational character on the full real cocharacter space. -/
def evalRat : (ℚ ⊗[ℤ] characterLattice S) →ₗ[ℚ] Module.Dual ℝ (V S) :=
  AlgebraTensorModule.lift
    (LinearMap.toSpanSingleton ℚ (characterLattice S →ₗ[ℤ] Module.Dual ℝ (V S))
      (integralEval S))

@[simp] theorem evalRat_tmul (q : ℚ) (χ : characterLattice S) :
    evalRat S (q ⊗ₜ[ℤ] χ) = q • eval S χ := rfl

@[simp] theorem evalRat_toRat (χ : characterLattice S) :
    evalRat S (toRat χ) = eval S χ := by
  simp [toRat_apply]

/-- Rational evaluation is injective for every actual split torus. -/
theorem evalRat_injective (hS : IsSplitTorus S.toGrp) :
    Function.Injective (evalRat S) := by
  apply LinearMap.ker_eq_bot.mp
  apply le_antisymm
  · intro x hx
    obtain ⟨n, χ, hχ⟩ := IsLocalizedModule.exists_integer_multiple
      (nonZeroDivisors ℤ) (TensorProduct.mk ℤ ℚ (characterLattice S) 1) x
    change (1 : ℚ) ⊗ₜ[ℤ] χ = n.val • x at hχ
    have heval : eval S χ = 0 := by
      have h := congrArg (evalRat S) hχ
      simpa only [evalRat_tmul, one_smul, map_zsmul, LinearMap.mem_ker.mp hx,
        smul_zero] using h
    have hχzero : χ = 0 := by
      let := CocharacterUniformizer.latticePairing_isPerfPair k S hS
      apply (LinearMap.IsPerfPair.bijective_left (latticePairing S)).injective
      ext ν
      have h := congrArg (fun f : Module.Dual ℝ (V S) =>
        f ((1 : ℝ) ⊗ₜ[ℤ] ν)) heval
      simpa only [eval_tmul, one_mul, LinearMap.zero_apply, map_zero, Int.cast_eq_zero]
        using h
    have hn : (n.val : ℚ) ≠ 0 := by
      exact_mod_cast (mem_nonZeroDivisors_iff_ne_zero.mp n.property)
    have hnx : (n.val : ℚ) • x = 0 := by
      simpa only [hχzero, TensorProduct.tmul_zero, Int.cast_smul_eq_zsmul] using hχ.symm
    change x = 0
    exact (smul_eq_zero.mp hnx).resolve_left hn
  · exact bot_le

end Langlands.GroupScheme.RealTorusSpace

namespace Langlands.Geometry.Building

open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace

variable {k : Type u} [Field k]
  {S : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  (i : S.toGrp ⟶ G)

private theorem evalRat_rootAnnihilator (x : relativeRootSpan i)
    (v : V S) (hv : v ∈ rootAnnihilator i) : evalRat S x v = 0 := by
  have aux : ∀ y, y ∈ Submodule.span ℚ (toRat '' relativeRoots i) →
      evalRat S y v = 0 := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem a ha =>
      obtain ⟨χ, hχ, rfl⟩ := ha
      rw [evalRat_toRat]
      exact (mem_rootAnnihilator.mp hv) χ hχ
    | zero => simp
    | add a b _ _ ha hb => simp [ha, hb]
    | smul q a _ ha => simp [ha]
  exact aux x.val x.property

/-- The rational linear map from the actual relative-root span to reduced
apartment functionals. -/
def relativeRootForm :
    relativeRootSpan i →ₗ[ℚ] Module.Dual ℝ (TranslationSpace i) where
  toFun x := (rootAnnihilator i).liftQ (evalRat S x) fun v hv =>
    LinearMap.mem_ker.mpr (evalRat_rootAnnihilator i x v hv)
  map_add' x y := by
    apply LinearMap.ext
    intro v
    refine Submodule.Quotient.induction_on _ v fun v => ?_
    change evalRat S (x.val + y.val) v = _
    simp
  map_smul' q x := by
    apply LinearMap.ext
    intro v
    refine Submodule.Quotient.induction_on _ v fun v => ?_
    change evalRat S (q • x.val) v = _
    simp

@[simp] theorem relativeRootForm_mk (x : relativeRootSpan i) (v : V S) :
    relativeRootForm i x (Submodule.Quotient.mk v) = evalRat S x v := rfl

@[simp] theorem relativeRootForm_toRat (a : relativeRoots i) :
    relativeRootForm i ⟨toRat a.val, toRat_mem_ratSpan a.property⟩ = rootForm i a := by
  apply LinearMap.ext
  intro v
  refine Submodule.Quotient.induction_on _ v fun v => ?_
  simp

theorem relativeRootForm_injective (hS : IsSplitTorus S.toGrp) :
    Function.Injective (relativeRootForm i) := by
  intro x y h
  apply Subtype.ext
  apply evalRat_injective S hS
  apply LinearMap.ext
  intro v
  exact congrArg (fun f : Module.Dual ℝ (TranslationSpace i) =>
    f (Submodule.Quotient.mk v)) h

theorem relativeRootForm_range :
    LinearMap.range (relativeRootForm i) =
      Submodule.span ℚ (Set.range (rootForm i)) := by
  let r : relativeRoots i → relativeRootSpan i :=
    fun a => ⟨toRat a.val, toRat_mem_ratSpan a.property⟩
  have hrange : Set.range (fun a : relativeRoots i => toRat a.val) =
      toRat '' relativeRoots i := by
    ext x
    simp
  have hgen : Submodule.span ℚ (Set.range r) = ⊤ := by
    apply (Submodule.span_range_subtype_eq_top_iff (relativeRootSpan i)
      (fun a : relativeRoots i => toRat_mem_ratSpan a.property)).2
    change Submodule.span ℚ (Set.range (fun a : relativeRoots i => toRat a.val)) =
      Submodule.span ℚ (toRat '' relativeRoots i)
    rw [hrange]
  rw [LinearMap.range_eq_map, ← hgen, Submodule.map_span, ← Set.range_comp]
  congr 1
  exact congrArg Set.range (funext fun a => relativeRootForm_toRat i a)

/-- Rational relative roots and their real apartment functionals have the same
rational span. -/
def relativeRootFormEquiv (hS : IsSplitTorus S.toGrp) :
    relativeRootSpan i ≃ₗ[ℚ] Submodule.span ℚ (Set.range (rootForm i)) :=
  LinearEquiv.ofBijective
    ((relativeRootForm i).codRestrict _ (fun x =>
      relativeRootForm_range i ▸ LinearMap.mem_range_self (relativeRootForm i) x))
    ⟨fun _ _ h => relativeRootForm_injective i hS (congrArg Subtype.val h), by
      intro x
      have hx : x.val ∈ LinearMap.range (relativeRootForm i) :=
        (relativeRootForm_range i).symm ▸ x.property
      obtain ⟨y, hy⟩ := hx
      exact ⟨y, Subtype.ext hy⟩⟩

@[simp] theorem relativeRootFormEquiv_coe (hS : IsSplitTorus S.toGrp)
    (x : relativeRootSpan i) :
    (relativeRootFormEquiv i hS x : Module.Dual ℝ (TranslationSpace i)) =
      relativeRootForm i x := rfl

end Langlands.Geometry.Building
