/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Lisse.LisseScalarFiberMaps
import Mathlib.RingTheory.AdicCompletion.Basic
import WeilConjectures.AlgebraicGeometry.Lisse.LisseScalarFiberReductions
import WeilConjectures.NumberTheory.Padics.AdicLimitFiniteModulesSupplement

/-! # Integral scalar extension commutes with geometric fibres

## References

* Deligne, Weil II (1.1.1) b), d), pp. 146-147
* Weil II (1.1.1) b), d), pp. 146-147
* Stacks Project, Tag 09B8
-/

@[expose] public section

universe d
open CategoryTheory CategoryTheory.Limits Opposite
open scoped Pointwise TensorProduct

namespace AlgebraicGeometry.Scheme

private theorem completeMapBijective {R : Type*} [CommRing R] (I : Ideal R)
    (M : ModuleCat.{d + 1} R) [IsAdicComplete I M] (D : ℕᵒᵖ ⥤ ModuleCat.{d + 1} R)
    (c : M ⟶ limit D)
    (hq : ∀ n : ℕ, Function.Surjective (c ≫ limit.π D (op n)).hom ∧
      LinearMap.ker (c ≫ limit.π D (op n)).hom = I ^ (n + 1) • ⊤) :
    Function.Bijective c := by
  classical
  let q (n : ℕ) := (c ≫ limit.π D (op n)).hom
  let e (n : ℕ) : (M ⧸ (I ^ (n + 1) • ⊤ : Submodule R M)) ≃ₗ[R] D.obj (op n) :=
    (Submodule.quotEquivOfEq _ _ (hq n).2.symm).trans
      ((q n).quotKerEquivOfSurjective (hq n).1)
  have he (n : ℕ) (x : M) : e n (Submodule.Quotient.mk x) = q n x := by
    simp only [e, LinearEquiv.trans_apply, Submodule.quotEquivOfEq_mk]
    exact LinearMap.quotKerEquivOfSurjective_apply_mk _ _ _
  let f (n : ℕ) : ↥(limit D) →ₗ[R] M ⧸ (I ^ (n + 1) • ⊤ : Submodule R M) :=
    (e n).symm.toLinearMap.comp (limit.π D (op n)).hom
  have hef (n : ℕ) (z : ↥(limit D)) : e n (f n z) = limit.π D (op n) z :=
    (e n).apply_symm_apply _
  have ht (n : ℕ) (x : M ⧸ (I ^ (n + 2) • ⊤ : Submodule R M)) :
      e n (Submodule.factorPow I M (Nat.le_succ (n + 1)) x) =
        D.map (homOfLE (Nat.le_succ n)).op (e (n + 1) x) := by
    induction x using Submodule.Quotient.induction_on with
    | _ x =>
      change e n (Submodule.Quotient.mk x) = _
      rw [he, he]
      exact (ConcreteCategory.congr_hom
        (limit.w D (homOfLE (Nat.le_succ n)).op) (c x)).symm
  have hf (n : ℕ) :
      (Submodule.factorPow I M (Nat.le_succ (n + 1))).comp (f (n + 1)) = f n := by
    ext z
    apply (e n).injective
    rw [LinearMap.comp_apply, ht, hef, hef]
    exact ConcreteCategory.congr_hom (limit.w D (homOfLE (Nat.le_succ n)).op) z
  have ha : StrictMono (fun n : ℕ ↦ n + 1) := fun _ _ h ↦ Nat.add_lt_add_right h 1
  let g := IsAdicComplete.StrictMono.lift I ha f (fun {n} ↦ hf n)
  have hg (n : ℕ) (z : ↥(limit D)) :
      (Submodule.Quotient.mk (g z) : M ⧸ (I ^ (n + 1) • ⊤ : Submodule R M)) = f n z :=
    IsAdicComplete.StrictMono.mk_lift I ha f (fun {n} ↦ hf n) z
  constructor
  · intro x y hxy
    apply sub_eq_zero.mp
    apply (inferInstance : IsHausdorff I M).haus (x - y)
    intro n
    apply SModEq.zero.mpr
    apply (Submodule.smul_mono_left (Ideal.pow_le_pow_right (Nat.le_succ n)))
    rw [← (hq n).2]
    change q n (x - y) = 0
    change (limit.π D (op n)) (c (x - y)) = 0
    rw [map_sub, hxy, sub_self, map_zero]
  · intro z
    refine ⟨g z, ?_⟩
    apply Concrete.limit_ext D
    intro j
    change q j.unop (g z) = _
    rw [← he, hg, hef]

private theorem ringExtensionFinite {R S : Type (d + 1)} [CommRing R] [CommRing S]
    (α : R →+* S) (M : ModuleCat.{d + 1} R) [Module.Finite R M] :
    Module.Finite S ((ModuleCat.ringExtendScalars.{d + 1, d + 1} α).obj M) := by
  let e := (ModuleCat.ringExtendScalarsAdj.{d + 1, d + 1} α).leftAdjointUniq
    (ModuleCat.extendRestrictScalarsAdj.{d + 1, d + 1, d + 1} α)
  let : Algebra R S := α.toAlgebra
  have : Module.Finite S ((ModuleCat.extendScalars α).obj M) := by
    change Module.Finite S (S ⊗[R] M)
    infer_instance
  exact Module.Finite.equiv (e.app M).symm.toLinearEquiv

variable (Y : Scheme.{d}) {Ω : Type d} [Field Ω] [IsAlgClosed Ω]
  (y : Spec (.of Ω) ⟶ Y) (l : ℕ) [Fact l.Prime]
  (E : Type (d + 1)) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  [IsNoetherian Y] [Y.IsSeparated] [∀ x : Y, Invertible (l : Y.residueField x)]
  (L : Type (d + 1)) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L)

/-- The constructed integral scalar comparison is invertible. -/
theorem lisseIntegralScalarFiberComparison_isIso (F : LisseIntegralSheaf l E Y) :
    IsIso (lisseIntegralScalarFiberComparison Y y l E L ι F) := by
  let S := Padic.coefficientExtensionIntegers l L
  let J := Ideal.span ({Padic.coefficientExtensionUniformizer l L} : Set S)
  let M := (ModuleCat.ringExtendScalars.{d + 1, d + 1}
    (lisseIntegerInclusion l E L ι)).obj (lisseIntegralFiber l E Y y F)
  let D := ((lisseIntegralScalarExtensionData l E Y L ι).functor.obj F).obj ⋙
    (pointSmallEtale y).ulift.{d + 1}.sheafFiber
  have := lisseIntegralFiber_finite Y y l E F
  have : Module.Finite S M := ringExtensionFinite _ _
  have : IsAdicComplete J M := AdicCompletion.of_bijective_iff.mp
    ((Padic.finite_module_adic_complete_and_hom.{d + 1, d + 1, d + 1} l L).1 M).2.1
  apply (ConcreteCategory.isIso_iff_bijective _).mpr
  exact completeMapBijective J M D (lisseIntegralScalarFiberComparison Y y l E L ι F)
    (lisseIntegralScalarFiberComparison_reductions Y y l E L ι F)

end AlgebraicGeometry.Scheme
