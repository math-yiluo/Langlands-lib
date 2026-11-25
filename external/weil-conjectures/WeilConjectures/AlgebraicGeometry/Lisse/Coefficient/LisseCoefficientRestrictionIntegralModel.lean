/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Lisse.LisseAdicSheaves
import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
import Mathlib.RingTheory.Ideal.Quotient.Index

/-! Integral restriction of finite-coefficient lisse systems.

## References

* Weil II (1.1.1) b)-d)
* Weil II (1.1.1) b)
* Deligne, Weil II (1.1.1) b)-d), pp. 146-147
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
universe d
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme
variable (l : ℕ) [Fact l.Prime] (Y : Scheme.{d})
  [IsNoetherian Y] [Y.IsSeparated] [∀ x : Y, Invertible (l : Y.residueField x)]
  (L E : Type (d + 1)) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (ι : L →ₐ[ℚ_[l]] E)

/-- The ramification subsequence is monotone. -/
theorem lisseIntegralRestrictionIndex_monotone :
    Monotone (fun n : ℕ ↦ lisseRamificationIndex l L E ι * (n + 1) - 1) := by
  intro _ _ h
  exact Nat.sub_le_sub_right
    (Nat.mul_le_mul_left (lisseRamificationIndex l L E ι) (Nat.succ_le_succ h)) 1

/-- Restrict the given lattice along the cofinal ramification-index subsequence.
The object at level n is the restriction of F at level e(n+1)-1. -/
def lisseIntegralRestrictionRaw (F : LisseIntegralSheaf l E Y) :
    AdicIntegralDiagram l L Y :=
  (lisseIntegralRestrictionIndex_monotone l L E ι).functor.op ⋙
    F.obj ⋙ sheafCompose Y.smallEtaleTopology
      (ModuleCat.restrictScalars.{d + 1} (lisseIntegerInclusion l L E ι))

private theorem restriction_annihilated
    (F : LisseIntegralSheaf l E Y) (n : ℕ) (U : Y.Etale) :
    Padic.coefficientExtensionIdeal l L (n + 1) •
      (⊤ : Submodule (Padic.coefficientExtensionIntegers l L)
        (((lisseIntegralRestrictionRaw l Y L E ι F).obj (op n)).obj.obj (op U))) = ⊥ := by
  let e := lisseRamificationIndex l L E ι
  have he : 0 < e := (lisseRamificationIndex_exists l L E ι).choose_spec.1
  have hp : e * (n + 1) - 1 + 1 = e * (n + 1) :=
    Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (Nat.ne_of_gt he)
      (Nat.succ_ne_zero n)))
  have hm : Ideal.map (lisseIntegerInclusion l L E ι)
      (Padic.coefficientExtensionIdeal l L (n + 1)) =
      Padic.coefficientExtensionIdeal l E (e * (n + 1)) := by
    dsimp only [Padic.coefficientExtensionIdeal]
    have hr : Ideal.map (lisseIntegerInclusion l L E ι)
        (Padic.coefficientExtensionMaximalIdeal l L) =
        Padic.coefficientExtensionMaximalIdeal l E ^ e :=
      (lisseRamificationIndex_exists l L E ι).choose_spec.2
    rw [Ideal.map_pow, lisseCoherence_uniformizerIdeal_eq l L, hr, ← pow_mul]
    exact congrArg (fun J : Ideal (Padic.coefficientExtensionIntegers l E) ↦
      J ^ (e * (n + 1))) (lisseCoherence_uniformizerIdeal_eq l E).symm
  apply bot_unique
  apply Submodule.smul_le.mpr
  intro a ha x _
  have ham : lisseIntegerInclusion l L E ι a ∈
      Padic.coefficientExtensionIdeal l E (e * (n + 1)) := by
    rw [← hm]
    exact Ideal.mem_map_of_mem _ ha
  have hh := lisseCoherence_integralLevel_annihilated l E Y F (e * (n + 1) - 1) U
  rw [hp] at hh
  have hx := Submodule.smul_mem_smul ham (Submodule.mem_top
    (x := (show ((F.obj.obj (op (e * (n + 1) - 1))).obj.obj (op U)) from x)))
  rw [hh] at hx
  exact hx

private theorem restriction_finite_lisse
    (F : LisseIntegralSheaf l E Y) (n : ℕ) :
    IsFiniteLocallyConstantSheaf
      ((lisseIntegralRestrictionRaw l Y L E ι F).obj (op n)) := by
  let k := lisseRamificationIndex l L E ι * (n + 1) - 1
  let f := lisseIntegerInclusion l L E ι
  let M := F.obj.obj (op k)
  have hM := F.property.1 k
  let _ := (ModuleCat.restrictCoextendScalarsAdj.{d + 1,d + 1,d + 1} f).isLeftAdjoint
  have hloc : IsLocallyConstantSheaf
      ((sheafCompose Y.smallEtaleTopology (ModuleCat.restrictScalars.{d + 1} f)).obj M) := by
    obtain ⟨⟨𝒰, h𝒰⟩⟩ := hM.toIsLocallyConstantSheaf.nonempty_locallyConstantDatum
    refine ⟨⟨⟨𝒰, fun j ↦ ?_⟩⟩⟩
    have := h𝒰 j
    exact inferInstanceAs (((sheafCompose _ (ModuleCat.restrictScalars.{d + 1} f)).obj
      (M.over _)).IsConstant _)
  refine { toIsLocallyConstantSheaf := hloc, toIsFiniteSheaf := ⟨?_⟩ }
  intro Ω _ _ y
  let p := pointSmallEtale y
  let S := Padic.coefficientExtensionIntegers l E
  let I := Padic.coefficientExtensionIdeal l E (k + 1)
  let V := (p.sheafFiber (A := ModuleCat.{d + 1} S)).obj M
  have hfin : Module.Finite S V :=
    (ModuleCat.isFinitelyGenerated_iff V).mp (hM.isFinitelyGenerated_sheafFiber Ω y)
  have : PreservesFilteredColimitsOfSize.{d, d}
      (CategoryTheory.forget (ModuleCat.{d + 1} S)) :=
    preservesFilteredColimitsOfSize_shrink.{d, d + 1, d, d + 1} _
  have hann : Module.IsTorsionBySet S V I := by
    intro z a
    rcases a with ⟨a, ha⟩
    obtain ⟨U, x, s, rfl⟩ := p.toPresheafFiber_jointly_surjective (P := M.obj) z
    have hz : a • s = 0 := by
      have hh := Submodule.smul_mem_smul ha (Submodule.mem_top (x := s))
      rw [lisseCoherence_integralLevel_annihilated l E Y F k U] at hh
      exact hh
    change a • p.toPresheafFiber U x M.obj s = 0
    rw [← map_smul, hz, map_zero]
  let _ := hann.module
  have : IsScalarTower S (S ⧸ I) V := hann.isScalarTower
  have : Module.Finite (S ⧸ I) V := Module.Finite.of_restrictScalars_finite S (S ⧸ I) V
  have : Finite (S ⧸ I) := Padic.finite_coefficientExtensionRing l E (k + 1) (Nat.le_add_left 1 k)
  have : Finite V := Module.finite_of_finite (S ⧸ I)
  have : Finite ((p.sheafFiber (A := ModuleCat.{d + 1}
      (Padic.coefficientExtensionIntegers l L))).obj
        ((sheafCompose Y.smallEtaleTopology (ModuleCat.restrictScalars.{d + 1} f)).obj M)) :=
    Finite.of_equiv V (((p.sheafFiberCompIso
      (ModuleCat.restrictScalars.{d + 1} f)).app M).symm.toLinearEquiv.toEquiv)
  rw [ModuleCat.isFinitelyGenerated_iff]
  change Module.Finite (Padic.coefficientExtensionIntegers l L)
    ((p.sheafFiber (A := ModuleCat.{d + 1} (Padic.coefficientExtensionIntegers l L))).obj
      ((sheafCompose Y.smallEtaleTopology (ModuleCat.restrictScalars.{d + 1} f)).obj M))
  exact Module.Finite.of_finite

section StalkRestriction
variable {R S : Type (d + 1)} [CommRing R] [CommRing S]
variable {Ω : Type d} [Field Ω] [IsAlgClosed Ω] (y : Spec (.of Ω) ⟶ Y)
local instance restrictLeftAdjoint (f : R →+* S) :
    (ModuleCat.restrictScalars.{d + 1} f).IsLeftAdjoint :=
  (ModuleCat.restrictCoextendScalarsAdj.{d + 1, d + 1, d + 1} f).isLeftAdjoint
omit [IsNoetherian Y] [Y.IsSeparated] in
private theorem restriction_stalk_kernel
    (f : R →+* S) {M N : Sheaf Y.smallEtaleTopology (ModuleCat.{d + 1} S)}
    (v : M ⟶ N) (I : Ideal R) (J : Ideal S) (hIJ : Ideal.map f I = J)
    (hv : let p := (pointSmallEtale y).ulift.{d + 1}
      let a := (p.sheafFiber.map v).hom
      Function.Surjective a ∧ LinearMap.ker a = J • ⊤) :
    let p := (pointSmallEtale y).ulift.{d + 1}
    let res := sheafCompose Y.smallEtaleTopology (ModuleCat.restrictScalars.{d + 1} f)
    let b := (p.sheafFiber.map (res.map v)).hom
    Function.Surjective b ∧ LinearMap.ker b = I • ⊤ := by
  let _ := f.toAlgebra
  let p := (pointSmallEtale y).ulift.{d + 1}
  let res := ModuleCat.restrictScalars.{d + 1} f
  let H := sheafCompose Y.smallEtaleTopology res
  let η := p.sheafFiberCompIso res
  let eM := (η.app M).toLinearEquiv
  let eN := (η.app N).toLinearEquiv
  let a := (p.sheafFiber.map v).hom
  let b := (p.sheafFiber.map (H.map v)).hom
  have hn (x : ((p.sheafFiber (A := ModuleCat.{d + 1} R)).obj (H.obj M))) : a (eM x) = eN (b x) :=
    (ConcreteCategory.congr_hom (η.hom.naturality v) x).symm
  have hb : Function.Surjective b := by
    intro z
    obtain ⟨x, hx⟩ := hv.1 (eN z)
    refine ⟨eM.symm x, eN.injective ?_⟩
    rw [← hn, LinearEquiv.apply_symm_apply, hx]
  refine ⟨hb, ?_⟩
  let _ : Module R ((p.sheafFiber (A := ModuleCat.{d + 1} S)).obj M) :=
    Module.compHom _ f
  have : IsScalarTower R S ((p.sheafFiber (A := ModuleCat.{d + 1} S)).obj M) :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  have hk : LinearMap.ker b =
      ((LinearMap.ker a).restrictScalars R).comap eM.toLinearMap := by
    ext x
    change b x = 0 ↔ a (eM x) = 0
    rw [hn]
    exact eN.map_eq_zero_iff.symm
  rw [hk, hv.2, ← hIJ]
  have hs : ((Ideal.map f I • (⊤ : Submodule S
      ((p.sheafFiber (A := ModuleCat.{d + 1} S)).obj M))).restrictScalars R) =
      I • (⊤ : Submodule R
        (res.obj ((p.sheafFiber (A := ModuleCat.{d + 1} S)).obj M))) := by
    exact Submodule.restrictScalars_map_smul_eq I ⊤
  rw [hs, Submodule.comap_smul'' eM.injective (by
    rw [LinearMap.range_eq_top.mpr eM.surjective]), Submodule.comap_top]
end StalkRestriction

section Stalks
variable {Ω : Type d} [Field Ω] [IsAlgClosed Ω] (y : Spec (.of Ω) ⟶ Y)

/-- The level ideal kills every geometric stalk, since every stalk element is represented
by a section on which that ideal acts as zero. -/
lemma lisseIntegralStalk_annihilated (F : LisseIntegralSheaf l E Y) (n : ℕ) :
    let R := Padic.coefficientExtensionIntegers l E
    let I := Ideal.span ({Padic.coefficientExtensionUniformizer l E} : Set R)
    I ^ (n + 1) • (⊤ : Submodule R
      ((pointSmallEtale y).ulift.{d + 1}.sheafFiber (A := ModuleCat.{d + 1} R) |>.obj
        (F.obj.obj (op n)))) = ⊥ := by
  let p := (pointSmallEtale y).ulift.{d + 1}
  apply le_antisymm ?_ bot_le
  apply Submodule.smul_le.mpr
  intro r hr z _
  obtain ⟨U, x, s, rfl⟩ := p.toPresheafFiber_jointly_surjective
    (P := (F.obj.obj (op n)).obj) z
  have hz : r • s = 0 := by
    have h := Submodule.smul_mem_smul hr (Submodule.mem_top (x := s))
    rw [F.property.2.1 n U] at h
    exact h
  change r • p.toPresheafFiber U x (F.obj.obj (op n)).obj s = 0
  rw [← map_smul, hz, map_zero]

/-- Arbitrary transition maps are surjective with the expected ideal-multiple kernel.
Induct on the length of the transition, using the adjacent transition condition and
preimages of ideal multiples under a surjective linear map. -/
theorem lisseIntegralStalk_transition (F : LisseIntegralSheaf l E Y)
    (m n : ℕ) (h : m ≤ n) :
    let R := Padic.coefficientExtensionIntegers l E
    let I := Ideal.span ({Padic.coefficientExtensionUniformizer l E} : Set R)
    let T := (pointSmallEtale y).ulift.{d + 1}.sheafFiber (A := ModuleCat.{d + 1} R)
    let v := (T.map (F.obj.map (homOfLE h).op)).hom
    Function.Surjective v ∧ LinearMap.ker v =
      I ^ (m + 1) • (⊤ : Submodule R (T.obj (F.obj.obj (op n)))) := by
  let R := Padic.coefficientExtensionIntegers l E
  let I := Ideal.span ({Padic.coefficientExtensionUniformizer l E} : Set R)
  let T := (pointSmallEtale y).ulift.{d + 1}.sheafFiber (A := ModuleCat.{d + 1} R)
  dsimp only
  induction n, h using Nat.le_induction with
  | base =>
    have he : (homOfLE (le_refl m)).op = 𝟙 (op m) := Subsingleton.elim _ _
    rw [he, F.obj.map_id, T.map_id]
    constructor
    · exact Function.surjective_id
    · exact LinearMap.ker_id.trans
        (lisseIntegralStalk_annihilated (l := l) (E := E) (Y := Y) (y := y) F m).symm
  | succ n h ih =>
    let a := (T.map (F.obj.map (homOfLE (Nat.le_succ n)).op)).hom
    let b := (T.map (F.obj.map (homOfLE h).op)).hom
    have hab : (T.map (F.obj.map (homOfLE (h.trans (Nat.le_succ n))).op)).hom =
        b.comp a := by
      have he : (homOfLE (h.trans (Nat.le_succ n))).op =
          (homOfLE (Nat.le_succ n)).op ≫ (homOfLE h).op := Subsingleton.elim _ _
      rw [he, F.obj.map_comp, T.map_comp]
      rfl
    rw [hab]
    have ha := F.property.2.2 Ω y n
    refine ⟨ih.1.comp ha.1, ?_⟩
    rw [LinearMap.ker_comp, ih.2,
      Submodule.comap_smul_top_of_surjective _ _ ha.1, ha.2]
    exact sup_eq_left.mpr
      (Submodule.smul_mono_left (Ideal.pow_le_pow_right (Nat.succ_le_succ h)))

end Stalks

/-- Reindexing the integral lattice along the ramification-index cofinal subsequence
and restricting coefficients gives a lisse integral system over the smaller field. -/
theorem lisseIntegralRestrictionRaw_isLisse (F : LisseIntegralSheaf l E Y) :
    IsLisseIntegralDiagram l L Y (lisseIntegralRestrictionRaw l Y L E ι F) := by
  refine ⟨restriction_finite_lisse l Y L E ι F,
    restriction_annihilated l Y L E ι F, ?_⟩
  intro Ω _ _ y n
  let e := lisseRamificationIndex l L E ι
  let m := e * (n + 1) - 1
  let k := e * ((n + 1) + 1) - 1
  have he : 0 < e := (lisseRamificationIndex_exists l L E ι).choose_spec.1
  have hp : m + 1 = e * (n + 1) :=
    Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (Nat.ne_of_gt he)
      (Nat.succ_ne_zero n)))
  have hmk : m ≤ k := Nat.sub_le_sub_right
    (Nat.mul_le_mul_left e (Nat.le_succ (n + 1))) 1
  have hm : Ideal.map (lisseIntegerInclusion l L E ι)
      (Padic.coefficientExtensionIdeal l L (n + 1)) =
      Padic.coefficientExtensionIdeal l E (m + 1) := by
    rw [hp]
    dsimp only [Padic.coefficientExtensionIdeal]
    have hr : Ideal.map (lisseIntegerInclusion l L E ι)
        (Padic.coefficientExtensionMaximalIdeal l L) =
        Padic.coefficientExtensionMaximalIdeal l E ^ e :=
      (lisseRamificationIndex_exists l L E ι).choose_spec.2
    rw [Ideal.map_pow, lisseCoherence_uniformizerIdeal_eq l L, hr, ← pow_mul]
    exact congrArg (fun J : Ideal (Padic.coefficientExtensionIntegers l E) ↦
      J ^ (e * (n + 1))) (lisseCoherence_uniformizerIdeal_eq l E).symm
  have hv := lisseIntegralStalk_transition (l := l) (E := E) (Y := Y) (y := y) F m k hmk
  have h := restriction_stalk_kernel Y y (lisseIntegerInclusion l L E ι)
    (F.obj.map (homOfLE hmk).op) (Padic.coefficientExtensionIdeal l L (n + 1))
    (Padic.coefficientExtensionIdeal l E (m + 1)) hm hv
  constructor
  · intro z
    obtain ⟨x, hx⟩ := h.1 z
    exact ⟨x, hx⟩
  · exact h.2

end AlgebraicGeometry.Scheme
