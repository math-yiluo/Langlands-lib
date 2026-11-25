/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Pur.PurTwistCoefficientRingsSupplement
public import Mathlib.Topology.ContinuousMap.Algebra
import WeilConjectures.AlgebraicGeometry.Continuous.ContinuousCoefficientCompletionSupplement
import WeilConjectures.Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.NumberTheory.Padics.ProperSpace

/-! Continuous-function coordinates for completed coefficients.
(blueprint: lem-sfb-completed-affine-coefficient-model)
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory Opposite
namespace AlgebraicGeometry.ProEtale.DiagonalCoefficients

/-- A sectionwise continuous-function presentation, compatible with every restriction.
Source: the coefficient-identification step in the docstring of
`completedAffineFree_localDual_detect`.
(blueprint: lem-sfb-completed-affine-coefficient-model) -/
structure CompletedAffineCoefficientModel (l : ℕ) [Fact l.Prime] (X : Scheme.{u}) where
  equiv (V : X.ProEt) :
    (Scheme.purTwistRing X (Scheme.purTwistZlCompletion X l)).obj.obj (op V) ≃+*
      C(V.left, ℤ_[l])
  naturality {V W : X.ProEt} (f : V ⟶ W)
      (a : (Scheme.purTwistRing X (Scheme.purTwistZlCompletion X l)).obj.obj (op W)) :
    equiv V ((Scheme.purTwistRing X (Scheme.purTwistZlCompletion X l)).obj.map f.op a) =
      (equiv W a).comp ⟨f.left, f.left.continuous⟩

private theorem positiveLift_exists (l : ℕ) [Fact l.Prime]
    {T : Type u} [TopologicalSpace T]
    (a : ∀ n : ℕ, C(T, ZMod (l ^ (n + 1))))
    (ha : ∀ n x, ZMod.castHom (pow_dvd_pow l (Nat.le_succ (n + 1)))
      (ZMod (l ^ (n + 1))) (a (n + 1) x) = a n x) :
    ∃ f : C(T, ℤ_[l]), ∀ n x, PadicInt.toZModPow (n + 1) (f x) = a n x := by
  let b (x : T) : ∀ n : ℕ, ZMod (l ^ n) := fun n ↦
    match n with
    | 0 => 0
    | n + 1 => a n x
  have hb (x : T) (n : ℕ) :
      ZMod.castHom (pow_dvd_pow l (Nat.le_add_right n 1)) (ZMod (l ^ n))
        (b x (n + 1)) = b x n := by
    cases n with
    | zero =>
      have : Subsingleton (ZMod (l ^ 0)) := by
        simpa only [pow_zero] using (inferInstance : Subsingleton (ZMod 1))
      exact Subsingleton.elim _ _
    | succ n => exact ha n x
  let f (x : T) := PadicInt.ofCompatible (b x) (hb x)
  have hf (n : ℕ) (x : T) : PadicInt.toZModPow (n + 1) (f x) = a n x :=
    PadicInt.toZModPow_ofCompatible (b x) (hb x) (n + 1)
  let e : ℤ_[l] → ∀ n : ℕ, ZMod (l ^ (n + 1)) :=
    fun z n ↦ PadicInt.toZModPow (n + 1) z
  have he : Continuous e := continuous_pi fun n ↦ PadicInt.continuous_toZModPow (n + 1)
  have hei : Function.Injective e := by
    intro x y h
    apply PadicInt.ext_of_toZModPow.mp
    intro n
    cases n with
    | zero =>
      have : Subsingleton (ZMod (l ^ 0)) := by
        simpa only [pow_zero] using (inferInstance : Subsingleton (ZMod 1))
      exact Subsingleton.elim _ _
    | succ n => exact congrFun h n
  have hemb := (he.isClosedEmbedding hei).isEmbedding
  have hc : Continuous f := hemb.continuous_iff.mpr (by
    apply continuous_pi
    intro n
    simpa only [Function.comp_def, e, hf] using (a n).continuous)
  exact ⟨⟨f, hc⟩, hf⟩

/-- Completed scalar sections are continuous p-adic functions, naturally in the test object.
Source: `CompletedAffineFreeLocalDual.lean`, coefficient-identification step of the
proof of `completedAffineFree_localDual_detect`; finite constant sheaves and sectionwise
limits, Stacks Tags 03CO and 0906.
(blueprint: lem-sfb-completed-affine-coefficient-model)

Proof: identify the constant finite ring sheaf at level n with locally constant
functions into Z/l^(n+1). A locally constant function gives its section by gluing
constant sections on its open level sets; conversely a section is locally constant
by local surjectivity of the constant-sheaf unit. Descent along pro-etale covers
identifies these functions on the underlying scheme. These inverse identifications
commute with restriction and finite reduction. Limits of sheaves are computed
sectionwise. A compatible family of finite functions has a unique Z_l-valued lift,
continuous because the finite reductions generate the p-adic topology. This gives
the ring equivalence and its naturality. Functions on connected components give
the same functions on the scheme by the quotient topology. The empty scheme gives
the zero ring on both sides, so no nonemptiness assumption is needed. -/
theorem completedAffineCoefficientModel_exists (l : ℕ) [Fact l.Prime] (X : Scheme.{u}) :
    Nonempty (CompletedAffineCoefficientModel l X) := by
  classical
  let A := Scheme.continuousCoefficientSheaf X (ULift.{u + 1} ℤ_[l])
  let T (n : ℕ) := CommRingCat.of (ULift.{u + 1} (ZMod (l ^ (n + 1))))
  let : ∀ n : ℕ, TopologicalSpace (T n) := fun _ ↦ ⊥
  let : ∀ n : ℕ, DiscreteTopology (T n) := fun _ ↦ ⟨rfl⟩
  let e := Scheme.discreteContinuousCoefficientIso X
  let red (n : ℕ) : A ⟶ (Scheme.discreteContinuousCoefficientFunctor X).obj (T n) := by
    let : TopologicalSpace (T n) := ⊥
    let : DiscreteTopology (T n) := ⟨rfl⟩
    apply Scheme.continuousCoefficientMap
      (ULift.ringEquiv.symm.toRingHom.comp
        ((PadicInt.toZModPow (n + 1)).comp ULift.ringEquiv.toRingHom))
    have hup : @Continuous (ZMod (l ^ (n + 1))) (T n) _ ⊥ ULift.up :=
      continuous_of_discreteTopology
    exact hup.comp ((PadicInt.continuous_toZModPow (n + 1)).comp continuous_uliftDown)
  let π (n : ℕ) : A ⟶ Scheme.purTwistFiniteRing X l n := red n ≫ e.inv.app (T n)
  have hπ (n : ℕ) : π (n + 1) ≫ Scheme.purTwistFiniteTransition X l n = π n := by
    let t : T (n + 1) ⟶ T n := CommRingCat.ofHom
      (ULift.ringEquiv.symm.toRingHom.comp
        ((ZMod.castHom (pow_dvd_pow l (Nat.le_succ (n + 1)))
          (ZMod (l ^ (n + 1)))).comp ULift.ringEquiv.toRingHom))
    change (red (n + 1) ≫ e.inv.app (T (n + 1))) ≫
      (constantSheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}).map t = _
    rw [Category.assoc, ← e.inv.naturality t, ← Category.assoc]
    congr 1
    ext V f
    apply @ContinuousMap.ext V.unop.left (T n) _ ⊥
    intro x
    apply ULift.ext
    let f' : C(V.unop.left, ULift.{u + 1} ℤ_[l]) := f
    change ZMod.castHom (pow_dvd_pow l (Nat.le_succ (n + 1)))
      (ZMod (l ^ (n + 1))) (PadicInt.toZModPow (n + 1 + 1) (f' x).down) =
        PadicInt.toZModPow (n + 1) (f' x).down
    exact PadicInt.castHom_toZModPow_succ (n + 1) (f' x).down
  let c : Limits.Cone (Scheme.purTwistZlTower X l) :=
    { pt := A
      π := NatTrans.ofOpSequence π (by
        intro n
        change 𝟙 _ ≫ _ = _
        rw [Category.id_comp]
        simpa only [Scheme.purTwistZlTower, Scheme.purTwistZlTowerOfUniverses,
          Functor.ofOpSequence_map_homOfLE_succ] using (hπ n).symm) }
  let Ψ : A ⟶ Scheme.purTwistZlCompletion X l := Limits.limit.lift _ c
  have hΨ (V : X.ProEtᵒᵖ) (n : ℕ) (f : A.obj.obj V) :
      (Scheme.purTwistZlProjection X l n).hom.app V (Ψ.hom.app V f) =
        (π n).hom.app V f := by
    exact congrArg (fun k ↦ k.hom.app V f) (Limits.limit.lift_π c (op n))
  have hext (V : X.ProEtᵒᵖ)
      (a b : (Scheme.purTwistZlCompletion X l).obj.obj V)
      (h : ∀ n, (Scheme.purTwistZlProjection X l n).hom.app V a =
        (Scheme.purTwistZlProjection X l n).hom.app V b) : a = b := by
    apply Limits.Concrete.isLimit_ext _
      (Limits.isLimitOfPreserves ((evaluation _ _).obj V)
        (Limits.isLimitOfPreserves
          (sheafToPresheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1})
            (Limits.limit.isLimit (Scheme.purTwistZlTower X l))))
    intro n
    exact h n.unop
  have hcancel (n : ℕ) (V : X.ProEtᵒᵖ) (v : A.obj.obj V) :
      (e.hom.app (T n)).hom.app V ((π n).hom.app V v) = (red n).hom.app V v := by
    have hh : π n ≫ e.hom.app (T n) = red n := by
      simp only [π, Category.assoc, e.inv_hom_id_app, Category.comp_id]
    exact congrArg (fun k ↦ k.hom.app V v) hh
  have hbij (V : X.ProEtᵒᵖ) : Function.Bijective (Ψ.hom.app V) := by
    constructor
    · intro f g h
      apply ContinuousMap.ext
      intro x
      apply ULift.ext
      apply PadicInt.ext_of_toZModPow.mp
      intro n
      cases n with
      | zero =>
        have : Subsingleton (ZMod (l ^ 0)) := by
          simpa only [pow_zero] using (inferInstance : Subsingleton (ZMod 1))
        exact Subsingleton.elim _ _
      | succ n =>
        have hn := congrArg (fun a ↦ (e.hom.app (T n)).hom.app V
          ((Scheme.purTwistZlProjection X l n).hom.app V a)) h
        rw [hΨ, hΨ] at hn
        have hn' := (hcancel n V f).symm.trans (hn.trans (hcancel n V g))
        exact congrArg (fun a : C(V.unop.left, T n) ↦ (a x).down) hn'
    · intro a
      let r (n : ℕ) : C(V.unop.left, ULift.{u + 1} (ZMod (l ^ (n + 1)))) :=
        (e.hom.app (T n)).hom.app V ((Scheme.purTwistZlProjection X l n).hom.app V a)
      let b (n : ℕ) : C(V.unop.left, ZMod (l ^ (n + 1))) :=
        ⟨fun x ↦ (r n x).down, continuous_of_discreteTopology.comp (r n).continuous⟩
      have hb (n : ℕ) (x : V.unop.left) :
          ZMod.castHom (pow_dvd_pow l (Nat.le_succ (n + 1)))
            (ZMod (l ^ (n + 1))) (b (n + 1) x) = b n x := by
        have hn : Scheme.purTwistZlProjection X l (n + 1) ≫
            Scheme.purTwistFiniteTransition X l n = Scheme.purTwistZlProjection X l n := by
          simpa only [Scheme.purTwistZlProjection, Scheme.purTwistZlProjectionOfUniverses,
            Scheme.purTwistFiniteTransition, Scheme.purTwistZlTower,
            Scheme.purTwistZlTowerOfUniverses, Functor.ofOpSequence_map_homOfLE_succ] using
            (Limits.limit.w (Scheme.purTwistZlTower X l) (homOfLE (Nat.le_succ n)).op)
        let t : T (n + 1) ⟶ T n := CommRingCat.ofHom
          (ULift.ringEquiv.symm.toRingHom.comp
            ((ZMod.castHom (pow_dvd_pow l (Nat.le_succ (n + 1)))
              (ZMod (l ^ (n + 1)))).comp ULift.ringEquiv.toRingHom))
        have hhcat : Scheme.purTwistZlProjection X l (n + 1) ≫
            e.hom.app (T (n + 1)) ≫ (Scheme.discreteContinuousCoefficientFunctor X).map t =
            Scheme.purTwistZlProjection X l n ≫ e.hom.app (T n) := by
          rw [← e.hom.naturality t, ← Category.assoc]
          exact congrArg (fun k ↦ k ≫ e.hom.app (T n)) hn
        have hh := congrArg (fun k ↦ k.hom.app V a) hhcat
        change ((Scheme.discreteContinuousCoefficientFunctor X).map t).hom.app V
          (r (n + 1)) = r n at hh
        exact congrArg (fun k : C(V.unop.left, T n) ↦ (k x).down) hh
      obtain ⟨f, hf⟩ := positiveLift_exists l b hb
      let f' : C(V.unop.left, ULift.{u + 1} ℤ_[l]) :=
        ⟨fun x ↦ ULift.up (f x), continuous_uliftUp.comp f.continuous⟩
      refine ⟨f', hext V _ _ (fun n ↦ ?_)⟩
      rw [hΨ]
      apply (ConcreteCategory.bijective_of_isIso ((e.hom.app (T n)).hom.app V)).injective
      apply (hcancel n V f').trans
      apply @ContinuousMap.ext V.unop.left (T n) _ ⊥
      intro x
      apply ULift.ext
      exact hf n x
  let (V : X.ProEtᵒᵖ) : IsIso (Ψ.hom.app V) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr (hbij V)
  have : IsIso Ψ.hom := NatIso.isIso_of_isIso_app _
  have : IsIso ((sheafToPresheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}).map Ψ) := by
    change IsIso Ψ.hom
    infer_instance
  have : IsIso Ψ := isIso_of_reflects_iso Ψ
    (sheafToPresheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1})
  let i := (asIso Ψ).symm
  let unlift (V : X.ProEt) : C(V.left, ULift.{u + 1} ℤ_[l]) ≃+* C(V.left, ℤ_[l]) :=
    { toFun := fun f ↦ ⟨fun x ↦ (f x).down, continuous_uliftDown.comp f.continuous⟩
      invFun := fun f ↦ ⟨fun x ↦ ULift.up (f x), continuous_uliftUp.comp f.continuous⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      map_mul' := fun _ _ ↦ rfl
      map_add' := fun _ _ ↦ rfl }
  refine ⟨{ equiv := fun V ↦
    ((sheafToPresheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1} |>.mapIso i).app (op V)
      |>.commRingCatIsoToRingEquiv).trans (unlift V), naturality := ?_ }⟩
  intro V W f a
  apply ContinuousMap.ext
  intro x
  exact congrArg (fun k ↦
    ((show C(V.left, ULift.{u + 1} ℤ_[l]) from k a) x).down)
      (i.hom.hom.naturality f.op)

end AlgebraicGeometry.ProEtale.DiagonalCoefficients
