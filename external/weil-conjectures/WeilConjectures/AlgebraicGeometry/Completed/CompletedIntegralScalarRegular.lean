/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.CompletedIntegralConstantMapOfUniverses
public import WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientGerm
import all WeilConjectures.AlgebraicGeometry.Completed.CompletedIntegralProjectionDivisibility
import Mathlib.CategoryTheory.Sites.LeftExact
import Mathlib.CategoryTheory.Types.Basic

/-! # Uniformizer regularity on completed integral coefficients

(blueprint: lem-pod-completed-integral-scalar-regular) -/
@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe t u z w v
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale
open WeilConjectures

private theorem ct_ulift_mul {C : Type w} [Category.{v} C]
    (J : GrothendieckTopology C)
    [HasSheafify J CommRingCat.{max u (t + 1)}]
    [HasSheafify J (Type (max u (t + 1)))]
    [J.PreservesSheafification (forget CommRingCat.{max u (t + 1)})]
    [J.HasSheafCompose (forget CommRingCat.{max u (t + 1)})]
    (A : Type u) [CommRing A] (b : A) (U : Cᵒᵖ)
    (x : (sheafify J ((Functor.const Cᵒᵖ).obj
      (CommRingCat.of (ULift.{t + 1} A)))).obj U) :
    (ce J (CommRingCat.of (ULift.{t + 1} A))).hom.app U
      ((uliftFunctor.{t + 1} ⋙ ct J U).map (TypeCat.ofHom (fun a : A ↦ b * a))
        ((ce J (CommRingCat.of (ULift.{t + 1} A))).inv.app U x)) =
      (toSheafify J ((Functor.const Cᵒᵖ).obj
        (CommRingCat.of (ULift.{t + 1} A)))).app U (ULift.up b) * x := by
  let B := CommRingCat.of (ULift.{t + 1} A)
  have h := ct_mul J (𝟙 B) (ULift.up b : B) U x
  have hid : sheafifyMap J ((Functor.const Cᵒᵖ).map (𝟙 B)) = 𝟙 _ := by
    change (presheafToSheaf J CommRingCat.{max u (t + 1)} ⋙ sheafToPresheaf J _).map
      ((Functor.const Cᵒᵖ).map (𝟙 B)) = _
    simp
  rw [hid] at h
  exact h

private theorem family_regular {A : Type u} [CommRing A] [IsDomain A]
    (π : A) (hπ : π ≠ 0) (m : ℕ)
    (F : Type u ⥤ Type z) [PreservesFiniteLimits F]
    (x y : ∀ k : ℕ, F.obj (A ⧸ Ideal.span {π} ^ (k + 1)))
    (hx : ∀ (i j : ℕ) (h : i ≤ j),
      F.map (TypeCat.ofHom (Ideal.Quotient.factorPow (Ideal.span {π})
        (Nat.add_le_add_right h 1))) (x j) = x i)
    (hy : ∀ (i j : ℕ) (h : i ≤ j),
      F.map (TypeCat.ofHom (Ideal.Quotient.factorPow (Ideal.span {π})
        (Nat.add_le_add_right h 1))) (y j) = y i)
    (hxy : ∀ k : ℕ, F.map (TypeCat.ofHom
        (fun a : A ⧸ Ideal.span {π} ^ (k + 1) ↦
          Ideal.Quotient.mk _ (π ^ m) * a)) (x k) =
      F.map (TypeCat.ofHom
        (fun a : A ⧸ Ideal.span {π} ^ (k + 1) ↦
          Ideal.Quotient.mk _ (π ^ m) * a)) (y k)) : x = y := by
  funext k
  have hi : Function.Injective (F.map (TypeCat.ofHom (qm π m (k + 1)))) := by
    have : Mono (TypeCat.ofHom (qm π m (k + 1))) :=
      (CategoryTheory.mono_iff_injective _).2 (qm_inj π hπ _ _)
    exact (CategoryTheory.mono_iff_injective _).1 (F.map_mono _)
  apply hi
  let q := Ideal.Quotient.factorPow (Ideal.span {π})
    (show k + 1 ≤ m + k + 1 by omega)
  have he : TypeCat.ofHom q ≫ TypeCat.ofHom (qm π m (k + 1)) =
      TypeCat.ofHom (fun a : A ⧸ Ideal.span {π} ^ (m + k + 1) ↦
        Ideal.Quotient.mk _ (π ^ m) * a) := by
    ext a
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    change qm π m (k + 1) (Ideal.Quotient.mk _ a) = _
    rw [qm_mk]
    exact map_mul (Ideal.Quotient.mk _) (π ^ m) a
  rw [← hx k (m + k) (by omega), ← hy k (m + k) (by omega)]
  change (F.map (TypeCat.ofHom q) ≫ F.map (TypeCat.ofHom (qm π m (k + 1)))) _ =
    (F.map (TypeCat.ofHom q) ≫ F.map (TypeCat.ofHom (qm π m (k + 1)))) _
  rw [← F.map_comp, he]
  exact hxy (m + k)

/-- Powers of the constant uniformizer act injectively on the completed coefficient sheaf.

Proof: at each finite level r, multiplication by pi^m identifies O/(pi^r) with its
image in O/(pi^(m+r)). Constant sheafification and evaluation preserve this injection.
For two completed sections with equal products by pi^m, their projections at level m+r
therefore give equal projections at level r. The inverse-limit projections jointly detect
equality. This argument works for every site object, including the empty object, and for
m=0; it never interchanges sheafification and an infinite limit.
Source: Stacks Tags 093J--093M; original blueprint step 1.
(blueprint: lem-pod-completed-integral-scalar-regular) -/
theorem completedIntegralScalar_regular
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (T : Scheme.{t})
    (m : ℕ) (U : T.ProEtᵒᵖ) :
    Function.Injective (fun x : (completedIntegralCoefficientSheafUnrestricted l E T).obj.obj U ↦
      ((integralConstantToCompletionOfUniverses l E T).hom.app U
        ((toSheafify (Scheme.ProEt.topology T)
          ((Functor.const T.ProEtᵒᵖ).obj
            (CommRingCat.of (ULift.{t + 1} (Padic.coefficientExtensionIntegers l E))))).app U
              (ULift.up (Padic.coefficientExtensionUniformizer l E)))) ^ m * x) := by
  have : LocallySmall.{max u (t + 1)} T.ProEt := locallySmall_max.{max u (t + 1), t, t + 1}
  let J := Scheme.ProEt.topology T
  have : HasColimitsOfSize.{t + 1, t + 1} CommRingCat.{max u (t + 1)} :=
    hasColimitsOfSizeShrink.{t + 1, t + 1, max u (t + 1), max u (t + 1)} _
  have : PreservesFilteredColimitsOfSize.{t + 1, t + 1} (forget CommRingCat.{max u (t + 1)}) :=
    preservesFilteredColimitsOfSize_shrink.{t + 1, max u (t + 1), t + 1, max u (t + 1)} _
  have : J.PreservesSheafification (forget CommRingCat.{max u (t + 1)}) :=
    GrothendieckTopology.instPreservesSheafification J _
  let O := Padic.coefficientExtensionIntegers l E
  let π := Padic.coefficientExtensionUniformizer l E
  let F : Type u ⥤ Type (max u (t + 1)) := uliftFunctor.{t + 1} ⋙ ct J U
  have : PreservesFiniteLimits F := by dsimp [F, ct]; infer_instance
  let B (k : ℕ) := CommRingCat.of (ULift.{t + 1} (O ⧸ Ideal.span {π} ^ (k + 1)))
  let p (k : ℕ) := (limit.π (integralCoefficientSheafSystem l E T) (op k)).hom.app U
  let s := (integralConstantToCompletionOfUniverses l E T).hom.app U
    ((toSheafify J ((Functor.const T.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{t + 1} O)))).app U
      (ULift.up π))
  have hs (k : ℕ) : p k s =
      (toSheafify J ((Functor.const T.ProEtᵒᵖ).obj (B k))).app U
        (ULift.up (Ideal.Quotient.mk _ π)) := by
    have hc := congrArg (fun h ↦ h.hom.app U
      ((toSheafify J ((Functor.const T.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{t + 1} O)))).app U
        (ULift.up π)))
      (limit.lift_π (integralConstantConeOfUniverses l E T) (op k))
    let φ : CommRingCat.of (ULift.{t + 1} O) ⟶ B k := CommRingCat.ofHom
      (RingHom.ulift (Ideal.Quotient.mk (Ideal.span {π} ^ (k + 1))))
    have hn := congrArg (fun h ↦ h.app U (ULift.up π))
      (toSheafify_naturality J ((Functor.const T.ProEtᵒᵖ).map φ))
    exact hc.trans hn.symm
  intro x y hxy
  let ev : Sheaf J RingCat.{max u (t + 1)} ⥤ Type (max u (t + 1)) :=
    sheafToPresheaf J RingCat.{max u (t + 1)} ⋙
      (evaluation T.ProEtᵒᵖ RingCat.{max u (t + 1)}).obj U ⋙ forget RingCat
  let e := Types.isLimitEquivSections
    (isLimitOfPreserves ev (limit.isLimit (integralCoefficientSheafSystem l E T)))
  apply e.injective
  apply Subtype.ext
  funext k
  change p k.unop x = p k.unop y
  let xx (x : (completedIntegralCoefficientSheafUnrestricted l E T).obj.obj U)
      (k : ℕ) := (ce J (B k)).inv.app U (p k x)
  have hx (x : (completedIntegralCoefficientSheafUnrestricted l E T).obj.obj U)
      (i j : ℕ) (hij : i ≤ j) :
      F.map (TypeCat.ofHom (Ideal.Quotient.factorPow (Ideal.span {π})
        (Nat.add_le_add_right hij 1))) (xx x j) = xx x i := by
    apply ce_injective J (B i) U
    rw [ce_inv]
    have hw := congrArg (fun h ↦ h.hom.app U x)
      (limit.w (integralCoefficientSheafSystem l E T) (homOfLE hij).op)
    rw [coefficientTower_map] at hw
    exact (ct_map J ((quotientTower.{t, u} l E).map (homOfLE hij).op) U
      (p j x)).trans hw
  have hm (k : ℕ) : F.map (TypeCat.ofHom
        (fun a : O ⧸ Ideal.span {π} ^ (k + 1) ↦
          Ideal.Quotient.mk _ (π ^ m) * a)) (xx x k) =
      F.map (TypeCat.ofHom
        (fun a : O ⧸ Ideal.span {π} ^ (k + 1) ↦
          Ideal.Quotient.mk _ (π ^ m) * a)) (xx y k) := by
    apply ce_injective J (B k) U
    erw [ct_ulift_mul J (O ⧸ Ideal.span {π} ^ (k + 1))
      (Ideal.Quotient.mk _ (π ^ m)) U (p k x),
      ct_ulift_mul J (O ⧸ Ideal.span {π} ^ (k + 1))
        (Ideal.Quotient.mk _ (π ^ m)) U (p k y)]
    have hh := congrArg (p k) hxy
    change p k (s ^ m * x) = p k (s ^ m * y) at hh
    rw [map_mul, map_mul, map_pow, hs] at hh
    have hp : (toSheafify J ((Functor.const T.ProEtᵒᵖ).obj (B k))).app U
          (ULift.up (Ideal.Quotient.mk _ (π ^ m))) =
        ((toSheafify J ((Functor.const T.ProEtᵒᵖ).obj (B k))).app U
          (ULift.up (Ideal.Quotient.mk _ π))) ^ m := by
      rw [← map_pow]
      exact congrArg ((toSheafify J ((Functor.const T.ProEtᵒᵖ).obj (B k))).app U)
        (ULift.ext (map_pow (Ideal.Quotient.mk _) π m))
    rw [hp]
    exact hh
  have he := family_regular π (uniformizer_ne_zero l E) m F (xx x) (xx y) (hx x) (hx y) hm
  have hh := congrArg ((ce J (B k.unop)).hom.app U) (congrFun he k.unop)
  exact (ce_inv J (B k.unop) U (p k.unop x)).symm.trans
    (hh.trans (ce_inv J (B k.unop) U (p k.unop y)))

end AlgebraicGeometry.ProEtale
