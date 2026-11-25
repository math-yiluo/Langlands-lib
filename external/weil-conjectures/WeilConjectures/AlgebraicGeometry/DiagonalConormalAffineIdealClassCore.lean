/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import WeilConjectures.AlgebraicGeometry.DiagonalConormal
public import Mathlib.RingTheory.Kaehler.Basic
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf
/-! # Affine diagonal tensor chart and kernel sections

Source: Stacks Project, Tags 08S2, 01KJ and 01R3.
(blueprint: stage3-diagonal-conormal-affine-ideal-class-core).
-/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct
namespace AlgebraicGeometry
variable {X S : Scheme.{u}}
/-- Core affine tensor-product ring calculation for the diagonal chart.
(blueprint: stage3-diagonal-conormal-affine-ideal-class-core)
Source: Stacks Project, Tags 08S2, 01KJ.
Proof: Put A = Γ(X,U), R = Γ(S,V), B = A ⊗[R] A, and J = ker μ.
The restricted morphism U → V has affine source and target. Its self-fibre product
embeds as W = p₁⁻¹U ∩ p₂⁻¹U, because equality over S of two points mapping into V
is equality over V. The affine fibre-product construction is Spec B; the two ring
maps are a ↦ a ⊗ 1 and a ↦ 1 ⊗ a. Applying affine global sections gives r and
both projection formulas. The diagonal pulls W back to U and is induced by μ.
The actual kernel sheaf restricts to the kernel of O_W → δ_*O_U: open restriction
preserves kernels and pushforward along δ is computed on inverse images of opens.
On the affine chart this morphism on sections is μ in the coordinates r, so its
sectionwise kernel contains r(j) for every j ∈ J. The universal property of the
module-sheaf kernel supplies the required section s. Empty U gives the zero ring
and zero section modules, and the construction still applies. -/
theorem diagonalConormal_affine_ideal_class_core (f : X ⟶ S)
    (U : X.affineOpens) (V : S.affineOpens) (hUV : U.1 ≤ f ⁻¹ᵁ V.1) :
    letI : Algebra Γ(S, V.1) Γ(X, U.1) := (f.appLE V.1 U.1 hUV).hom.toAlgebra
    let W := (pullback.fst f f) ⁻¹ᵁ U.1 ⊓ (pullback.snd f f) ⁻¹ᵁ U.1
    ∃ r : (Γ(X, U.1) ⊗[Γ(S, V.1)] Γ(X, U.1)) ≃+* Γ(pullback f f, W),
      (∀ a : Γ(X, U.1), r ((1 : Γ(X, U.1)) ⊗ₜ[Γ(S, V.1)] a) =
        (pullback.snd f f).appLE U.1 W inf_le_right a) ∧
      (∀ a : Γ(X, U.1), r (a ⊗ₜ[Γ(S, V.1)] (1 : Γ(X, U.1))) =
        (pullback.fst f f).appLE U.1 W inf_le_left a) ∧
      ∀ j : KaehlerDifferential.ideal Γ(S, V.1) Γ(X, U.1),
        ∃ s : Γ(kernel (SheafOfModules.unitToPushforwardObjUnit
            (pullback.diagonal f).toRingCatSheafHom), W),
          (kernel.ι (SheafOfModules.unitToPushforwardObjUnit
            (pullback.diagonal f).toRingCatSheafHom)).val.app (op W) s = r j := by
  let : Algebra Γ(S, V.1) Γ(X, U.1) := (f.appLE V.1 U.1 hUV).hom.toAlgebra
  let W := (pullback.fst f f) ⁻¹ᵁ U.1 ⊓ (pullback.snd f f) ⁻¹ᵁ U.1
  let H := IsPullback.of_hasPullback f f
  have : IsIso (pushoutSection H hUV hUV (show W = _ from rfl)) :=
    isIso_pushoutSection_of_isAffineOpen H hUV hUV rfl V.2 U.2 U.2
  have hp : IsPushout (f.appLE V.1 U.1 hUV) (f.appLE V.1 U.1 hUV)
      ((pullback.fst f f).appLE U.1 W inf_le_left)
      ((pullback.snd f f).appLE U.1 W inf_le_right) :=
    (isIso_pushoutSection_iff H hUV hUV rfl).mp inferInstance
  let e : CommRingCat.of (Γ(X, U.1) ⊗[Γ(S, V.1)] Γ(X, U.1)) ≅
      Γ(pullback f f, W) :=
    IsColimit.coconePointUniqueUpToIso
      (CommRingCat.pushoutCoconeIsColimit Γ(S, V.1) Γ(X, U.1) Γ(X, U.1)) hp.isColimit
  let r := e.commRingCatIsoToRingEquiv
  have hr₂ (a : Γ(X, U.1)) : r (1 ⊗ₜ[Γ(S, V.1)] a) =
      (pullback.snd f f).appLE U.1 W inf_le_right a := by
    exact ConcreteCategory.congr_hom
      (IsColimit.comp_coconePointUniqueUpToIso_hom
        (CommRingCat.pushoutCoconeIsColimit Γ(S, V.1) Γ(X, U.1) Γ(X, U.1))
        hp.isColimit WalkingSpan.right) a
  have hr₁ (a : Γ(X, U.1)) : r (a ⊗ₜ[Γ(S, V.1)] 1) =
      (pullback.fst f f).appLE U.1 W inf_le_left a := by
    exact ConcreteCategory.congr_hom
      (IsColimit.comp_coconePointUniqueUpToIso_hom
        (CommRingCat.pushoutCoconeIsColimit Γ(S, V.1) Γ(X, U.1) Γ(X, U.1))
        hp.isColimit WalkingSpan.left) a
  refine ⟨r, hr₂, hr₁, ?_⟩
  let δ := pullback.diagonal f
  let φ := SheafOfModules.unitToPushforwardObjUnit δ.toRingCatSheafHom
  have hcomp : (pullback.snd f f).appLE U.1 W inf_le_right ≫ δ.app W =
      (pullback.fst f f).appLE U.1 W inf_le_left ≫ δ.app W := by
    rw [δ.app_eq_appLE, Scheme.Hom.appLE_comp_appLE,
      Scheme.Hom.appLE_comp_appLE]
    simp [δ]
  have hker : KaehlerDifferential.ideal Γ(S, V.1) Γ(X, U.1) ≤
      RingHom.ker ((δ.app W).hom.comp r.toRingHom) := by
    rw [← KaehlerDifferential.span_range_eq_ideal, Ideal.span_le]
    rintro _ ⟨a, rfl⟩
    change δ.app W (r (1 ⊗ₜ[Γ(S, V.1)] a - a ⊗ₜ[Γ(S, V.1)] 1)) = 0
    rw [map_sub, hr₂, hr₁, map_sub]
    exact sub_eq_zero.mpr (ConcreteCategory.congr_hom hcomp a)
  intro j
  have hj : (SheafOfModules.evaluation (pullback f f).ringCatSheaf (op W)).map φ
      (r j) = 0 := by
    change δ.app W (r j) = 0
    exact hker j.property
  have hj' : r j ∈ Set.range
      ((SheafOfModules.evaluation (pullback f f).ringCatSheaf (op W)).map
        (kernel.ι φ)) := by
    rw [Scheme.Modules.range_map_kernelι]
    exact hj
  exact hj'
end AlgebraicGeometry
