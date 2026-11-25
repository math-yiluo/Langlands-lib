/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import WeilConjectures.AlgebraicGeometry.DiagonalConormal
public import WeilConjectures.AlgebraicGeometry.TensorPullbackAdjunction
public import Mathlib.RingTheory.Kaehler.Basic
import WeilConjectures.AlgebraicGeometry.AffineOpenKernelConormalSections
import Mathlib.AlgebraicGeometry.PullbackCarrier
/-! # Affine diagonal cotangent comparison

Source: Stacks Project, Tags 08S2, 01KJ and 01R3.
(blueprint: stage3-diagonal-conormal-affine-ideal-class-q).
-/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct
namespace AlgebraicGeometry
variable {X S : Scheme.{u}}
-- The chart and scalar-action transports elaborate several nested sheaf module instances.
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Affine diagonal cotangent equivalence and unit formula, assuming tensor coordinates.
(blueprint: stage3-diagonal-conormal-affine-ideal-class-q)
Source: Stacks Project, Tags 08S2, 01KJ, 01R3.
Proof: Put A = Γ(X,U), R = Γ(S,V), B = A ⊗[R] A and J = ker μ.
The two projection formulas determine r on pure tensors, hence on B. They identify
the restricted diagonal U → W with Spec μ, a closed immersion since μ is onto.
Restriction to W preserves the actual module-sheaf kernel, and identifies it with
the closed immersion ideal module J. Inverse image of sheaves commutes with open
restriction, as does extension of scalars: both are the same inverse-image sheaf
followed by sheafification of the sectionwise tensor product. Their canonical units
restrict compatibly, since inverse-image unit followed by 1 ⊗ s is unchanged by
restriction and its sheafification unit is natural. Apply
Scheme.Modules.affine_conormal_sections_existence to this restricted closed
immersion. It gives an equivalence J/J² with the conormal sections, sending the
class of j to the restricted unit of any section s whose inclusion is r(j).
The B-action on J/J² factors through B/J, because every product of two
elements of J vanishes in J/J². Multiplication identifies B/J with A and sends
a ⊗ 1 to a. Thus the transported equivalence is A-linear for the first-factor action.
Mathlib's KaehlerDifferential R A is exactly J.Cotangent = J/J².
This yields e with the displayed formula. Any proof hδ gives the same restriction
map by proof irrelevance. The zero-ring chart obeys the same quotient calculation. -/
theorem diagonalConormal_affine_ideal_class_q (f : X ⟶ S)
    (U : X.affineOpens) (V : S.affineOpens) (hUV : U.1 ≤ f ⁻¹ᵁ V.1)
    : letI : Algebra Γ(S, V.1) Γ(X, U.1) :=
        (f.appLE V.1 U.1 hUV).hom.toAlgebra
      let W := (pullback.fst f f) ⁻¹ᵁ U.1 ⊓ (pullback.snd f f) ⁻¹ᵁ U.1
      ∀ (r : (Γ(X, U.1) ⊗[Γ(S, V.1)] Γ(X, U.1)) ≃+* Γ(pullback f f, W)),
        (∀ a : Γ(X, U.1), r ((1 : Γ(X, U.1)) ⊗ₜ[Γ(S, V.1)] a) =
          (pullback.snd f f).appLE U.1 W inf_le_right a) →
        (∀ a : Γ(X, U.1), r (a ⊗ₜ[Γ(S, V.1)] (1 : Γ(X, U.1))) =
          (pullback.fst f f).appLE U.1 W inf_le_left a) →
        ∃ e : KaehlerDifferential Γ(S, V.1) Γ(X, U.1) ≃ₗ[Γ(X, U.1)]
            Γ(diagonalConormal f, U.1),
          ∀ (hδ : U.1 ≤ (pullback.diagonal f) ⁻¹ᵁ W)
            (j : KaehlerDifferential.ideal Γ(S, V.1) Γ(X, U.1))
            (s : Γ(kernel (SheafOfModules.unitToPushforwardObjUnit
              (pullback.diagonal f).toRingCatSheafHom), W)),
            (kernel.ι (SheafOfModules.unitToPushforwardObjUnit
              (pullback.diagonal f).toRingCatSheafHom)).val.app (op W) s = r j →
            e (KaehlerDifferential.fromIdeal Γ(S, V.1) Γ(X, U.1) j) =
              (diagonalConormal f).presheaf.map (homOfLE hδ).op
                (((Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction
                  (pullback.diagonal f))).unit.app
                    (kernel (SheafOfModules.unitToPushforwardObjUnit
                      (pullback.diagonal f).toRingCatSheafHom))).val.app (op W) s) := by
  classical
  dsimp only
  let : Algebra Γ(S, V.1) Γ(X, U.1) := (f.appLE V.1 U.1 hUV).hom.toAlgebra
  let W := (pullback.fst f f) ⁻¹ᵁ U.1 ⊓ (pullback.snd f f) ⁻¹ᵁ U.1
  intro r hright hleft
  have hpre : (pullback.diagonal f) ⁻¹ᵁ W = U.1 := by
    simp only [W, Scheme.Hom.preimage_inf, ← Scheme.Hom.comp_preimage,
      pullback.diagonal_fst, pullback.diagonal_snd, Scheme.Hom.id_preimage, inf_idem]
  have hδ : U.1 ≤ (pullback.diagonal f) ⁻¹ᵁ W := hpre.ge
  have hW : IsAffineOpen W := by
    let g := f.resLE V.1 U.1 hUV
    let m := pullback.map g g f f U.1.ι U.1.ι V.1.ι
      (f.resLE_comp_ι hUV) (f.resLE_comp_ι hUV)
    have : IsAffine U.1.toScheme := U.2
    have : IsAffine V.1.toScheme := V.2
    have : IsOpenImmersion m :=
      Scheme.pullback_map_isOpenImmersion ..
    have hm : W = m.opensRange := by
      apply TopologicalSpace.Opens.ext
      rw [Scheme.Hom.coe_opensRange, Scheme.Pullback.range_map]
      simp only [Scheme.Opens.range_ι]
      rfl
    rw [hm]
    exact isAffineOpen_opensRange m
  have hp₁ (a : Γ(X, U.1)) :
      (pullback.diagonal f).appLE W U.1 hδ
        ((pullback.fst f f).appLE U.1 W inf_le_left a) = a := by
    have h := Scheme.Hom.appLE_comp_appLE (pullback.diagonal f)
      (pullback.fst f f) U.1 W U.1 inf_le_left hδ
    simp only [pullback.diagonal_fst] at h
    have hid : Scheme.Hom.appLE (𝟙 X) U.1 U.1 (by simp) = 𝟙 Γ(X, U.1) := by
      simp only [Scheme.Hom.appLE, Scheme.Hom.id_app, Scheme.Hom.id_preimage,
        homOfLE_refl, op_id, Category.id_comp]
      exact X.presheaf.map_id _
    rw [hid] at h
    exact congrArg (fun q ↦ q a) h
  have hp₂ (a : Γ(X, U.1)) :
      (pullback.diagonal f).appLE W U.1 hδ
        ((pullback.snd f f).appLE U.1 W inf_le_right a) = a := by
    have h := Scheme.Hom.appLE_comp_appLE (pullback.diagonal f)
      (pullback.snd f f) U.1 W U.1 inf_le_right hδ
    simp only [pullback.diagonal_snd] at h
    have hid : Scheme.Hom.appLE (𝟙 X) U.1 U.1 (by simp) = 𝟙 Γ(X, U.1) := by
      simp only [Scheme.Hom.appLE, Scheme.Hom.id_app, Scheme.Hom.id_preimage,
        homOfLE_refl, op_id, Category.id_comp]
      exact X.presheaf.map_id _
    rw [hid] at h
    exact congrArg (fun q ↦ q a) h
  have hmul : ((pullback.diagonal f).appLE W U.1 hδ).hom.comp r.toRingHom =
      (Algebra.TensorProduct.lmul' Γ(S, V.1) :
        Γ(X, U.1) ⊗[Γ(S, V.1)] Γ(X, U.1) →ₐ[Γ(S, V.1)] Γ(X, U.1)).toRingHom := by
    apply RingHom.ext
    intro t
    induction t using TensorProduct.inductionOn with
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul a b =>
      change (pullback.diagonal f).appLE W U.1 hδ (r (a ⊗ₜ[Γ(S, V.1)] b)) = a * b
      rw [show a ⊗ₜ[Γ(S, V.1)] b =
        (a ⊗ₜ[Γ(S, V.1)] (1 : Γ(X, U.1))) *
          ((1 : Γ(X, U.1)) ⊗ₜ[Γ(S, V.1)] b) by simp]
      rw [map_mul, hleft, hright, map_mul, hp₁, hp₂]
  have hsurj : Function.Surjective
      (((pullback.diagonal f).appLE W U.1 hδ).hom.comp r.toRingHom) := by
    intro a
    refine ⟨a ⊗ₜ[Γ(S, V.1)] (1 : Γ(X, U.1)), ?_⟩
    change (pullback.diagonal f).appLE W U.1 hδ (r _) = a
    rw [hleft, hp₁]
  let : Module (Γ(X, U.1) ⊗[Γ(S, V.1)] Γ(X, U.1))
      Γ((Scheme.Modules.tensorPullback (pullback.diagonal f)).obj
        (kernel (SheafOfModules.unitToPushforwardObjUnit
          (pullback.diagonal f).toRingCatSheafHom)), U.1) := Module.compHom _
        (((pullback.diagonal f).appLE W U.1 hδ).hom.comp r.toRingHom)
  obtain ⟨e, he⟩ := Scheme.Modules.affineOpen_kernel_conormal_sections
    (pullback.diagonal f) ⟨W, hW⟩ U hδ hpre
    (Γ(X, U.1) ⊗[Γ(S, V.1)] Γ(X, U.1)) r
    (KaehlerDifferential.ideal Γ(S, V.1) Γ(X, U.1))
    (by rw [hmul]; rfl) hsurj
  dsimp only at e he
  let eA : KaehlerDifferential Γ(S, V.1) Γ(X, U.1) ≃ₗ[Γ(X, U.1)]
      Γ(diagonalConormal f, U.1) :=
    { e.toAddEquiv with
      map_smul' := by
        intro a x
        change e (a • x) = a • e x
        refine (congrArg e (IsScalarTower.algebraMap_smul
          (Γ(X, U.1) ⊗[Γ(S, V.1)] Γ(X, U.1)) a x).symm).trans ?_
        refine (e.map_smul (algebraMap Γ(X, U.1) _ a) x).trans ?_
        change (((pullback.diagonal f).appLE W U.1 hδ).hom.comp r.toRingHom)
          (algebraMap Γ(X, U.1) _ a) • e x = a • e x
        have ha : (((pullback.diagonal f).appLE W U.1 hδ).hom.comp r.toRingHom)
            (algebraMap Γ(X, U.1) (Γ(X, U.1) ⊗[Γ(S, V.1)] Γ(X, U.1)) a) = a := by
          rw [hmul]
          simp [Algebra.TensorProduct.algebraMap_apply]
        exact congrArg (fun b : Γ(X, U.1) ↦ b • e x) ha }
  refine ⟨eA, ?_⟩
  intro h j s hs
  change e ((KaehlerDifferential.ideal Γ(S, V.1) Γ(X, U.1)).toCotangent j) = _
  exact he j s hs
end AlgebraicGeometry
