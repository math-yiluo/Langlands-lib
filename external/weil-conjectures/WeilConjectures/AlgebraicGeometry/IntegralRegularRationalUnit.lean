/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.IntegralMatrixAnalyticCover
public import WeilConjectures.AlgebraicGeometry.ContinuousRegularFunctions

import WeilConjectures.AlgebraicGeometry.RegularExtensionComparison

/-! # Rational invertibility of a nowhere-zero integral multiplier -/

@[expose] public section
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory Limits MonObj Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- A nowhere-zero continuous integral multiplier becomes invertible over E.

Source: Bhatt--Scholze, Section 6.8, integral-to-field coefficient extension.
(auxiliary; not a blueprint node)

Proof: realize regular-module maps as multiplication by their continuous coefficient.
Extension from O_E to E sends the regular module to the regular E-module and sends this
map to multiplication by the image of the same coefficient. Its pointwise reciprocal
is continuous because the coefficient is nowhere zero. Multiplication by that reciprocal
is the inverse regular E-module endomorphism. The supplied compatibility square
identifies its composite with the integral coefficient inclusion. The regular-module
scalar-extension isomorphism intertwines the two endomorphisms by the adjunction
universal property, so scalar extension of the original map is also invertible. Neither
a matrix, a dominating entry, nor a rational cokernel hypothesis is used.
Empty schemes give the identity endomorphism of the zero regular module. -/
theorem integralRegular_rationalUnit_of_nowhereZero (ℓ : ℕ) [Fact ℓ.Prime]
    (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E] (X : Scheme.{u})
    (e : condensedRingObj (integralCoeff ℓ E) X ⟶
      (sheafCompose (Scheme.ProEt.topology X) (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj
        (continuousMapRingSheaf X (continuousIntegers ℓ E))) [IsIso e] [IsMonHom e]
    (eE : condensedRingObj (Profinite.continuousMapRingObj E) X ⟶
      continuousAbRing X E) [IsIso eE] [IsMonHom eE]
    (he : coefficientMap (integralScalarMap ℓ E) X ≫ eE =
      e ≫ integralFunctionInclusion ℓ E X)
    (p : Mod.regular (condensedRingObj (integralCoeff ℓ E) X) ⟶
      Mod.regular (condensedRingObj (integralCoeff ℓ E) X))
    (hp : ∀ x, ((((inv e ≫ p.hom ≫ e).hom.app
      (op (Scheme.ProEt.mk (𝟙 X)))) (ULift.up 1)).down x).val ≠ 0) :
    IsIso ((Mod.extendScalars (coefficientMap (integralScalarMap ℓ E) X)).map p) := by
  let R := condensedRingObj (integralCoeff ℓ E) X
  let S := condensedRingObj (Profinite.continuousMapRingObj E) X
  let φ := coefficientMap (integralScalarMap ℓ E) X
  let O := continuousIntegers ℓ E
  let F := (Mod.comapEquivalenceOfIsIso (inv e)).functor
  let jO := Mod.regularIsoOfIsIso e
  let pO := jO.inv ≫ F.map p ≫ jO.hom
  let b := regularCoefficient X O pO
  let c : C(X, E) := ⟨fun x ↦ (b x).val, continuous_subtype_val.comp b.continuous⟩
  let qE := continuousMultiplier X E c
  have hqE : IsIso qE := continuousRegular_field_isIso X E qE (by
    intro x
    rw [regularCoefficient_multiplier]
    exact hp x)
  let G := (Mod.comapEquivalenceOfIsIso (inv eE)).functor
  have : G.IsEquivalence := (Mod.comapEquivalenceOfIsIso (inv eE)).isEquivalence_functor
  let jE := Mod.regularIsoOfIsIso eE
  let q := G.preimage (jE.hom ≫ qE ≫ jE.inv)
  have hGq : G.map q = jE.hom ≫ qE ≫ jE.inv := Functor.map_preimage _ _
  have : IsIso (G.map q) := by rw [hGq]; infer_instance
  have hq : IsIso q := isIso_of_reflects_iso q G
  have hqhom : q.hom ≫ eE = eE ≫ qE.hom := by
    have hh := congrArg (fun z ↦ z.hom) hGq
    change q.hom = eE ≫ qE.hom ≫ inv eE at hh
    rw [hh, Category.assoc, Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  have hpO : p.hom ≫ e = e ≫ pO.hom := by
    change p.hom ≫ e = e ≫ (inv e ≫ p.hom ≫ e)
    simp only [← Category.assoc, IsIso.hom_inv_id, Category.id_comp]
  have hcont : pO.hom ≫ integralFunctionInclusion ℓ E X =
      integralFunctionInclusion ℓ E X ≫ qE.hom := by
    ext U a
    apply ULift.ext
    ext x
    change ((pO.hom.hom.app U a).down x).val =
      (a.down x).val * (b (U.unop.hom x)).val
    rw [continuousRegular_apply]
    rfl
  have hsquare : p.hom ≫ φ = φ ≫ q.hom := by
    apply (cancel_mono eE).1
    calc
      (p.hom ≫ φ) ≫ eE = p.hom ≫ e ≫ integralFunctionInclusion ℓ E X := by
        rw [Category.assoc, he]
      _ = e ≫ pO.hom ≫ integralFunctionInclusion ℓ E X := by
        rw [← Category.assoc, hpO, Category.assoc]
      _ = e ≫ integralFunctionInclusion ℓ E X ≫ qE.hom := by rw [hcont]
      _ = (φ ≫ q.hom) ≫ eE := by
        rw [Category.assoc, hqhom]
        simpa only [Category.assoc] using congrArg (fun z ↦ z ≫ qE.hom) he.symm
  let j := Mod.regularExtensionIso φ
  have hn := Mod.regularExtensionIso_naturality φ p q hsquare
  have hh : (Mod.extendScalars φ).map p = j.hom ≫ q ≫ j.inv := by
    apply (cancel_mono j.hom).1
    simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using hn
  rw [hh]
  infer_instance

end AlgebraicGeometry.ProEtale.CondensedRing
