/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.AlgebraicGeometry.RelativeProj.BaseChange
public import WeilConjectures.AlgebraicGeometry.RelativeProj.Rees
public import WeilConjectures.Blowup.InvertibleCenter
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Affine

/-!
# Flat base change of blow-ups

Let `g : Y ⟶ X` be a flat morphism and `I` a quasi-coherent ideal sheaf on `X`. Then the Rees
algebra of the pulled-back ideal `I·𝒪_Y` is the coefficientwise pullback of the Rees algebra of
`I`, since `g^*(Iⁿ) ≅ (I·𝒪_Y)ⁿ` for flat `g`. Taking relative `Proj` gives the flat base change
isomorphism `Bl_{I·𝒪_Y}(Y) ≅ Y ×_X Bl_I(X)` over `Y`.

## Main definitions and results

- `Ideal.injective_liftBaseChange_pow_of_flat`, `Ideal.range_liftBaseChange_pow`: for a flat
  ring map `A → B`, the map `B ⊗_A Iⁿ → B` is injective with image `(IB)ⁿ`.
- `AlgebraicGeometry.Scheme.IdealSheafData.reesPullbackData`: the comparison
  `β_g : g^* ℛ_X(I) → ℛ_Y(I·𝒪_Y)` of Rees algebras, a coefficientwise base change.
- `AlgebraicGeometry.Scheme.IdealSheafData.blowupFlatBaseChangeIso`: the flat base change
  isomorphism `Bl_{I·𝒪_Y}(Y) ≅ Y ×_X Bl_I(X)`.
- `AlgebraicGeometry.Scheme.IdealSheafData.isIso_relProjHom_reesData_of_isInvertible`: the
  relative `Proj` of the Rees algebra of an invertible ideal is the base itself.
-/

@[expose] public section

universe u

open CategoryTheory Limits TensorProduct

namespace Ideal

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B] (I : Ideal A) (n : ℕ)

/-- The `B`-linear map `B ⊗_A Iⁿ → B`, `b ⊗ x ↦ b·x̄`, whose image is `(IB)ⁿ`. -/
noncomputable abbrev powLiftBaseChange : B ⊗[A] ↥(I ^ n) →ₗ[B] B :=
  ((Algebra.linearMap A B).comp (I ^ n).subtype).liftBaseChange B

/-- **The image of `B ⊗_A Iⁿ → B` is `(IB)ⁿ`.** This holds for any ring map `A → B`.
(blueprint: `lemma-products-composites-u-admissible-blow--3`) -/
theorem range_powLiftBaseChange :
    LinearMap.range (powLiftBaseChange (B := B) I n) =
      ((I.map (algebraMap A B)) ^ n).restrictScalars B := by
  apply le_antisymm
  · rintro _ ⟨z, rfl⟩
    induction z using TensorProduct.inductionOn with
    | tmul b x =>
      simp only [LinearMap.liftBaseChange_tmul, LinearMap.coe_comp, Function.comp_apply,
        Submodule.coe_subtype, Algebra.linearMap_apply, smul_eq_mul,
        Submodule.restrictScalars_mem]
      rw [← Ideal.map_pow]
      exact Ideal.mul_mem_left _ b (Ideal.mem_map_of_mem _ x.2)
    | add z z' hz hz' => rw [map_add]; exact add_mem hz hz'
  · intro y hy
    rw [Submodule.restrictScalars_mem, ← Ideal.map_pow] at hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨x, hx, rfl⟩ := hy
      exact ⟨1 ⊗ₜ ⟨x, hx⟩, by simp⟩
    | zero => exact zero_mem _
    | add y y' _ _ hy hy' => exact add_mem hy hy'
    | smul c y _ hy => exact Submodule.smul_mem _ c hy

/-- **For a flat ring map `A → B`, the map `B ⊗_A Iⁿ → B` is injective**, so that
`B ⊗_A Iⁿ ≅ (IB)ⁿ`. (blueprint: `lemma-products-composites-u-admissible-blow--3`) -/
theorem injective_powLiftBaseChange_of_flat [Module.Flat A B] :
    Function.Injective (powLiftBaseChange (B := B) I n) := by
  have h1 := Module.Flat.lTensor_preserves_injective_linearMap (M := B) ((I ^ n).subtype)
    Subtype.val_injective
  have e : ∀ x, powLiftBaseChange (B := B) I n x =
      Algebra.TensorProduct.rid A B B ((I ^ n).subtype.lTensor B x) := by
    intro x
    induction x using TensorProduct.inductionOn with
    | tmul b y => simp [Algebra.smul_def, mul_comm]
    | add x y hx hy => simp only [map_add, hx, hy]
  intro x y hxy
  rw [e, e] at hxy
  exact h1 ((Algebra.TensorProduct.rid A B B).injective hxy)

end Ideal

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X Y : Scheme.{u}} (I : X.IdealSheafData) (g : Y ⟶ X)

lemma map_ideal_appLE {U : X.affineOpens} {U' : Y.affineOpens} (h : U'.1 ≤ g ⁻¹ᵁ U.1) :
    (I.ideal U).map (g.appLE U.1 U'.1 h).hom = (I.comap g).ideal U' :=
  (ideal_comap_appLE I g U U' h).symm

/-- The map of Rees algebras `ℛ(I(U)) → ℛ((I·𝒪_Y)(U'))` induced by `Γ(X, U) → Γ(Y, U')` for
affine opens `U' ⊆ g⁻¹ U`. -/
noncomputable def reesPullbackMap {U : X.affineOpens} {U' : Y.affineOpens}
    (h : U'.1 ≤ g ⁻¹ᵁ U.1) : reesGrading (I.ideal U) →+*ᵍ reesGrading ((I.comap g).ideal U') :=
  reesGrading.hom (g.appLE U.1 U'.1 h).hom (I.map_ideal_appLE g h)

lemma res_reesPullbackMap {U' V' : Y.affineOpens} {U : X.affineOpens} (h' : U' ≤ V')
    (h : V'.1 ≤ g ⁻¹ᵁ U.1) (x : reesAlgebra (I.ideal U)) :
    reesGrading.hom (Y.presheaf.map (homOfLE (X := Y.Opens) h').op).hom
        ((I.comap g).map_ideal h') (I.reesPullbackMap g h x) =
      I.reesPullbackMap g ((show U'.1 ≤ V'.1 from h').trans h) x := by
  rw [reesPullbackMap, reesPullbackMap, ← GradedRingHom.comp_apply, reesGrading.hom_comp]
  exact DFunLike.congr_fun (reesGrading.hom_congr (by
    rw [← CommRingCat.hom_comp, Scheme.Hom.appLE_map]) _) x

lemma reesPullbackMap_res {U' : Y.affineOpens} {U V : X.affineOpens} (h : U'.1 ≤ g ⁻¹ᵁ U.1)
    (hUV : U ≤ V) (x : reesAlgebra (I.ideal V)) :
    I.reesPullbackMap g h
        (reesGrading.hom (X.presheaf.map (homOfLE (X := X.Opens) hUV).op).hom (I.map_ideal hUV) x) =
      I.reesPullbackMap g (h.trans (g.preimage_mono hUV)) x := by
  rw [reesPullbackMap, reesPullbackMap, ← GradedRingHom.comp_apply, reesGrading.hom_comp]
  exact DFunLike.congr_fun (reesGrading.hom_congr (by
    rw [← CommRingCat.hom_comp, Scheme.Hom.map_appLE]) _) x

/-- **The comparison `β_g : g^* ℛ_X(I) → ℛ_Y(I·𝒪_Y)` of Rees algebras** along a flat morphism
`g : Y ⟶ X`: over affine opens `U' ⊆ g⁻¹ U` it is the map of Rees algebras induced by
`Γ(X, U) → Γ(Y, U')`, and it is a coefficientwise base change, i.e. a graded isomorphism
`g^* ℛ_X(I) ≅ ℛ_Y(I·𝒪_Y)`, since `Γ(Y, U') ⊗ Iⁿ(U) ≅ (I·𝒪_Y)ⁿ(U')` for flat `g`
(`reesGrading.isGradedBaseChangeAlong_hom`).
(blueprint: `lemma-products-composites-u-admissible-blow--3`) -/
noncomputable def reesPullbackData [Flat g] :
    GradedAlgebraData.PullbackData g I.reesData (I.comap g).reesData where
  map h := I.reesPullbackMap g h
  isGradedBaseChangeAlong {U' U} h :=
    reesGrading.isGradedBaseChangeAlong_hom (g.appLE U.1 U'.1 h).hom
      (HasRingHomProperty.appLE (P := @Flat) g inferInstance U U' h) (I.map_ideal_appLE g h)
  res_map h' h x := I.res_reesPullbackMap g h' h x
  map_res h hUV x := I.reesPullbackMap_res g h hUV x

variable [Flat g]

/-- **The flat base change comparison of blow-ups** `bc_g : Bl_{I·𝒪_Y}(Y) ⟶ Y ×_X Bl_I(X)`,
obtained by applying relative `Proj` to `β_g` affine-locally and gluing.
(blueprint: `lemma-products-composites-u-admissible-blow--3`) -/
noncomputable def blowupFlatBaseChange : (I.comap g).blowup ⟶ pullback I.blowupMap g :=
  (I.comap g).relProjReesIso.inv ≫ (I.reesPullbackData g).relProjIsoPullback.hom ≫
    pullback.map _ _ _ _ I.relProjReesIso.hom (𝟙 _) (𝟙 _) (by simp) (by simp)

instance : IsIso (I.blowupFlatBaseChange g) := by
  unfold blowupFlatBaseChange
  infer_instance

/-- **Flat base change of blow-ups**: for a flat morphism `g : Y ⟶ X` the comparison
`bc_g : Bl_{I·𝒪_Y}(Y) ≅ Y ×_X Bl_I(X)` is an isomorphism over `Y`.
(blueprint: `lemma-products-composites-u-admissible-blow--3`) -/
noncomputable def blowupFlatBaseChangeIso : (I.comap g).blowup ≅ pullback I.blowupMap g :=
  asIso (I.blowupFlatBaseChange g)

@[reassoc (attr := simp)]
lemma blowupFlatBaseChangeIso_hom_snd :
    (I.blowupFlatBaseChangeIso g).hom ≫ pullback.snd _ _ = (I.comap g).blowupMap := by
  rw [blowupFlatBaseChangeIso, asIso_hom, blowupFlatBaseChange, Category.assoc, Category.assoc,
    pullback.lift_snd, Category.comp_id,
    GradedAlgebraData.PullbackData.relProjIsoPullback_hom_snd, Iso.inv_comp_eq,
    relProjReesIso_hom_blowupMap]

end AlgebraicGeometry.Scheme.IdealSheafData

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X : Scheme.{u}} {L : X.IdealSheafData}

/-- **The relative `Proj` of the Rees algebra of an invertible ideal is the base**: for an
invertible ideal sheaf `L`, the structure morphism `Proj_X(⨁ₙ Lⁿ) ⟶ X` is an isomorphism. On an
affine open where `L` is generated by a non-zerodivisor `a`, the Rees algebra is the polynomial
algebra on `a` in degree one, and its `Proj` is the base
(`AlgebraicGeometry.AffineBlowup.isIso_toSpec_of_eq_span`).
(blueprint: `lemma-products-composites-u-admissible-blow`; the affine case
`lemma-products-composites-u-admissible-blow` is
`AlgebraicGeometry.AffineBlowup.isIso_toSpec_of_eq_span`) -/
theorem isIso_relProjHom_reesData_of_isInvertible (hL : L.IsInvertible) :
    IsIso L.reesData.relProjHom := by
  have := isIso_blowupMap_of_isInvertible L hL
  rw [← relProjReesIso_hom_blowupMap]
  infer_instance

end AlgebraicGeometry.Scheme.IdealSheafData
