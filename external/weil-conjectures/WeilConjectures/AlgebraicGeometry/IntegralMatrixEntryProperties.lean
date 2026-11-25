/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.IntegralMatrixAnalyticCover

import WeilConjectures.AlgebraicGeometry.IntegralRegularRationalUnit
import WeilConjectures.AlgebraicGeometry.ContinuousRegularFunctions

/-! # Integral division and cancellation for a dominating coefficient -/

@[expose] public section

universe u
open CategoryTheory Limits MonoidalCategory MonObj Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

private lemma continuousIntegral_divides (ℓ : ℕ) [Fact ℓ.Prime]
    (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E] (X : Scheme.{u})
    (p g : Mod.regular (continuousAbRing X (continuousIntegers ℓ E)) ⟶
      Mod.regular (continuousAbRing X (continuousIntegers ℓ E)))
    (hp : ∀ x, (regularCoefficient X _ p x).val ≠ 0)
    (hg : ∀ x, ‖(regularCoefficient X _ g x).val‖ ≤
      ‖(regularCoefficient X _ p x).val‖) :
    ∃ q, q ≫ p = g := by
  have hb (x : X) : (regularCoefficient X _ g x).val /
      (regularCoefficient X _ p x).val ∈ continuousIntegers ℓ E := by
    change ‖(regularCoefficient X _ g x).val / (regularCoefficient X _ p x).val‖₊ ≤ 1
    rw [← NNReal.coe_le_coe, coe_nnnorm, NNReal.coe_one, norm_div]
    exact (div_le_one (norm_pos_iff.mpr (hp x))).2 (hg x)
  let b : C(X, continuousIntegers ℓ E) :=
    ⟨fun x ↦ ⟨_, hb x⟩,
      ((continuous_subtype_val.comp (regularCoefficient X _ g).continuous).div
        (continuous_subtype_val.comp (regularCoefficient X _ p).continuous) hp).subtype_mk _⟩
  refine ⟨continuousMultiplier X _ b, regularCoefficient_injective X _ ?_⟩
  rw [regularCoefficient_comp, regularCoefficient_multiplier]
  ext x
  exact div_mul_cancel₀ _ (hp x)

/-- A nowhere-zero dominating matrix entry cancels, is rationally invertible, and
integrally divides every entry of its row.

Source: Bhatt--Scholze, Section 6.8, Definition 6.8.10 and Proposition 6.8.11(1);
continuous-function pivot argument, division and cancellation step.
(auxiliary; not a blueprint node)

Proof: conjugate each regular-module endomorphism by the supplied ring realization.
Linearity on sections makes it multiplication by its value on 1; naturality makes this
value the restriction of the global continuous function. A nowhere-zero multiplier is
injective on every site object, hence monic as a sheaf and a module map. Over E its
continuous reciprocal is an inverse, and coefficient comparison commutes with extension
of scalars on regular modules. For every row entry, divide its E-valued function by the
pivot. The quotient is continuous and has norm at most one by dominance, so it is an
actual continuous O_E-valued function. Multiplication by this quotient is a regular
endomorphism q; pointwise multiplication proves q followed by the pivot is the row entry.
No rational cokernel or constant-rank hypothesis is used. -/
theorem integralMatrix_entry_properties (ℓ : ℕ) [Fact ℓ.Prime]
    (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E] (X : Scheme.{u})
    (e : condensedRingObj (integralCoeff ℓ E) X ⟶
      (sheafCompose (Scheme.ProEt.topology X) (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj
        (continuousMapRingSheaf X (continuousIntegers ℓ E))) [IsIso e] [IsMonHom e]
    (eE : condensedRingObj (Profinite.continuousMapRingObj E) X ⟶
      (sheafCompose (Scheme.ProEt.topology X) (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj
        (continuousMapRingSheaf X E)) [IsIso eE] [IsMonHom eE]
    (he : coefficientMap (integralScalarMap ℓ E) X ≫ eE =
      e ≫ integralFunctionInclusion ℓ E X)
    {n t : ℕ}
    (f : Mod.finiteFree (condensedRingObj (integralCoeff ℓ E) X) n ⟶
      Mod.finiteFree (condensedRingObj (integralCoeff ℓ E) X) t)
    (i : Fin t) (j : Fin n)
    (hzero : ∀ x, (integralMatrixFunctions ℓ E X e f i j x).val ≠ 0)
    (hbound : ∀ r s x, ‖(integralMatrixFunctions ℓ E X e f r s x).val‖ ≤
      ‖(integralMatrixFunctions ℓ E X e f i j x).val‖) :
    let p := biproduct.ι _ j ≫ f ≫ biproduct.π _ i
    Mono p ∧
      IsIso ((Mod.extendScalars (coefficientMap (integralScalarMap ℓ E) X)).map p) ∧
      ∃ q : Fin n →
        (Mod.regular (condensedRingObj (integralCoeff ℓ E) X) ⟶
          Mod.regular (condensedRingObj (integralCoeff ℓ E) X)),
        ∀ k, q k ≫ p = biproduct.ι _ k ≫ f ≫ biproduct.π _ i := by
  let R := condensedRingObj (integralCoeff ℓ E) X
  let O := continuousIntegers ℓ E
  let p : Mod.regular R ⟶ Mod.regular R :=
    biproduct.ι (fun _ : Fin n ↦ Mod.regular R) j ≫ f ≫
      biproduct.π (fun _ : Fin t ↦ Mod.regular R) i
  let K := (Mod.comapEquivalenceOfIsIso (inv e)).functor
  have : K.IsEquivalence := (Mod.comapEquivalenceOfIsIso (inv e)).isEquivalence_functor
  let jR := Mod.regularIsoOfIsIso e
  let p' := jR.inv ≫ K.map p ≫ jR.hom
  let g (k : Fin n) := biproduct.ι (fun _ : Fin n ↦ Mod.regular R) k ≫ f ≫
    biproduct.π (fun _ : Fin t ↦ Mod.regular R) i
  let g' (k : Fin n) := jR.inv ≫ K.map (g k) ≫ jR.hom
  have hc (k : Fin n) : regularCoefficient X O (g' k) =
      integralMatrixFunctions ℓ E X e f i k := rfl
  have hcp : regularCoefficient X O p' = integralMatrixFunctions ℓ E X e f i j := rfl
  have hp' : Mono p' := continuousRegular_mono X O p' (by
    intro x hx
    exact hzero x (congrArg Subtype.val hx))
  have hKp : K.map p = jR.hom ≫ p' ≫ jR.inv := by
    simp only [p', Category.assoc, Iso.hom_inv_id_assoc, Iso.hom_inv_id, Category.comp_id]
  have : Mono (K.map p) := by rw [hKp]; infer_instance
  have hp : Mono p := K.mono_of_mono_map ‹Mono (K.map p)›
  have hdiv (k : Fin n) : ∃ q, q ≫ p' = g' k := by
    apply continuousIntegral_divides ℓ E X p' (g' k)
    · exact hzero
    · exact hbound i k
  choose q' hq' using hdiv
  let q (k : Fin n) := K.preimage (jR.hom ≫ q' k ≫ jR.inv)
  refine ⟨hp, integralRegular_rationalUnit_of_nowhereZero ℓ E X e eE he p hzero, q, ?_⟩
  intro k
  apply K.map_injective
  rw [K.map_comp, Functor.map_preimage]
  simpa only [p', g', Category.assoc, Iso.hom_inv_id_assoc, Iso.hom_inv_id,
    Category.comp_id] using congrArg (fun z ↦ jR.hom ≫ z ≫ jR.inv) (hq' k)

end AlgebraicGeometry.ProEtale.CondensedRing
