/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ContinuousIntegralCoefficients
import WeilConjectures.AlgebraicGeometry.ContinuousFiniteFreeDenominators
import WeilConjectures.AlgebraicGeometry.ContinuousIntegralModuleTelescope
import WeilConjectures.AlgebraicGeometry.IntegralMatrixAnalyticData
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated

/-! # Integral models of kernels of rational matrices -/

@[expose] public section
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory Limits MonoidalCategory MonObj Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

private theorem integralScalarMap_mono (ℓ : ℕ) [Fact ℓ.Prime]
    (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E] (X : Scheme.{u}) :
    Mono (coefficientMap (integralScalarMap ℓ E) X) := by
  let : IsUltrametricDist E := IsUltrametricDist.of_normedAlgebra ℚ_[ℓ]
  let φ := coefficientMap (integralScalarMap ℓ E) X
  let e := chartComparison X (continuousIntegers ℓ E)
  let eE := chartComparison X E
  let i := integralFunctionInclusion ℓ E X
  have happ (U : X.ProEtᵒᵖ) : Mono (i.hom.app U) := by
    apply (AddCommGrpCat.mono_iff_injective _).2
    intro a b h
    apply ULift.ext
    ext x
    exact congrArg (fun z ↦ z.down x) h
  let _ := happ
  have : Mono i.hom := NatTrans.mono_of_mono_app _
  have : Mono i := (sheafToPresheaf (Scheme.ProEt.topology X) Ab.{u + 1}).mono_of_mono_map
    (inferInstanceAs (Mono i.hom))
  have he : φ ≫ eE = e ≫ i := chartComparison_naturality X
    (continuousIntegers ℓ E) E (continuousIntegers ℓ E).subtype continuous_subtype_val
  have : Mono (φ ≫ eE) := by rw [he]; infer_instance
  exact mono_of_mono φ eE

/-- The scalar-localization unit is injective on each standard finite free integral module.
Source: injectivity of O_E to E and naturality of the extension unit.
(auxiliary; not a blueprint node)

Proof. For the regular module the unit, followed by the regular extension
isomorphism, is the injective coefficient map. For a finite free module, compose
a morphism killed by the unit with each coordinate projection. Naturality and
injectivity of the regular unit show all coordinates vanish. -/
theorem integralFiniteFree_unit_mono (ℓ : ℕ) [Fact ℓ.Prime]
    (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]
    (X : Scheme.{u}) (n : ℕ) :
    Mono ((Mod.extendRestrictAdjunction
      (coefficientMap (integralScalarMap ℓ E) X)).unit.app
        (Mod.finiteFree (condensedRingObj (integralCoeff ℓ E) X) n)) := by
  let R := condensedRingObj (integralCoeff ℓ E) X
  let φ := coefficientMap (integralScalarMap ℓ E) X
  let adj := Mod.extendRestrictAdjunction φ
  let j := Mod.regularExtensionIso φ
  have : Mono φ := integralScalarMap_mono ℓ E X
  have : Mono (Mod.regularCoefficientMap φ) :=
    (Mod.forget R).mono_of_mono_map (inferInstanceAs (Mono φ))
  have hunit : adj.unit.app (Mod.regular R) ≫ (Mod.comap φ).map j.hom =
      Mod.regularCoefficientMap φ := by
    apply Mod.hom_ext
    change Mod.extendUnitHom φ (Mod.regular R) ≫
      (Mod.extendHom φ (Mod.regularCoefficientMap φ)).hom = φ
    exact Mod.extendUnitHom_extendHom φ (Mod.regularCoefficientMap φ)
  have : Mono (adj.unit.app (Mod.regular R)) := mono_of_mono_fac hunit
  apply (Preadditive.mono_iff_cancel_zero _).2
  intro Z g hg
  apply biproduct.hom_ext
  intro i
  apply (cancel_mono (adj.unit.app (Mod.regular R))).1
  have hn := adj.unit.naturality (biproduct.π (fun _ : Fin n ↦ Mod.regular R) i)
  dsimp only [Functor.id_map] at hn
  rw [Category.assoc, hn, ← Category.assoc, hg]
  simp

private theorem integralRational_pow_nsmul_isIso (ℓ : ℕ) [Fact ℓ.Prime]
    (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E] (X : Scheme.{u})
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj E) X)) (k : ℕ) :
    IsIso (ℓ ^ k • 𝟙 M) := by
  induction k with
  | zero => simpa using (inferInstance : IsIso (𝟙 M))
  | succ k ih =>
    have : IsIso (ℓ • 𝟙 M) := module_nsmul_isIso ℓ E X M
    have h : ℓ ^ (k + 1) • 𝟙 M = (ℓ ^ k • 𝟙 M) ≫ (ℓ • 𝟙 M) := by
      simp only [pow_succ, Preadditive.nsmul_comp, Preadditive.comp_nsmul,
        Category.id_comp, mul_smul]
      exact smul_comm _ _ _
    rw [h]
    infer_instance

/-- The kernel of the integral adjoint of a surjective rational finite matrix
has a model as the kernel of an integral matrix with surjective rationalization.
Source: Bhatt--Scholze, Section 6.8, continuous coefficient localization.
(auxiliary; not a blueprint node)

Proof. Clear the matrix denominators on the compact scheme. Adjunction identifies
the integral numerator followed by the target's localization unit with the
corresponding power of ℓ times the original adjoint. The localization unit is mono
on a finite free module, and ℓ is invertible on rational modules. These two facts
identify the kernels. The same scalar invertibility preserves rational surjectivity. -/
theorem integralFiniteFree_kernel_model (ℓ : ℕ) [Fact ℓ.Prime]
    (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]
    (X : Scheme.{u}) [CompactSpace X] (n m : ℕ)
    (f : (Mod.extendScalars (coefficientMap (integralScalarMap ℓ E) X)).obj
        (Mod.finiteFree (condensedRingObj (integralCoeff ℓ E) X) n) ⟶
      (Mod.extendScalars (coefficientMap (integralScalarMap ℓ E) X)).obj
        (Mod.finiteFree (condensedRingObj (integralCoeff ℓ E) X) m)) [Epi f] :
    ∃ g : Mod.finiteFree (condensedRingObj (integralCoeff ℓ E) X) n ⟶
        Mod.finiteFree (condensedRingObj (integralCoeff ℓ E) X) m,
      Epi ((Mod.extendScalars (coefficientMap (integralScalarMap ℓ E) X)).map g) ∧
      Nonempty (kernel ((Mod.extendRestrictAdjunction
        (coefficientMap (integralScalarMap ℓ E) X)).homEquiv _ _ f) ≅ kernel g) := by
  classical
  let φ := coefficientMap (integralScalarMap ℓ E) X
  let F := Mod.extendScalars φ
  let G := Mod.comap (D := Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) φ
  let adj := Mod.extendRestrictAdjunction φ
  let A := Mod.finiteFree (condensedRingObj (integralCoeff ℓ E) X) n
  let B := Mod.finiteFree (condensedRingObj (integralCoeff ℓ E) X) m
  let b := adj.homEquiv A (F.obj B) f
  obtain ⟨k, g, hg⟩ := integralFiniteFree_clear_denominators ℓ E X n m f
  have hscalar : IsIso (ℓ ^ k • 𝟙 (F.obj B)) :=
    integralRational_pow_nsmul_isIso ℓ E X _ k
  have hscalarG : IsIso (ℓ ^ k • 𝟙 (G.obj (F.obj B))) := by
    simpa only [G.map_nsmul, G.map_id] using G.map_isIso (ℓ ^ k • 𝟙 (F.obj B))
  have hFg : F.map g = f ≫ (ℓ ^ k • 𝟙 (F.obj B)) := by
    rw [Preadditive.comp_nsmul, Category.comp_id]
    exact hg
  have hEpi : Epi (F.map g) := by rw [hFg]; infer_instance
  have hb : g ≫ adj.unit.app B = b ≫ (ℓ ^ k • 𝟙 (G.obj (F.obj B))) := by
    have hn := adj.unit.naturality g
    dsimp only [Functor.id_map, Functor.comp_map] at hn
    rw [hn]
    rw [hg, G.map_nsmul, Preadditive.comp_nsmul]
    change ℓ ^ k • (adj.unit.app A ≫ G.map f) =
      b ≫ (ℓ ^ k • 𝟙 (G.obj (F.obj B)))
    simp only [Preadditive.comp_nsmul]
    rfl
  have : Mono (adj.unit.app B) := integralFiniteFree_unit_mono ℓ E X m
  exact ⟨g, hEpi, ⟨(kernelCompMono b (ℓ ^ k • 𝟙 (G.obj (F.obj B)))).symm ≪≫
    kernelIsoOfEq hb.symm ≪≫ kernelCompMono g (adj.unit.app B)⟩⟩

end AlgebraicGeometry.ProEtale.CondensedRing
