/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.IntegralFiniteScalar.IntegralFiniteScalarModelDefinitions
/-! # The forced cochain formula for an augmentation-normalized comparison
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.IntegralFiniteScalar
open CondensedRing
attribute [local instance 20000] AlgebraicGeometry.ProEtale.sheafBraidedCategory
private instance ring_comm (Λ : ScalarSixRing.{u}) : IsCommMonObj Λ.X := Λ.comm
attribute [local irreducible] Functor.mapDerivedCategory Functor.leftDerivedFunctor
  DerivedCategory.monoidalClosed Mod.monoidalClosed Sheaf.monoidalCategory
  AlgebraicGeometry.ProEtale.upperStarFromPoint
-- Compare the two total tensors using their invertible coefficient summands.
/-- Augmentation normalization computes beta using any ordinary and total comparisons
with the prescribed underlying maps and degree-zero summands. -/
theorem finiteFreeScalar_normalizedBeta_computes
    {Λ Λ' : ScalarSixRing.{u}} (a : Λ ⟶ Λ')
    (S : ShortComplex (PointModules Λ))
    (t : S.X₃ ≅ (Mod.comap a.hom.hom).obj (Mod.regular Λ'.X)) (Z : Scheme.{u})
    (β : tensorLeft (DerivedCategory.Q.obj (complex Λ S Z)) ≅
      scalarSixChange a Z ⋙ restriction a Z)
    (hβ : AugmentationNormalized a S t Z β)
    (C : CochainComplex (ModuleRingedComparison.internalModules Λ.X Z) ℤ)
    (hC : (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat C)
    (κ : ∀ M : ModuleRingedComparison.internalModules Λ.X Z,
      (Mod.comap (coefficientMap (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom Z)).obj
        (Mod.regular (condensedRingObj Λ'.X Z)) ⊗ M ≅
      (Mod.comap (coefficientMap (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom Z)).obj
        ((Mod.extendScalars
          (coefficientMap (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom Z)).obj M))
    (hκ : ∀ M, (κ M).hom.hom =
      (Mod.extendForgetTensorObjIso
        (coefficientMap (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom Z) M).inv)
    (τ : HomologicalComplex.tensorObj (target Λ S Z) C ≅
      (((Mod.comap
        (coefficientMap (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom Z)).mapHomologicalComplex (.up ℤ)).obj
          (((Mod.extendScalars
            (coefficientMap (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom Z)).mapHomologicalComplex
              (.up ℤ)).obj C)))
    (hτ : ∀ n : ℤ,
      HomologicalComplex.ιTensorObj (target Λ S Z) C 0 n n (zero_add n) ≫ τ.hom.f n =
        ((targetZeroIso a S t Z).hom ⊗ₘ 𝟙 (C.X n)) ≫ (κ (C.X n)).hom) :
    β.hom.app (DerivedCategory.Q.obj C) ≫
        (restriction a Z).map (scalarCounit a Z C) ≫
        (Mod.comap
        (coefficientMap (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom Z)).mapDerivedCategoryFactors.hom.app _ =
      Functor.LaxMonoidal.μ DerivedCategory.Q (complex Λ S Z) C ≫
        DerivedCategory.Q.map (HomologicalComplex.tensorHom (augmentation Λ S Z) (𝟙 C)) ≫
        DerivedCategory.Q.map τ.hom := by
  obtain ⟨κ', hκ', hβ⟩ := hβ
  obtain ⟨τ', hτ', hβ⟩ := hβ C hC
  have hk (M : ModuleRingedComparison.internalModules Λ.X Z) :
      (κ' M).hom = (κ M).hom := by
    apply Mod.hom_ext
    exact (hκ' M).trans (hκ M).symm
  have ht : τ'.hom = τ.hom := by
    ext n : 1
    let i := HomologicalComplex.ιTensorObj (target Λ S Z) C 0 n n (zero_add n)
    have hi : IsIso (i ≫ τ.hom.f n) := by
      dsimp only [i]
      rw [hτ]
      infer_instance
    have : IsIso i := IsIso.of_isIso_comp_right i (τ.hom.f n)
    apply (cancel_epi i).1
    rw [hτ', hτ, hk]
  simpa only [ht] using hβ

end AlgebraicGeometry.ProEtale.IntegralFiniteScalar
