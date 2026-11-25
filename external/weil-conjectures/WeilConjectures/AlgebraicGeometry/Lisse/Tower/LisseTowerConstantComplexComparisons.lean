/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Lisse.Tower.LisseTowerLocalizedConstantsNormalization
import WeilConjectures.AlgebraicGeometry.Lisse.Tower.LisseTowerConstantCoherence

/-! # Constant model comparisons and the coefficient identity on complexes

Only the identity semilinear arrow on a represented complex is checked here.
Localization and naturality extend this to arbitrary derived arrows in
`lisseTower_localized_constants_normalization`.

## References

* Stacks Project, Modules on Sites, Tags 03CY and 03DA
* Sites, Tag 0H7J
* Cohomology on Sites, Tag 06YY
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme
attribute [local irreducible] HasDerivedCategory.standard pbcDerivedRestrict
  lisseTowerFixedRealization constantAdicQuotientRealization constantAdicFiniteRealization
  constantAdicQuotientRightIso constantAdicFiniteProjection
  lisseTowerConstantInput lisseTowerConstantScalarIso lisseTowerConstantModelIso
  lisseTowerAlgebraRestrictIso

/-- The natural constant comparisons can be constructed with compatible coefficient
identity arrows on cochain complexes. -/
theorem lisseTower_constant_complex_comparisons
    {X Z T S : Scheme.{u}} (g : Z ⟶ X) (a : T ⟶ S) (b : Z ⟶ T)
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) :
    ∃ model : ∀ n : ℕ,
      lisseTowerConstantInput g a b d n ≅ constantAdicQuotientRealization g d n,
    ∀ (n : ℕ)
      (K : CochainComplex (ModuleCat.{u + 1} (lisseTowerEtaleRing d n)) ℤ),
      ((lisseTowerConstantScalarIso g a b d n) ≪≫
        lisseTowerConstantModelIso g a b d n (model n)).hom.app (DerivedCategory.Q.obj K) =
      (Functor.isoWhiskerLeft (normalizationModuleRestrict (lisseTowerEtaleQuotient d n))
          (lisseTowerConstantModelIso g a b d (n + 1) (model (n + 1))) ≪≫
        Functor.isoWhiskerRight (lisseTowerAlgebraRestrictIso d n)
          (constantAdicFiniteRealization g d)).hom.app (DerivedCategory.Q.obj K) :=
  ⟨fun n ↦ lisseTowerConstantModel g a b d n,
    fun n K ↦ lisseTowerConstantModel_coherence g a b d n K⟩

end AlgebraicGeometry.Scheme
