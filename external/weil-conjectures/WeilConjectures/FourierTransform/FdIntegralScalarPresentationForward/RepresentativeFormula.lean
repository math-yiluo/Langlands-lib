/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.FourierTransform.FdIntegralScalarPresentationForward.DerivedCoherence
import all WeilConjectures.FourierTransform.FdIntegralScalarPresentationForward.DerivedCoherence
import all WeilConjectures.FourierTransform.FdIntegralScalarPresentationForward.DerivedCocycle
import all WeilConjectures.FourierTransform.FdIntegralScalarPresentationForward.OrdinaryCocycle
import all WeilConjectures.FourierTransform.FdIntegralOrdinaryScalarModel.FdIntegralOrdinaryScalarModel
import all WeilConjectures.AlgebraicGeometry.Finite.FiniteStagePairCategory

/-! # Representative unit facts for the normalized derived ordinary square

The ordinary transport comparison and the ambient derived unit are computed on cochain
representatives, as needed for the unit equation of the normalized derived ordinary square.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u w
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.FdIntegralScalarForward

/-- The chain-level unit equation of a tensor-normalized comparison. -/
theorem chain_unit_gen {V W : Type*} [Category V] [Category W] [Preadditive V]
    [Preadditive W] (o : V ⥤ V) (t : V ⥤ W) (x : W ⥤ W) [ho : o.Additive] [ht : t.Additive]
    [hx : x.Additive]
    (c : o ⋙ t ≅ t ⋙ x)
    (C : o.mapHomologicalComplex (.up ℤ) ⋙ t.mapHomologicalComplex (.up ℤ) ≅
      t.mapHomologicalComplex (.up ℤ) ⋙ x.mapHomologicalComplex (.up ℤ))
    (hC : ∀ P n, (C.hom.app P).f n = c.hom.app (P.X n)) (Ou : o ≅ 𝟭 V) (Xu : x ≅ 𝟭 W)
    (hmod : ∀ N, c.inv.app N ≫ t.map (Ou.hom.app N) = Xu.hom.app (t.obj N))
    (P : CochainComplex V ℤ) :
    (t.mapHomologicalComplex (.up ℤ)).map
        ((NatIso.mapHomologicalComplex Ou (.up ℤ) ≪≫
          Functor.mapHomologicalComplexIdIso V (.up ℤ)).hom.app P) =
      C.hom.app P ≫ (NatIso.mapHomologicalComplex Xu (.up ℤ) ≪≫
        Functor.mapHomologicalComplexIdIso W (.up ℤ)).hom.app
          ((t.mapHomologicalComplex (.up ℤ)).obj P) := by
  apply HomologicalComplex.hom_ext
  intro n
  have h := hmod (P.X n)
  rw [← Iso.app_inv, Iso.inv_comp_eq, Iso.app_hom] at h
  simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f, hC,
    Iso.trans_hom, NatTrans.comp_app, NatIso.mapHomologicalComplex_hom_app_f,
    Functor.mapHomologicalComplexIdIso_hom_app_f]
  erw [Category.comp_id, Category.comp_id]
  exact h

variable (l : ℕ) [Fact l.Prime]
  (Ω : Type w) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
  (T : Scheme.{u}) [IsNoetherian T]

set_option hygiene false in
local notation "𝓉 " E:max => fdCoefficientTransport l (pbcFiniteField.{u} l Ω E) T

/-- Chain-level unit equation of the ordinary transport comparison. -/
private theorem ordinary_unit_chain (E : Padic.FiniteCoefficientFields l Ω)
    (o : FdOrdinaryScalarTransport l Ω T (le_refl E))
    (P : CochainComplex (integralTowerModules l (pbcFiniteField.{u} l Ω E) T) ℤ) :
    letI := fdCoefficientTransportAdditive l (pbcFiniteField.{u} l Ω E) T
    ((𝓉 E).mapHomologicalComplex (.up ℤ)).map
        ((NatIso.mapHomologicalComplex (Ounit l Ω T E) (.up ℤ) ≪≫
          Functor.mapHomologicalComplexIdIso _ (.up ℤ)).hom.app P) =
      (FdIntegralOrdinaryScalarModel.ordinaryTransportComplex l Ω T (le_refl E) o).hom.app P ≫
        (NatIso.mapHomologicalComplex (pbcOrdinaryScalarUnit l Ω T E) (.up ℤ) ≪≫
          Functor.mapHomologicalComplexIdIso _ (.up ℤ)).hom.app
            (((𝓉 E).mapHomologicalComplex (.up ℤ)).obj P) := by
  exact chain_unit_gen (ht := fdCoefficientTransportAdditive l (pbcFiniteField.{u} l Ω E) T)
    (ho := integralOrdinaryScalar_additive l _ _ _ T)
    (hx := pbcExtend_additive (pbcCompletedScalarMap l Ω T (le_refl E)))
    _ _ _ (oc l Ω T (le_refl E) o) _ (otc_f l Ω T (le_refl E) o)
    (Ounit l Ω T E) (pbcOrdinaryScalarUnit l Ω T E)
    (comparison_unit l Ω T E (oc l Ω T (le_refl E) o) (Ounit l Ω T E)
      (pbcOrdinaryScalarUnit l Ω T E) (oc_inv_tensor l Ω T (le_refl E) o)
      (Ounit_tensor l Ω T E) (Xunit_tensor l Ω T E)) P

/-- The ambient derived unit on representatives. -/
private theorem ambient_unit_rep (E : Padic.FiniteCoefficientFields l Ω)
    (P : CochainComplex (pbcModules T (pbcAdicCompletion T (pbcStageDatum.{u} l Ω E))) ℤ) :
    (pbcAmbientScalarUnit l Ω T E).hom.app (DerivedCategory.Q.obj P) =
      (pbcCounitNT (pbcCompletedScalarMap l Ω T (le_refl E))).app P ≫ DerivedCategory.Q.map
        ((NatIso.mapHomologicalComplex (pbcOrdinaryScalarUnit l Ω T E) (.up ℤ) ≪≫
          Functor.mapHomologicalComplexIdIso _ (.up ℤ)).hom.app P) := by
  rw [pbcCounitNT_app]
  refine ((pbcAmbientScalarUnit_exists l Ω T E).exists.choose_spec P).trans ?_
  congr 2

end WeilConjectures.FdIntegralScalarForward
