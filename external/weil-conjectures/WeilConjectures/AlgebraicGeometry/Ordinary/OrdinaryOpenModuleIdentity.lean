/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Completed.Open.CompletedOpenExchangeTransport
public import WeilConjectures.AlgebraicGeometry.AdicCoefficientDatum.CompletedOrdinaryComparisons
import WeilConjectures.AlgebraicGeometry.ProEtale.Canonical.ProEtaleCanonicalAdjunctionUnit

/-! # Identity normalization before deriving open exchange

## References

* Stacks 03D8 and 03DI
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe t
open CategoryTheory CategoryTheory.Limits Opposite
open scoped ChangeOfRings

namespace AlgebraicGeometry.Scheme

private theorem tensor_transport (T : Scheme.{t})
    {R S : Sheaf (ProEt.topology T) CommRingCat.{t + 1}} (φ : R ⟶ S)
    (M : pbcModules T R) (V : T.ProEtᵒᵖ) (s : S.obj.obj V) (x : M.val.obj V)
    (h : (pbcExtend φ).obj M = SheafOfModules.changeOfRings.{t, t + 1, t + 1} φ M) :
    (eqToHom h).val.app V (pbcTensorSection φ M V s x) =
      (toSheafify (ProEt.topology T)
        (SheafOfModules.changeOfRingsPresheaf.{t, t + 1, t + 1}
          (J := ProEt.topology T) φ M).presheaf).app V
              (s ⊗ₜ[R.obj.obj V, (φ.hom.app V).hom] x) := by
  let h₀ := (completedAdicChangeData T φ).choose_spec.choose M
  have hh : (eqToHom h₀.symm ≫ eqToHom h) = 𝟙 _ := by simp
  exact congrArg (fun f ↦ f.val.app V
    ((toSheafify (ProEt.topology T)
      (SheafOfModules.changeOfRingsPresheaf.{t, t + 1, t + 1}
        (J := ProEt.topology T) φ M).presheaf).app V
            (s ⊗ₜ[R.obj.obj V, (φ.hom.app V).hom] x))) hh

/-- Identity on the ordinary module pullback, with the section-normalized adjunction. -/
def cbcModulePullId {A : Type (t + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    (T : Scheme.{t}) : completedModulePullback (𝟙 T) d ≅ 𝟭 _ :=
  eqToIso (cbcDatumModulePull_eq d (𝟙 T)) ≪≫
    (proEtaleRingModuleAdjunction (𝟙 T) (d.completedRing T) (d.completedRing T)
      (d.integralRingIso (𝟙 T))).leftAdjointIdIso (d.modulePushId T)

end AlgebraicGeometry.Scheme
