import Langlands.Geometry.FormalGroup.DeligneStalkUBaseChange
import Mathlib.RingTheory.Flat.Basic

/-! # Actual residue-fibre compatibility and condition (b) under base change -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory _root_.AlgebraicGeometry

namespace Langlands.DeligneFormalSpace

/-- The actual extension unit for a field homomorphism is injective. -/
theorem fieldExtension_unit_injective {K K' : Type u} [Field K] [Field K']
    (β : K →+* K') (M : ModuleCat.{u} K) :
    Function.Injective ((ModuleCat.extendRestrictScalarsAdj β).unit.app M) := by
  let := β.toAlgebra
  have h : Function.Injective (fun m : M => (1 : K') ⊗ₜ[K] m) := by
    convert!
      (Module.Flat.rTensor_preserves_injective_linearMap (M := M)
        (Algebra.linearMap K K') β.injective).comp
          (TensorProduct.lid K M).symm.injective
    ext m
    simp
  exact h

variable {O : Type u} [CommRing O] {d : ℕ} [NeZero d] {π : O}
  {F : Type u} [Field F] [Algebra O F] {S S' : Scheme.{u}}
  {φ : O →+* Γ(S, ⊤)}

namespace SheafPreDatum

variable (D : SheafPreDatum d π F φ) (f : S' ⟶ S)

/-- The actual residue-fibre comparison intertwines the actual maps induced by u. -/
theorem uResidueFibrePullback_square (x : S') (e : D.etaStalk (f x)) :
    (D.tangentPiQuotientFibrePullbackIso f x).hom
        ((D.pullback f).uResidueFibreMap x ((D.etaStalkPullbackIso f x).hom e)) =
      (ModuleCat.extendRestrictScalarsAdj (f.residueFieldMap x).hom).unit.app
        (D.tangentPiQuotientFibre (f x)) (D.uResidueFibreMap (f x) e) := by
  let M := ModuleCat.of (S.presheaf.stalk (f x)) (D.tangentPiQuotient (f x))
  let M' := ModuleCat.of (S'.presheaf.stalk x) ((D.pullback f).tangentPiQuotient x)
  let ρ := (f.stalkMap x).hom
  let σ := (S'.residue x).hom
  let α := (S.residue (f x)).hom
  let β := (f.residueFieldMap x).hom
  have h : σ.comp ρ = β.comp α :=
    congrArg CommRingCat.Hom.hom (Scheme.residue_residueFieldMap f x).symm
  let i₃ : (ModuleCat.extendScalars (σ.comp ρ)).obj M ≅
      (ModuleCat.extendScalars (β.comp α)).obj M :=
    eqToIso (congrArg (fun γ => (ModuleCat.extendScalars γ).obj M) h)
  change ((ModuleCat.extendScalarsComp α β).app M).hom
      (i₃.hom
        (((ModuleCat.extendScalarsComp ρ σ).app M).inv
          ((ModuleCat.extendScalars σ).map (D.tangentPiQuotientPullbackIso f x).hom
            ((ModuleCat.extendRestrictScalarsAdj σ).unit.app M'
              ((LinearMap.range ((D.pullback f).tangentStalkPi x)).mkQ
                ((D.pullback f).uStalkAdd x ((D.etaStalkPullbackIso f x).hom e))))))) =
    (ModuleCat.extendRestrictScalarsAdj β).unit.app
      ((ModuleCat.extendScalars α).obj M)
        ((ModuleCat.extendRestrictScalarsAdj α).unit.app M
          ((LinearMap.range (D.tangentStalkPi (f x))).mkQ (D.uStalkAdd (f x) e)))
  rw [extendScalars_unit_map, D.uPiQuotientPullback_square]
  rw [extendScalarsComp_inv_unit, extendScalars_eqToIso_unit _ _ h, extendScalarsComp_unit]

/-- Compare the actual pulled condition (b) map, with the original quotient as source. -/
def piQuotientResiduePullbackMap (x : S') :
    D.etaPiQuotient (f x) →+
      (ModuleCat.extendScalars (f.residueFieldMap x).hom).obj
        (D.tangentPiQuotientFibre (f x)) :=
  (D.tangentPiQuotientFibrePullbackIso f x).hom.hom.toAddMonoidHom.comp
    (((D.pullback f).piQuotientResidueMap x).comp
      (D.etaPiQuotientPullbackEquiv f x).toLinearMap.toAddMonoidHom)

/-- The actual condition (b) maps commute with the actual quotient and fibre comparisons. -/
theorem piQuotientResiduePullback_square (x : S') (q : D.etaPiQuotient (f x)) :
    (D.tangentPiQuotientFibrePullbackIso f x).hom
        ((D.pullback f).piQuotientResidueMap x (D.etaPiQuotientPullbackEquiv f x q)) =
      (ModuleCat.extendRestrictScalarsAdj (f.residueFieldMap x).hom).unit.app
        (D.tangentPiQuotientFibre (f x)) (D.piQuotientResidueMap (f x) q) := by
  obtain ⟨e, rfl⟩ := (LinearMap.range (D.etaStalkPi (f x))).mkQ_surjective q
  rw [D.etaPiQuotientPullbackEquiv_mk, (D.pullback f).piQuotientResidueMap_mk,
    D.piQuotientResidueMap_mk]
  exact D.uResidueFibrePullback_square f x e

/-- Condition (b) is preserved by arbitrary scheme base change. -/
theorem residueFibreInjective_pullback (hD : D.ResidueFibreInjective) :
    (D.pullback f).ResidueFibreInjective := by
  intro x a b hab
  obtain ⟨a, rfl⟩ := (D.etaPiQuotientPullbackEquiv f x).surjective a
  obtain ⟨b, rfl⟩ := (D.etaPiQuotientPullbackEquiv f x).surjective b
  apply congrArg (D.etaPiQuotientPullbackEquiv f x)
  apply hD (f x)
  apply fieldExtension_unit_injective (f.residueFieldMap x).hom
    (D.tangentPiQuotientFibre (f x))
  have h := congrArg (D.tangentPiQuotientFibrePullbackIso f x).hom hab
  simpa only [D.piQuotientResiduePullback_square f x] using h

end SheafPreDatum

end Langlands.DeligneFormalSpace
