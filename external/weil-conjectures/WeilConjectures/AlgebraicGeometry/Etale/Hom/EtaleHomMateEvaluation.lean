/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Native.NativeHomSourceShiftData
public import WeilConjectures.CategoryTheory.SixFunctors.HomShiftEvaluationNormalization

/-! # Evaluation identity for the opposite internal Hom shift mate -/

@[expose] public section
set_option autoImplicit false
set_option linter.style.haveILetI false
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated MonoidalCategory
open CategoryTheory.Pretriangulated.Opposite Opposite
namespace AlgebraicGeometry.Etale

section MateEvaluation

variable {D : Type*} [Category D] [Preadditive D] [HasShift D ℤ]
  [monoidal : MonoidalCategory D] [MonoidalClosed D]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [(curriedTensor D).CommShift₂Int]

private theorem raw_mate_evaluation (K M : D) (r : ℤ) :
    (tensorLeft (K⟦r⟧)).map ((ProEtale.siteHomSourceShift K r).hom.app M) ≫
        (ProEtale.siteHomTensorParameterShift K r).hom.app (((ihom K).obj M)⟦-r⟧) ≫
        (((tensorLeft K).commShiftIso (-r)).hom.app ((ihom K).obj M))⟦r⟧' ≫
        (shiftFunctorCompIsoId D (-r) r (neg_add_cancel r)).hom.app _ ≫
        (ihom.adjunction K).counit.app M =
      (ihom.adjunction (K⟦r⟧)).counit.app M := by
  let e := (tensorLeft K).commShiftIso r ≪≫
    (ProEtale.siteHomTensorParameterShift K r).symm
  have h := Adjunction.rightAdjointUniq_hom_app_counit
    (ihom.adjunction (K⟦r⟧))
    (((shiftEquiv D r).toAdjunction.comp (ihom.adjunction K)).ofNatIsoLeft e) M
  simpa only [ProEtale.siteHomSourceShift, Adjunction.ofNatIsoLeft_counit,
    Adjunction.comp_counit_app,
    NatTrans.comp_app, Functor.whiskerLeft_app, e, Iso.trans_inv, Iso.symm_inv,
    Category.assoc, Equivalence.toAdjunction_counit, shiftEquiv, shiftEquiv',
    Equivalence.Equivalence_mk'_counit, Functor.comp_obj,
    Functor.map_shiftFunctorCompIsoId_hom_app, Iso.inv_hom_id_app_assoc] using h

private theorem transported_mate_evaluation (K M : D) (r s : ℤ) (h : -r = s) :
    (tensorLeft (K⟦r⟧)).map
        (((ProEtale.siteHomSourceShift K r).hom.app M) ≫
          (eqToIso (congrArg (shiftFunctor D) h)).hom.app ((ihom K).obj M)) ≫
      (ProEtale.siteHomTensorParameterShift K r).hom.app (((ihom K).obj M)⟦s⟧) ≫
      (((tensorLeft K).commShiftIso s).hom.app ((ihom K).obj M))⟦r⟧' ≫
      (shiftFunctorCompIsoId D s r (by rw [← h]; exact neg_add_cancel r)).hom.app _ ≫
      (ihom.adjunction K).counit.app M =
    (ihom.adjunction (K⟦r⟧)).counit.app M := by
  subst s
  simpa only [eqToIso_refl, Iso.refl_hom, NatTrans.id_app, Functor.comp_obj,
    Category.comp_id] using
    raw_mate_evaluation K M r

/-- The raw opposite source-shift mate preserves evaluation after tensor cancellation.
Source: Stacks Project, Tag 08JC; right-adjoint uniqueness and its counit identity.
Proof: expand the mate defined by rightAdjointUniq, use its counit identity, and
cancel the tensor shift isomorphism. Reindex r=-n and transport through neg_neg n.
The identity holds for zero and negative shifts as well.
(blueprint: lem-coef-etale-hom-opposite-mate-evaluation) -/
private theorem opposite_mate_evaluation (K M : D) (n : ℤ) :
    (tensorLeft (K⟦-n⟧)).map
        ((ProEtale.siteHomOppositeSourceShift K n).hom.app M) ≫
      ((((curriedTensor D).flip.obj (((ihom K).obj M)⟦n⟧)).commShiftIso (-n)).hom.app K ≫
        (((tensorLeft K).commShiftIso n).hom.app ((ihom K).obj M))⟦-n⟧' ≫
        (shiftFunctorCompIsoId D n (-n) (add_neg_cancel n)).hom.app _) ≫
      (ihom.adjunction K).counit.app M = (ihom.adjunction (K⟦-n⟧)).counit.app M := by
  simpa only [ProEtale.siteHomOppositeSourceShift, ProEtale.siteHomTensorParameterShift,
    Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.whiskerLeft_app, NatIso.ofComponents_hom_app, Iso.app_hom, Functor.comp_obj,
    Functor.id_obj, Category.assoc] using
    transported_mate_evaluation K M (-n) n (neg_neg n)

/-- The quadratic-signed mate obeys evaluation normalization.
Source: Stacks Project, Tag 08JC; right-adjoint uniqueness and its counit identity.
Proof: substitute the signed source-mate component, cancel the two identical
integer-unit signs, and apply the raw opposite mate evaluation identity above.
The raw identity expands rightAdjointUniq_hom_app_counit and cancels the tensor
shift isomorphism, then reindexes the source shift by r=-n.
(blueprint: lem-coef-etale-hom-opposite-mate-evaluation) -/
theorem etaleHom_signedMateEvaluation (M : D)
    (s : (MonoidalClosed.internalHom.flip.obj M).CommShift ℤ)
    (hs : ∀ (K : D) (n : ℤ),
      (s.commShiftIso n).hom.app (op K) = (n * (n + 1) / 2).negOnePow •
        (ProEtale.siteHomOppositeSourceShift K n).hom.app M) :
    homShiftEvaluationNormalization M s := by
  letI := s
  unfold homShiftEvaluationNormalization
  intro K n
  rw [hs K n]
  simp only [smul_smul, Int.units_mul_self, one_smul]
  simpa only [MonoidalClosed.internalHom, Functor.flip_obj_obj,
    MonoidalClosed.internalHomAdjunction₂] using opposite_mate_evaluation K M n

end MateEvaluation

end AlgebraicGeometry.Etale
