import Langlands.Algebra.CenterScalarFunctionStatement
import Langlands.Algebra.NonUnitalSchurProof
import Langlands.Algebra.NondegenerateModuleNaturalEndClassificationProof

/-! # Proof of Renard I.1.8: the centre as an algebra of functions on the irreducibles

This proves `Langlands.Algebra.CenterScalarFunctionStatement`. The scalars come from the
original-action Schur lemma B.II (`Langlands.Renard.nonUnitalSchurScalarOfAlgebraRankCountable`)
applied with Renard's canonical scalars (I.2.1). Class invariance is naturality of the
centre together with automatic scalar linearity of intertwiners. Faithfulness on `Â` uses
the fixing idempotent `e` of `e • m`; faithfulness on `ℨ(A)` uses naturality along the
orbit intertwiners from the lifted regular module `A`.
-/

set_option autoImplicit false

noncomputable section

namespace Langlands.Algebra
namespace CenterScalarFunctionProof

open CategoryTheory

universe uA uM

section

variable {A : Type uA} [NonUnitalRing A]

/-- Subtraction law of an original action, from `add_smul`. -/
theorem sub_smul {M : Type*} [AddCommGroup M] [NonUnitalModule A M] (a b : A) (m : M) :
    (a - b) • m = a • m - b • m := by
  rw [eq_sub_iff_add_eq, ← NonUnitalModule.add_smul, sub_add_cancel]

/-- Naturality of a centre element along the orbit intertwiner `a ↦ a • m` of the lifted
regular module: `z_M (a • m) = z_A(a) • m`. -/
theorem app_smul_eq (hA : IsIdempotented A) (z : NondegenerateModuleCenter.{uA, max uA uM} A)
    (M : NondegenerateModuleCat.{uA, max uA uM} A) (m : M.obj) (a : A) :
    (z.app M).hom.toAddMonoidHom (a • m) =
      ((z.app (NondegenerateModuleNaturalEndEvaluation.liftedRegularObject.{uA, uM} hA)).hom.toAddMonoidHom
        (ULift.up a)).down • m :=
  congrArg (fun f => f.hom.toAddMonoidHom (ULift.up a))
    (z.naturality (NondegenerateModuleNaturalEndClassificationProof.orbitMap hA M m))

/-- Class invariance of a scalar describing a centre element, along an isomorphism. -/
theorem scalar_of_iso [Module ℂ A] [IsScalarTower ℂ A A]
    (hA : IsIdempotented A) (z : NondegenerateModuleCenter.{uA, max uA uM} A)
    (M N : NondegenerateModuleCat.{uA, max uA uM} A) (f : M ≅ N) (c : ℂ)
    (hc : ∀ m : M.obj, (z.app M).hom.toAddMonoidHom m =
      NondegenerateScalars.scalarMul ℂ M.property c m) (n : N.obj) :
    (z.app N).hom.toAddMonoidHom n = NondegenerateScalars.scalarMul ℂ N.property c n := by
  have hn : f.hom.hom.toAddMonoidHom (f.inv.hom.toAddMonoidHom n) = n :=
    congrArg (fun g : N ⟶ N => g.hom.toAddMonoidHom n) f.inv_hom_id
  have hnat : (z.app N).hom.toAddMonoidHom (f.hom.hom.toAddMonoidHom (f.inv.hom.toAddMonoidHom n)) =
      f.hom.hom.toAddMonoidHom ((z.app M).hom.toAddMonoidHom (f.inv.hom.toAddMonoidHom n)) :=
    congrArg (fun g : M ⟶ N => g.hom.toAddMonoidHom (f.inv.hom.toAddMonoidHom n))
      (z.naturality f.hom)
  rw [← hn, hnat, hc]
  exact NondegenerateScalars.map_scalarMul ℂ hA M.property N.property f.hom.hom c _

end

/-- Renard I.1.8. -/
theorem centerScalarFunction : CenterScalarFunctionStatement.{uA, uM} := by
  intro A _ _ _ _ hA hrank IsSimple acts
  refine ⟨?_, ?_, ?_⟩
  · intro z M hM
    let _ := NondegenerateScalars.module ℂ hA M.property
    exact (Langlands.Renard.nonUnitalSchurScalarOfAlgebraRankCountable
      (NondegenerateScalars.toLinearEndHom ℂ hA M.property) hM hrank).2 (z.app M).hom
  · rintro z M N ⟨f⟩ _ _ c hc n
    exact scalar_of_iso hA z M N f c hc n
  · intro hsep
    refine ⟨?_, ?_⟩
    · intro x hx
      apply IdempotentedRingRightLimit.ext
      intro e
      apply Subtype.ext
      change x.val e = 0
      by_contra hxe
      obtain ⟨M, hMs, m, hm⟩ := hsep (x.val e) hxe
      have hfix : (e : A) • ((e : A) • m) = (e : A) • m := by
        rw [← mul_smul, e.property.eq]
      have h0 := hx M hMs ((e : A) • m)
      rw [IdempotentedRingRightLimitAction.act_eq hA M.property x _ e hfix, ← mul_smul,
        x.property.1 e] at h0
      exact hm h0
    · intro z z' hzz'
      let R := NondegenerateModuleNaturalEndEvaluation.liftedRegularObject.{uA, uM} hA
      have hR : ∀ e : Idempotent A,
          ((z.app R).hom.toAddMonoidHom (ULift.up (e : A))).down =
            ((z'.app R).hom.toAddMonoidHom (ULift.up (e : A))).down := by
        intro e
        rw [← sub_eq_zero]
        by_contra hd
        obtain ⟨M, hMs, m, hm⟩ := hsep _ hd
        apply hm
        have h := hzz' M hMs ((e : A) • m)
        change (z.app M).hom.toAddMonoidHom ((e : A) • m) =
          (z'.app M).hom.toAddMonoidHom ((e : A) • m) at h
        rw [app_smul_eq hA z M m (e : A), app_smul_eq hA z' M m (e : A)] at h
        rw [sub_smul, h, sub_self]
      apply CatCenter.ext
      intro M
      apply ObjectProperty.hom_ext
      apply NonUnitalModuleHom.ext
      intro m
      obtain ⟨e, he⟩ := M.property m
      change (z.app M).hom.toAddMonoidHom m = (z'.app M).hom.toAddMonoidHom m
      rw [← he, app_smul_eq hA z M m (e : A), app_smul_eq hA z' M m (e : A), hR e]

end CenterScalarFunctionProof
end Langlands.Algebra
