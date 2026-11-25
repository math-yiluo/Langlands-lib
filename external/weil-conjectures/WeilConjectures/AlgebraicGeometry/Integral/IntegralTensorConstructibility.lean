/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
public import WeilConjectures.AlgebraicGeometry.AdicCompletion.DerivedCompletionSupplement
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index

import all WeilConjectures.AlgebraicGeometry.Integral.IntegralTensorShriek
import all WeilConjectures.AlgebraicGeometry.IntegralLfpConstantModelComparison
import all WeilConjectures.AlgebraicGeometry.Integral.IntegralCriterionReductionsSupplement
import all WeilConjectures.AlgebraicGeometry.Integral.Constant.IntegralConstantModelHeartClosureSupplement
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Bounded.BoundedConstructibleTensorPreservation
import WeilConjectures.AlgebraicGeometry.Bounded.BoundedConstructibleDevissageSupplement
import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Equivalence
import WeilConjectures.CategoryTheory.ModuleObjects.MapModMonoidal

/-! # Constructibility of the ordinary integral tensor

This separates the constructibility clause from local duality and limit preservation.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

attribute [local irreducible] upperStarFromPoint DerivedCategory.TStructure.t

private noncomputable def pointIntegerIso
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] :
    Mon.mk (integralCondensedRing l E) ≅ Mon.mk (DerivedNakayama.integerRing l E) := by
  letI := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
  let e : latticeCoefficientIntegers l E ≃+* Padic.coefficientExtensionIntegers l E :=
    RingEquiv.restrict (WithAbs.equiv (Padic.coefficientExtensionAbsoluteValue l E))
      _ _ (fun _ ↦ Iff.rfl)
  have he : Isometry e := by
    apply AddMonoidHomClass.isometry_of_norm e
    intro x
    rfl
  have hi : Isometry e.symm := by
    intro x y
    simpa only [e.apply_symm_apply] using (he (e.symm x) (e.symm y)).symm
  let c : Profinite.continuousMapRingSheafOfUniverse (latticeCoefficientIntegers l E) ≅
      DerivedNakayama.integerRingSheaf l E :=
    { hom := ⟨{
        app := fun S ↦ RingCat.ofHom
          (ULift.ringEquiv.symm.toRingHom.comp
            ((e.toRingHom.compLeftContinuous S.unop he.continuous).comp
              ULift.ringEquiv.toRingHom))
        naturality := fun _ _ _ ↦ rfl }⟩
      inv := ⟨{
        app := fun S ↦ RingCat.ofHom
          (ULift.ringEquiv.symm.toRingHom.comp
            ((e.symm.toRingHom.compLeftContinuous S.unop hi.continuous).comp
              ULift.ringEquiv.toRingHom))
        naturality := fun _ _ _ ↦ rfl }⟩
      hom_inv_id := by
        ext S f
        apply ULift.ext
        apply ContinuousMap.ext
        intro x
        exact e.symm_apply_apply _
      inv_hom_id := by
        ext S f
        apply ULift.ext
        apply ContinuousMap.ext
        intro x
        exact e.apply_symm_apply _ }
  let cAb := (sheafCompose (coherentTopology Profinite.{u})
    (forget₂ RingCat.{u + 1} Ab.{u + 1})).mapIso c
  have : IsMonHom cAb.hom := Sheaf.isMonHom_sheafCompose_map _ c.hom
  have : IsMonHom cAb.inv := Sheaf.isMonHom_sheafCompose_map _ c.inv
  exact
    { hom := Mon.ofHom cAb.hom
      inv := Mon.ofHom cAb.inv
      hom_inv_id := by apply Mon.Hom.ext; exact cAb.hom_inv_id
      inv_hom_id := by apply Mon.Hom.ext; exact cAb.inv_hom_id }

attribute [local irreducible] pointIntegerIso

private theorem integer_models
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (X : Scheme.{u}) [EssentiallySmall.{u + 1} X.ProEt] [IsNoetherian X]
    (M : AdicCompletion.Modules l E X)
    (hM : IsConstructibleModuleObject (AdicCompletion.ring l E X) M) :
    IsConstantModelConstructible (DerivedNakayama.integerRing l E) X M := by
  let e := pointIntegerIso l E
  let φ := e.hom.hom
  let ψ := coefficientMap φ X
  have h := integralLfpConstantModelComparison l E X ((Mod.comap ψ).obj M)
  exact (constantModel_comap_iff φ X M).mp
    (h.mp (_root_.constructible_comap ψ hM))

private theorem integerConstructibleComparison
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (X : Scheme.{u}) [IsNoetherian X]
    (M : AdicCompletion.Modules l E X) :
    IsConstructibleModuleObject (AdicCompletion.ring l E X) M ↔
      IsConstantModelConstructible (DerivedNakayama.integerRing l E) X M := by
  have : EssentiallySmall.{u + 1} X.ProEt := essentiallySmallSelf.{0} _
  constructor
  · exact integer_models.{u} l E X M
  · intro h
    have hqcqs : CompactSpace X ∧ QuasiSeparatedSpace X := ⟨inferInstance, inferInstance⟩
    rw [IsConstantModelConstructible, ite_eq_left hqcqs] at h
    exact constructible_of_finiteConstantStratified.{u} _ X M h

private theorem boundedConstructible_comap
    {X : Scheme.{u}} {R S : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}}
    [MonObj R] [IsCommMonObj R] [MonObj S] [IsCommMonObj S]
    (φ : R ⟶ S) [IsMonHom φ] [IsIso φ]
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) S))
    (hK : boundedConstructible S K) :
    boundedConstructible R ((Mod.comap φ).mapDerivedCategory.obj K) := by
  refine ⟨(Mod.comap φ).bounded_mapDerivedCategory_obj hK.1, fun n ↦ ?_⟩
  exact _root_.constructible_of_iso
    (((Mod.comap φ).mapDerivedCategoryHomologyFunctorIso n).app K)
    (_root_.constructible_comap φ (hK.2 n))

/-- Ordinary integral derived tensor preserves the finite constant-model constructible category.
-/
theorem integralTensorConstructibility
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (k : Type u) [Field k] (p : ℕ) [CharP k p] (_hp : 0 < p) (_hpl : p ≠ l) :
    ∀ (X : Scheme.{u}) [X.Over (Spec (.of k))]
      [IsSeparated (X ↘ Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]
      [QuasiCompact (X ↘ Spec (.of k))]
      (K L : DerivedCategory (AdicCompletion.Modules l E X)),
      constantModelBoundedConstructible (DerivedNakayama.integerRing l E) X K →
      constantModelBoundedConstructible (DerivedNakayama.integerRing l E) X L →
      constantModelBoundedConstructible (DerivedNakayama.integerRing l E) X (K ⊗ L) := by
  intro X _ _ _ _ K L hK hL
  have : EssentiallySmall.{u + 1} X.ProEt := essentiallySmallSelf.{0} _
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian
    (X ↘ Spec (.of k))
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace
    (X ↘ Spec (.of k))
  have : IsNoetherian X := ⟨⟩
  have : Fact (ringChar k ≠ l) := ⟨by simpa only [ringChar.eq k p] using _hpl⟩
  have hcmp (N : DerivedCategory (AdicCompletion.Modules l E X)) :
      boundedConstructible (AdicCompletion.ring l E X) N ↔
        constantModelBoundedConstructible (DerivedNakayama.integerRing l E) X N :=
    and_congr Iff.rfl (forall_congr' fun n ↦ integerConstructibleComparison l E X _)
  obtain ⟨F, nf, na, fd, ⟨e⟩⟩ := coefficientSmallIso l E
  let := nf
  let := na
  let := fd
  let e₀ : Mon.mk (DerivedNakayama.integerRing l E) ≅
      Mon.mk (integralModelCondensedCoefficients l E).X :=
    eqToIso (integralPointMon_eq l E)
  let e' := e₀ ≪≫ e
  let φ : AdicCompletion.ring l E X ⟶ condensedRingObj (CondensedRing.integralCoeff l F) X :=
    (upperStarFromPoint X).map e'.hom.hom
  have : IsMonHom e'.hom.hom := inferInstance
  have : IsMonHom φ := inferInstance
  have : IsIso φ := inferInstance
  let G : AdicCompletion.Modules l E X ⥤
      Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (condensedRingObj (CondensedRing.integralCoeff l F) X) := Mod.comap (inv φ)
  have : G.IsEquivalence := (Mod.comapEquivalenceOfIsIso (inv φ)).isEquivalence_functor
  let Xk : Over (Spec (.of k)) := Over.mk (X ↘ Spec (.of k))
  have : LocallyOfFiniteType Xk.hom := inferInstanceAs
    (LocallyOfFiniteType (X ↘ Spec (.of k)))
  have : QuasiCompact Xk.hom := inferInstanceAs (QuasiCompact (X ↘ Spec (.of k)))
  have : IsSeparated Xk.hom := inferInstanceAs (IsSeparated (X ↘ Spec (.of k)))
  have : Fact (∀ x : F, x ∈ CondensedRing.continuousIntegers l F ↔ ‖x‖ ≤ 1) :=
    ⟨fun x ↦ NNReal.coe_le_coe.symm⟩
  have hT := CondensedRing.UnitBallRingObj.boundedConstructible_tensor_closure (X := Xk) l
    (CondensedRing.continuousIntegers l F)
    (G.mapDerivedCategory.obj K) (G.mapDerivedCategory.obj L)
    (boundedConstructible_comap (inv φ) K ((hcmp K).mpr hK))
    (boundedConstructible_comap (inv φ) L ((hcmp L).mpr hL))
  have ht : boundedConstructible (condensedRingObj (CondensedRing.integralCoeff l F) X)
      (G.mapDerivedCategory.obj (K ⊗ L)) :=
    ObjectProperty.prop_of_iso _
      ((DerivedCategory.tensorLeftCompMapDerivedCategoryIso.{u + 1, u + 1} G K).app L).symm hT
  apply (hcmp _).mp
  refine ⟨G.bounded_of_bounded_mapDerivedCategory_obj ht.1, fun n ↦ ?_⟩
  have hn := _root_.constructible_of_iso
    (((G.mapDerivedCategoryHomologyFunctorIso n).app (K ⊗ L)).symm) (ht.2 n)
  have hh := _root_.constructible_comap φ hn
  exact _root_.constructible_of_iso
    ((Mod.comapEquivalenceOfIsIso φ).counitIso.app
      ((DerivedCategory.homologyFunctor _ n).obj (K ⊗ L))) hh

end AlgebraicGeometry.ProEtale
