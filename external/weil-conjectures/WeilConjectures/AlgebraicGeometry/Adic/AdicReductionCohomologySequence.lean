/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Integral.IntegralUniformCoefficient
public import WeilConjectures.AlgebraicGeometry.Bounded.BoundedConstructibleTowerSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.AlgebraicGeometry.Adic.AdicReductionTriangle
import all WeilConjectures.AlgebraicGeometry.CompletedConstantReduction.CompletedConstantSheafReductionSupplement
import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvr
import Mathlib.Algebra.Order.AbsoluteValue.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Localization.FractionRing
import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrCore
import Mathlib.Analysis.Normed.Algebra.Ultra
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.NumberTheory.Padics.ProperSpace
import Mathlib.Topology.Algebra.Valued.LocallyCompact
import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrFactorization
import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrFactorizationUnique
import WeilConjectures.Mathlib.RingTheory.OrderOfVanishing.Noetherian
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

set_option linter.privateModule false

/-! # The cohomology sequence for a completed DVR quotient

Source: blueprint integral truncations, hypothesis paragraph, and the quotient-resolution
argument in steps 1 and 3 of lem-weil-pbc-adic-tor-flat-cohomology.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u
open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

private theorem uniformizer_ne_zero (l : ℕ) [Fact l.Prime]
    (E : Type (u + 1)) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] : Padic.coefficientExtensionUniformizer l E ≠ 0 := by
  let A := Padic.coefficientExtensionIntegers l E
  let π := Padic.coefficientExtensionUniformizer l E
  have h := (Padic.coefficientExtensionIntegers_dvr l E).choose_spec
  let : IsDiscreteValuationRing A := h.2.2.2.2.2.2.2.1
  have hgen : Ideal.span ({π} : Set A) = Padic.coefficientExtensionMaximalIdeal l E :=
    h.2.2.2.2.2.2.2.2.2.2.2.2.2.1.choose_spec
  have hm : Padic.coefficientExtensionMaximalIdeal l E = IsLocalRing.maximalIdeal A :=
    IsLocalRing.eq_maximalIdeal h.2.2.2.2.1
  exact ((IsDiscreteValuationRing.irreducible_iff_uniformizer π).2
    (hm.symm.trans hgen.symm)).ne_zero

private theorem principal_scalar_sequence {A : Type*} [CommRing A] [IsDomain A]
    (a : A) (ha : a ≠ 0) :
    let μ := ModuleCat.ofHom (LinearMap.mulLeft A a)
    let p := ModuleCat.ofHom ((Ideal.Quotient.mkₐ A (Ideal.span {a})).toLinearMap)
    ∃ h : μ ≫ p = 0, (ShortComplex.mk μ p h).ShortExact := by
  dsimp only
  have h : ModuleCat.ofHom (LinearMap.mulLeft A a) ≫
      ModuleCat.ofHom ((Ideal.Quotient.mkₐ A (Ideal.span {a})).toLinearMap) = 0 := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change Ideal.Quotient.mk (Ideal.span {a}) (a * x) = 0
    exact Ideal.Quotient.eq_zero_iff_mem.mpr
      (Ideal.mul_mem_right _ _ (Ideal.subset_span (Set.mem_singleton a)))
  refine ⟨h, ModuleCat.shortComplex_shortExact _ ?_ ?_ ?_⟩
  · intro x
    change Ideal.Quotient.mk (Ideal.span {a}) x = 0 ↔ _
    rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
    constructor
    · rintro ⟨y, hy⟩
      exact ⟨y, hy.symm⟩
    · rintro ⟨y, hy⟩
      exact ⟨y, hy.symm⟩
  · intro x y hxy
    exact mul_left_cancel₀ ha hxy
  · exact Ideal.Quotient.mk_surjective

private abbrev constantPresheaves (T : Scheme.{u}) (A : Type (u + 1)) [CommRing A] :=
  siteConstantModulePresheaf (C := Discrete (ULift.{u + 1} Unit)) A ⋙
    PresheafOfModules.pushforward₀
      ((Functor.const T.ProEt).obj (Discrete.mk (ULift.up ())))
      ((Functor.const (Discrete (ULift.{u + 1} Unit))ᵒᵖ).obj (RingCat.of A))

private def constantGenerator (T : Scheme.{u}) {A : Type (u + 1)} [CommRing A]
    (M : ModuleCat.{u + 1} A) (U : T.ProEtᵒᵖ) (x : M) :
    ((adicLisseConstantModules T A).obj M).val.obj U :=
  ((PresheafOfModules.sheafificationAdjunction.{u + 1}
    (adicLisseConstantUnit T A)).unit.app ((constantPresheaves T A).obj M)).app U x

private theorem constantGenerator_naturality (T : Scheme.{u})
    {A : Type (u + 1)} [CommRing A] {M N : ModuleCat.{u + 1} A} (g : M ⟶ N)
    (U : T.ProEtᵒᵖ) (x : M) :
    ((adicLisseConstantModules T A).map g).val.app U (constantGenerator T M U x) =
      constantGenerator T N U (g x) := by
  exact (congrArg (fun k ↦ k.app U x)
    ((PresheafOfModules.sheafificationAdjunction.{u + 1}
      (adicLisseConstantUnit T A)).unit.naturality
      ((constantPresheaves T A).map g))).symm

open scoped ChangeOfRings in
set_option backward.isDefEq.respectTransparency false in
private theorem constant_unit_inv_one (T : Scheme.{u})
    {A : Type (u + 1)} [CommRing A]
    {S : Sheaf (ProEt.topology T) CommRingCat.{u + 1}}
    (c : adicLisseConstantRing T A ⟶ S) (U : T.ProEtᵒᵖ) :
    (CompletedConstantReduction.constantChange_unit T c).inv.val.app U (1 : S.obj.obj U) =
      completedAdicChangeTensor T c ((adicLisseConstantModules T A).obj (ModuleCat.of A A))
        U 1 (constantGenerator T (ModuleCat.of A A) U 1) := by
  unfold CompletedConstantReduction.constantChange_unit
  simp only [Iso.trans_inv, eqToIso.inv, SheafOfModules.comp_val,
    PresheafOfModules.comp_app, ModuleCat.comp_apply]
  change (eqToHom ((completedAdicChangeData T c).choose_spec.choose
    ((adicLisseConstantModules T A).obj (ModuleCat.of A A))).symm).val.app U
      ((1 : S.obj.obj U) •
        (show (SheafOfModules.changeOfRings c
          ((adicLisseConstantModules T A).obj (ModuleCat.of A A))).val.obj U from
        ((toSheafify (ProEt.topology T)
          (SheafOfModules.changeOfRingsPresheaf c
            ((adicLisseConstantModules T A).obj (ModuleCat.of A A))).presheaf).app U
              ((1 : S.obj.obj U) ⊗ₜ[(adicLisseConstantRing T A).obj.obj U,
                (c.hom.app U).hom] (constantGenerator T (ModuleCat.of A A) U 1))))) = _
  exact congrArg ((eqToHom ((completedAdicChangeData T c).choose_spec.choose
    ((adicLisseConstantModules T A).obj (ModuleCat.of A A))).symm).val.app U)
      (one_smul (S.obj.obj U)
        (show (SheafOfModules.changeOfRings c
          ((adicLisseConstantModules T A).obj (ModuleCat.of A A))).val.obj U from
          (toSheafify (ProEt.topology T)
            (SheafOfModules.changeOfRingsPresheaf c
              ((adicLisseConstantModules T A).obj (ModuleCat.of A A))).presheaf).app U
                ((1 : S.obj.obj U) ⊗ₜ[(adicLisseConstantRing T A).obj.obj U,
                  (c.hom.app U).hom] (constantGenerator T (ModuleCat.of A A) U 1))))

set_option backward.isDefEq.respectTransparency false in
private theorem completed_map_tensor_one (T : Scheme.{u})
    {R S : Sheaf (ProEt.topology T) CommRingCat.{u + 1}} (φ : R ⟶ S)
    {M N : pbcModules T R} (g : M ⟶ N) (U : T.ProEtᵒᵖ) (x : M.val.obj U) :
    ((completedAdicChange T φ).map g).val.app U
        (completedAdicChangeTensor T φ M U 1 x) =
      completedAdicChangeTensor T φ N U 1 (g.val.app U x) := by
  have h := congrArg (fun k ↦ k.val.app U x) ((pbcScalarAdjunction φ).unit.naturality g)
  change ((pbcScalarAdjunction φ).unit.app N).val.app U (g.val.app U x) =
    ((completedAdicChange T φ).map g).val.app U
      (((pbcScalarAdjunction φ).unit.app M).val.app U x) at h
  have hM : ((pbcScalarAdjunction φ).unit.app M).val.app U x =
      completedAdicChangeTensor T φ M U 1 x :=
    (pbcScalarAdjunction_exists φ).exists.choose_spec M U x
  have hN : ((pbcScalarAdjunction φ).unit.app N).val.app U (g.val.app U x) =
      completedAdicChangeTensor T φ N U 1 (g.val.app U x) :=
    (pbcScalarAdjunction_exists φ).exists.choose_spec N U (g.val.app U x)
  exact (congrArg (fun y ↦ ((completedAdicChange T φ).map g).val.app U y) hM.symm).trans
    (h.symm.trans hN)

private theorem exact_transport
    {C : Type*} [Category C] [Abelian C]
    {X Y Z X' Y' Z' : C} (a : X ⟶ Y) (b : Y ⟶ Z)
    (a' : X' ⟶ Y') (b' : Y' ⟶ Z') (h : a ≫ b = 0) (h' : a' ≫ b' = 0)
    (eX : X ≅ X') (eY : Y ≅ Y') (eZ : Z ≅ Z')
    (ha : eX.hom ≫ a' = a ≫ eY.hom)
    (hb : eY.hom ≫ b' = b ≫ eZ.hom)
    (hex : (ShortComplex.mk a b h).Exact) :
    (ShortComplex.mk a' b' h').Exact := by
  let g : (ShortComplex.mk a b h) ⟶ (ShortComplex.mk a' b' h') :=
    { τ₁ := eX.hom
      τ₂ := eY.hom
      τ₃ := eZ.hom
      comm₁₂ := ha
      comm₂₃ := hb }
  exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono g).mp hex

end AlgebraicGeometry.Scheme
