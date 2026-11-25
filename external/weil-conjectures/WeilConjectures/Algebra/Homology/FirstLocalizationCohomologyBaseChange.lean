/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.BaseDerivedTensorCohomologyModel
public import WeilConjectures.Algebra.Homology.RingTensorCohomology
public import Mathlib.RingTheory.Localization.Basic
import WeilConjectures.Algebra.Homology.LocalizationModelKernel
import WeilConjectures.Algebra.Homology.LocalizationModelDenominators
import Mathlib.RingTheory.Localization.BaseChange

/-! # Cohomology under localization of the first coefficient ring

Source: Stacks Project, More on Algebra, Tag 06Y6; perfect.tex, Tag 0DJ8.
(blueprint: lem-pc-first-localization-cohomology-base-change).
-/

@[expose] public section

set_option autoImplicit false

universe u w

open CategoryTheory
open scoped TensorProduct ChangeOfRings

attribute [local instance] Algebra.TensorProduct.rightAlgebra

namespace RingTensorCohomology

variable (R A Aq B D : Type u)
  [CommRing R] [CommRing A] [CommRing Aq] [CommRing B] [CommRing D]
  [Algebra R A] [Algebra R B] [Algebra A Aq] [Algebra R Aq]
  [IsScalarTower R A Aq]
  [Algebra (A ⊗[R] B) D] [Algebra (Aq ⊗[R] B) D]
  [HasDerivedCategory.{w} (ModuleCat.{u} R)]
  [HasDerivedCategory.{w} (ModuleCat.{u} B)]

/-- Cohomology localizes over the tensor coefficient ring, before further extension to D.
Source: Stacks Project, Tags 06Y6 and 0DJ8.
(blueprint: lem-pc-first-localization-cohomology-base-change).

Proof: take a K-flat R-resolution F of B[0] and compute the balanced derived tensor
of Q with F. Since F is K-flat over R, it preserves quasi-isomorphisms in Q; no
flatness of Q or A over R is required. Extension from A to Aq is exact, preserves
the direct sums in totalization, and commutes with the differentials. Thus the
localized balanced total complex is the balanced total complex of Aq tensor_A Q
with F. Exact scalar extension commutes with cohomology. Tensor associativity
identifies extension of its A-tensor_R-B cohomology to Aq-tensor_R-B with that
localized cohomology. A resolution F over R need not have a strict B-action:
use the balanced derived bifunctor to apply multiplication by b on B[0], then
transport that endomorphism through the K-flat computation isomorphism. Naturality
in the second derived variable makes the localization isomorphism commute with
these B-endomorphisms. It also commutes with the A-action termwise. The balanced
model and scalar-action naturality identify these commuting actions with the
usual B-linear derived tensor model and its derived A-action. Thus the isomorphism
is linear over Aq-tensor_R-B. Compare with L and K using the unique counit-compatible
isomorphisms of left derived functors; cohomologyIso_smul identifies their A-actions,
and B-linearity identifies their B-actions. The localization unit is uQ by its
termwise generator formula. Naturality of these comparisons then gives the displayed
formula. Equality on extension generators fixes the isomorphism uniquely. When S
contains zero both sides are zero; identity localization gives just model comparison.
D is only an index of the supplied models here: no compatibility of maps to D and
no tensor extension to D is used in this assertion. -/
theorem exists_firstLocalization_cohomology_baseChange
    (S : Submonoid A) [IsLocalization S Aq] (i : ℤ)
    (Q : CochainComplex (ModuleCat.{u} A) ℤ)
    (L : ModuleCat.BaseDerivedTensorCohomologyModel R A B Q D)
    (K : ModuleCat.BaseDerivedTensorCohomologyModel R Aq B ((extend A Aq).obj Q) D)
    (uQ : (restrict R A).obj Q ⟶ (restrict R Aq).obj ((extend A Aq).obj Q))
    (huQ : ∀ (j : ℤ) (x : Q.X j), uQ.f j x = (1 : Aq) ⊗ₜ[A,algebraMap A Aq] x) :
    letI := L.universal
    letI := K.universal
    let ζ := Functor.leftDerivedNatIso L.derived K.derived L.counit K.counit
      (HomotopyCategory.quasiIso (ModuleCat.{u} R) (.up ℤ)) (Iso.refl _)
    ∃ e : (ModuleCat.extendScalars
        (Algebra.TensorProduct.map (IsScalarTower.toAlgHom R A Aq)
          (AlgHom.id R B)).toRingHom).obj (L.cohomology i) ≅ K.cohomology i,
      ∀ x : L.cohomology i,
        e.hom ((1 : Aq ⊗[R] B) ⊗ₜ[A ⊗[R] B,
          (Algebra.TensorProduct.map (IsScalarTower.toAlgHom R A Aq)
            (AlgHom.id R B)).toRingHom] x) =
        ((L.cohomologyIso i).hom ≫
          (DerivedCategory.homologyFunctor (ModuleCat.{u} B) i).map
            (L.derived.map (DerivedCategory.Qh.map
              ((HomotopyCategory.quotient (ModuleCat.{u} R) (.up ℤ)).map uQ)) ≫
              ζ.hom.app (DerivedCategory.Qh.obj
                ((HomotopyCategory.quotient (ModuleCat.{u} R) (.up ℤ)).obj
                  ((restrict R Aq).obj ((extend A Aq).obj Q))))) ≫
          (K.cohomologyIso i).inv) x := by
  let φ := (Algebra.TensorProduct.map (IsScalarTower.toAlgHom R A Aq)
    (AlgHom.id R B)).toRingHom
  let : Algebra (A ⊗[R] B) (Aq ⊗[R] B) := φ.toAlgebra
  have ht : IsScalarTower A (A ⊗[R] B) (Aq ⊗[R] B) := by
    apply IsScalarTower.of_algebraMap_eq'
    ext a
    rw [RingHom.comp_apply, RingHom.algebraMap_toAlgebra]
    simp [φ]
  let := ht
  let T := Algebra.algebraMapSubmonoid (A ⊗[R] B) S
  have hloc : IsLocalization T (Aq ⊗[R] B) := by
    apply IsLocalization.tensorProduct_tensorProduct R B S Aq
    ext b
    rw [RingHom.comp_apply, RingHom.algebraMap_toAlgebra]
    simp [φ]
  let := hloc
  let N := (ModuleCat.restrictScalars φ).obj (K.cohomology i)
  let : Module (Aq ⊗[R] B) N :=
    inferInstanceAs (Module (Aq ⊗[R] B) (K.cohomology i))
  let : IsScalarTower (A ⊗[R] B) (Aq ⊗[R] B) N :=
    ⟨fun a b x ↦ mul_smul (φ a) b x⟩
  let c := localizationModelMap R A Aq B D i Q L K uQ
  let f : L.cohomology i →ₗ[A ⊗[R] B] N :=
    { toFun := c
      map_add' := c.hom.map_add
      map_smul' := fun a x ↦ localizationModelMap_smul R A Aq B D i Q L K uQ huQ a x }
  have hf : IsLocalizedModule T f := by
    refine ⟨?_, ?_, ?_⟩
    · intro s
      simpa only [AlgHom.commutes] using
        (IsLocalization.map_units (Aq ⊗[R] B) s).map
        (Algebra.lsmul (A ⊗[R] B) (A := Aq ⊗[R] B) (A ⊗[R] B) N)
    · intro y
      obtain ⟨x, s, hs⟩ :=
        localizationModelMap_denominators R A Aq B D S i Q L K uQ huQ y
      refine ⟨⟨x, ⟨algebraMap A (A ⊗[R] B) s, ?_⟩⟩, ?_⟩
      · exact ⟨s, s.property, rfl⟩
      · simpa [f, c, N, φ, Algebra.TensorProduct.map_tmul] using hs
    · intro x y hxy
      have hz : c (x - y) = 0 := by
        rw [map_sub, show c x = c y from hxy, sub_self]
      obtain ⟨s, hs⟩ := localizationModelMap_kernel R A Aq B D S i Q L K uQ huQ
        (x - y) hz
      refine ⟨⟨algebraMap A (A ⊗[R] B) s, ?_⟩, ?_⟩
      · exact ⟨s, s.property, rfl⟩
      · exact sub_eq_zero.mp (by simpa [Submonoid.smul_def, smul_sub] using hs)
  let := hf
  let e := (IsLocalizedModule.isBaseChange T (Aq ⊗[R] B) f).equiv
  refine ⟨e.toModuleIso, ?_⟩
  intro x
  change e ((1 : Aq ⊗[R] B) ⊗ₜ[A ⊗[R] B] x) = c x
  simp only [e, IsBaseChange.equiv_tmul, one_smul]
  rfl

end RingTensorCohomology
