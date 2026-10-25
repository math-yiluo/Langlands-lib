import Langlands.Coefficients.AdicSystem
import Mathlib.LinearAlgebra.TensorProduct.Quotient

/-! # Tensor presentation of coefficient reductions and their inverse system -/

noncomputable section

namespace Langlands.Coefficients.AdicSystem

open CategoryTheory Opposite
open scoped TensorProduct ChangeOfRings

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {R : Type u} [CommRing R] (I : Ideal R)

/-- The tensor presentation as an isomorphism over the actual quotient ring. -/
def tensorReductionIso (M : ModuleCat.{u} R) :
    (ModuleCat.extendScalars (Ideal.Quotient.mk I)).obj M ≅ (reduction I).obj M :=
  ((TensorProduct.quotTensorEquivQuotSMul M I).extendScalarsOfSurjective
    (Ideal.Quotient.mk_surjective (I := I))).toModuleIso

@[simp] theorem tensorReductionIso_hom_mk_tmul (M : ModuleCat.{u} R) (r : R) (m : M) :
    (tensorReductionIso I M).hom (Ideal.Quotient.mk I r ⊗ₜ[R,Ideal.Quotient.mk I] m) =
      Submodule.Quotient.mk (r • m) :=
  TensorProduct.quotTensorEquivQuotSMul_mk_tmul I r m

@[simp] theorem tensorReductionIso_inv_mk (M : ModuleCat.{u} R) (m : M) :
    (tensorReductionIso I M).inv (Submodule.Quotient.mk m) =
      (1 : R ⧸ I) ⊗ₜ[R,Ideal.Quotient.mk I] m := rfl

/-- Scalar extension along the quotient map is naturally the quotient-module functor. -/
def tensorReduction : ModuleCat.extendScalars (Ideal.Quotient.mk I) ≅ reduction.{u, u} I :=
  NatIso.ofComponents (tensorReductionIso I) (by
    intro M N f
    apply ModuleCat.ExtendScalars.hom_ext
    intro m
    change (tensorReductionIso I N).hom ((1 : R ⧸ I) ⊗ₜ[R,Ideal.Quotient.mk I] f m) =
      (reduction I).map f ((tensorReductionIso I M).hom ((1 : R ⧸ I) ⊗ₜ[R,Ideal.Quotient.mk I] m))
    simp only [← map_one (Ideal.Quotient.mk I), tensorReductionIso_hom_mk_tmul, one_smul]
    rfl)

/-- After forgetting quotient scalars, a power reduction has the same actual quotient module. -/
def reductionRestrictIso (n : ℕ) :
    reduction (I ^ n) ⋙ ModuleCat.restrictScalars (Ideal.Quotient.mk (I ^ n)) ≅
      powerReduction.{u, u} I n :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by intros; rfl)

/-- The tensor presentation of a power reduction as an `R`-linear functor. -/
def tensorPowerIso (n : ℕ) :
    ModuleCat.extendScalars (Ideal.Quotient.mk (I ^ n)) ⋙
      ModuleCat.restrictScalars (Ideal.Quotient.mk (I ^ n)) ≅ powerReduction.{u, u} I n :=
  Functor.isoWhiskerRight (tensorReduction (I ^ n))
    (ModuleCat.restrictScalars (Ideal.Quotient.mk (I ^ n))) ≪≫ reductionRestrictIso I n

/-- The scalar-extension unit is the quotient map under the tensor presentation. -/
@[reassoc (attr := simp)] theorem tensorPowerIso_unit (n : ℕ) :
    (ModuleCat.extendRestrictScalarsAdj (Ideal.Quotient.mk (I ^ n))).unit ≫
      (tensorPowerIso I n).hom = quotientMap I n := by
  ext M m
  change TensorProduct.quotTensorEquivQuotSMul M (I ^ n) (1 ⊗ₜ[R] m) =
    Submodule.Quotient.mk m
  exact TensorProduct.quotTensorEquivQuotSMul_mk_one_tmul (I ^ n) m

/-- Power-level tensors, viewed as modules over the initial coefficient ring. -/
abbrev tensorPower (n : ℕ) : ModuleCat.{u} R ⥤ ModuleCat.{u} R :=
  ModuleCat.extendScalars (Ideal.Quotient.mk (I ^ n)) ⋙
    ModuleCat.restrictScalars (Ideal.Quotient.mk (I ^ n))

/-- The canonical transition on the tensor presentation, transported from the quotient map. -/
def tensorTransition {m n : ℕ} (h : m ≤ n) : tensorPower I n ⟶ tensorPower I m :=
  (tensorPowerIso I n).hom ≫ transition I h ≫ (tensorPowerIso I m).inv

/-- On pure tensors the transition applies the canonical quotient-ring map. -/
@[simp] theorem tensorTransition_tmul {m n : ℕ} (h : m ≤ n)
    (M : ModuleCat.{u} R) (a : R ⧸ I ^ n) (x : M) :
    (tensorTransition I h).app M (a ⊗ₜ[R,Ideal.Quotient.mk (I ^ n)] x) =
      Ideal.Quotient.factorPow I h a ⊗ₜ[R,Ideal.Quotient.mk (I ^ m)] x := by
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective a
  change (TensorProduct.quotTensorEquivQuotSMul M (I ^ m)).symm
    (Submodule.factorPow I M h
      (TensorProduct.quotTensorEquivQuotSMul M (I ^ n)
        (Ideal.Quotient.mk (I ^ n) r ⊗ₜ[R] x))) = _
  rw [TensorProduct.quotTensorEquivQuotSMul_mk_tmul]
  change (TensorProduct.quotTensorEquivQuotSMul M (I ^ m)).symm
    (Submodule.Quotient.mk (r • x)) = Ideal.Quotient.mk (I ^ m) r ⊗ₜ[R] x
  rw [TensorProduct.quotTensorEquivQuotSMul_symm_mk, ← TensorProduct.smul_tmul]
  change (Ideal.Quotient.mk (I ^ m) r * 1) ⊗ₜ[R] x = _
  rw [mul_one]

@[reassoc (attr := simp)] theorem tensorTransition_comparison {m n : ℕ} (h : m ≤ n) :
    tensorTransition I h ≫ (tensorPowerIso I m).hom =
      (tensorPowerIso I n).hom ≫ transition I h := by
  simp [tensorTransition]

@[simp] theorem tensorTransition_refl (n : ℕ) :
    tensorTransition I (le_refl n) = 𝟙 (tensorPower I n) := by
  simp [tensorTransition]

@[reassoc (attr := simp)] theorem tensorTransition_comp {l m n : ℕ}
    (h : l ≤ m) (k : m ≤ n) :
    tensorTransition I k ≫ tensorTransition I h = tensorTransition I (h.trans k) := by
  simp [tensorTransition]

/-- Tensor units are compatible with all inverse-system transitions. -/
@[reassoc (attr := simp)] theorem tensorTransition_unit {m n : ℕ} (h : m ≤ n) :
    (ModuleCat.extendRestrictScalarsAdj (Ideal.Quotient.mk (I ^ n))).unit ≫
      tensorTransition I h =
        (ModuleCat.extendRestrictScalarsAdj (Ideal.Quotient.mk (I ^ m))).unit := by
  apply (cancel_mono (tensorPowerIso I m).hom).mp
  rw [Category.assoc, tensorTransition_comparison, ← Category.assoc,
    tensorPowerIso_unit, quotientMap_transition, tensorPowerIso_unit]

/-- The actual inverse system of tensor coefficient functors. -/
def tensorPowers : ℕᵒᵖ ⥤ (ModuleCat.{u} R ⥤ ModuleCat.{u} R) where
  obj n := tensorPower I n.unop
  map f := tensorTransition I (leOfHom f.unop)
  map_id _ := tensorTransition_refl I _
  map_comp f g := (tensorTransition_comp I (leOfHom g.unop) (leOfHom f.unop)).symm

/-- Tensor and quotient presentations agree as inverse systems of functors. -/
def tensorPowersIso : tensorPowers I ≅ powers.{u, u} I :=
  NatIso.ofComponents (fun n => tensorPowerIso I n.unop) (by
    intro m n f
    exact tensorTransition_comparison I (leOfHom f.unop))

/-- Tensor coefficient inverse systems, functorially in the original module. -/
def tensorFunctor : ModuleCat.{u} R ⥤ (ℕᵒᵖ ⥤ ModuleCat.{u} R) :=
  (tensorPowers I).flip

/-- The pointwise quotient comparisons assemble naturally in modules and power indices. -/
def tensorFunctorIso : tensorFunctor I ≅ functor.{u, u} I :=
  NatIso.ofComponents (fun M => NatIso.ofComponents
    (fun n => (tensorPowerIso I n.unop).app M) (by
      intro m n f
      exact congrArg (fun a => a.app M) (tensorTransition_comparison I (leOfHom f.unop))))
    (by
      intro M N f
      apply NatTrans.ext
      funext n
      exact (tensorPowerIso I n.unop).hom.naturality f)

end Langlands.Coefficients.AdicSystem
