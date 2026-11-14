import Langlands.Geometry.Building.KPZeroNormKernel
import Langlands.Galois.Local.SeparableUnramifiedArithmeticProof
import Langlands.Galois.Local.SpectralProof
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.TensorProduct.Pi

/-! # The valuation ring of a finite extension of the maximal unramified extension

Let `F` be a nonarchimedean local field, `K = inertiaFixedField F` and
`O = fixedFieldIntegers F`. For an intermediate field `L` of `F^sep / K`, the valuation ring
`O_L` of `intermediateValuation F L` is the integral closure of `O` in `L`. When `L / K` is
finite and Galois, `O_L` is a finite free `O`-module and `K ⊗[O] O_L ≃ L`. -/

noncomputable section

universe u

open Langlands.LocalGalois Langlands.LocalGalois.Separable Langlands.Geometry.Building
open scoped TensorProduct

namespace Langlands.BruhatTits.IntegralModels.ConnectedImage

set_option synthInstance.maxHeartbeats 100000

variable (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  (L : IntermediateField (inertiaFixedField F) (SeparableClosure F))

/-- The valuation ring `O_L` of `intermediateValuation F L`. -/
abbrev integers : ValuationSubring L := (intermediateValuation F L).valuationSubring

theorem mem_integers_iff (x : L) :
    x ∈ integers F L ↔ intermediateValuation F L x ≤ 1 :=
  Valuation.mem_valuationSubring_iff _ _

/-- An element of `L` is a unit of `O_L` exactly when it has valuation one. -/
theorem isUnit_integers_iff (x : integers F L) :
    IsUnit x ↔ intermediateValuation F L (x : L) = 1 := by
  constructor
  · intro h
    obtain ⟨y, hy⟩ := h.exists_right_inv
    have h1 : intermediateValuation F L (x : L) * intermediateValuation F L (y : L) = 1 := by
      rw [← map_mul]
      have : (x : L) * (y : L) = 1 := congrArg Subtype.val hy
      rw [this, map_one]
    have hx : intermediateValuation F L (x : L) ≤ 1 := x.property
    have hy' : intermediateValuation F L (y : L) ≤ 1 := y.property
    by_contra hne
    have hlt : intermediateValuation F L (x : L) < 1 := lt_of_le_of_ne hx hne
    have : intermediateValuation F L (x : L) * intermediateValuation F L (y : L) < 1 :=
      mul_lt_one_of_lt_of_le hlt hy'
    exact absurd h1 (ne_of_lt this)
  · intro h
    have hx0 : (x : L) ≠ 0 := by
      intro h0
      rw [h0, map_zero] at h
      exact zero_ne_one h
    refine IsUnit.of_mul_eq_one ⟨(x : L)⁻¹, ?_⟩ ?_
    · change intermediateValuation F L (x : L)⁻¹ ≤ 1
      rw [map_inv₀, h, inv_one]
    · apply Subtype.ext
      change (x : L) * (x : L)⁻¹ = 1
      exact mul_inv_cancel₀ hx0

/-- The algebra structure of `O` on `L`, through `K`. It is given explicitly, since instance
search through the valuation-subring and intermediate-field coercions is slow. -/
local instance (priority := high) integersAlgebraL : Algebra (fixedFieldIntegers F) L :=
  ((algebraMap (inertiaFixedField F) L).comp
    (algebraMap (fixedFieldIntegers F) (inertiaFixedField F))).toAlgebra

/-- The algebra structure of `O` on `F^sep`, through `K`. -/
local instance (priority := high) integersAlgebraSep :
    Algebra (fixedFieldIntegers F) (SeparableClosure F) :=
  ((algebraMap (inertiaFixedField F) (SeparableClosure F)).comp
    (algebraMap (fixedFieldIntegers F) (inertiaFixedField F))).toAlgebra

local instance (priority := high) integersTowerKL :
    IsScalarTower (fixedFieldIntegers F) (inertiaFixedField F) L :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

local instance (priority := high) integersTowerOL :
    IsScalarTower (fixedFieldIntegers F) (integers F L) L :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

local instance (priority := high) integersTowerSep :
    IsScalarTower (fixedFieldIntegers F) L (SeparableClosure F) :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

section Integral

local instance integersNormedField : NontriviallyNormedField F := localNormedField F
local instance integersUltrametric : IsUltrametricDist F := localNormedField_ultrametric F
local instance integersComplete : CompleteSpace F := localNormedField_complete F

/-- The base integers of the normed local field map to `O`. -/
def baseToFixedIntegers : baseIntegers F →+* fixedFieldIntegers F :=
  (integerToFixedField F).comp (RingEquiv.subringCongr (localNormedField_integer F)).toRingHom

/-- Every element of `O_L` is integral over `O`: it is integral over the integers of `F` by
the spectral-norm criterion. -/
theorem isIntegral_integers (x : integers F L) : IsIntegral (fixedFieldIntegers F) (x : L) := by
  have hmem : ((x : L) : SeparableClosure F) ∈ extensionIntegers F (SeparableClosure F) :=
    x.property
  have h1 : IsIntegral (baseIntegers F) ((x : L) : SeparableClosure F) :=
    spectral_integral F (SeparableClosure F) ⟨_, hmem⟩
  have h2 : IsIntegral (fixedFieldIntegers F) ((x : L) : SeparableClosure F) :=
    IsIntegral.map_of_comp_eq (S := SeparableClosure F) (U := SeparableClosure F)
      (baseToFixedIntegers F) (RingHom.id _) (RingHom.ext fun _ => rfl) h1
  let f : L →ₐ[fixedFieldIntegers F] SeparableClosure F :=
    IsScalarTower.toAlgHom (fixedFieldIntegers F) L (SeparableClosure F)
  exact (isIntegral_algHom_iff f (algebraMap L (SeparableClosure F)).injective).mp h2

/-- `O_L` is the integral closure of `O` in `L`. -/
instance isIntegralClosure : IsIntegralClosure (integers F L) (fixedFieldIntegers F) L where
  algebraMap_injective := Subtype.val_injective
  isIntegral_iff {x} := by
    constructor
    · intro hx
      exact IsIntegrallyClosed.algebraMap_eq_of_integral
        (hx.tower_top (A := integers F L))
    · rintro ⟨y, rfl⟩
      exact isIntegral_integers F L y

end Integral

section Finite

local instance integersDVR : IsDiscreteValuationRing (fixedFieldIntegers F) :=
  (separableUnramifiedArithmetic F).2.2.2.1

variable [FiniteDimensional (inertiaFixedField F) L] [IsGalois (inertiaFixedField F) L]

instance integers_finite : Module.Finite (fixedFieldIntegers F) (integers F L) :=
  IsIntegralClosure.finite (fixedFieldIntegers F) (inertiaFixedField F) L (integers F L)

instance integers_free : Module.Free (fixedFieldIntegers F) (integers F L) := by
  have : Module.IsTorsionFree (fixedFieldIntegers F) L :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr <| by
      change Function.Injective (⇑(algebraMap (inertiaFixedField F) L) ∘
        ⇑(algebraMap (fixedFieldIntegers F) (inertiaFixedField F)))
      exact (algebraMap (inertiaFixedField F) L).injective.comp
        (IsFractionRing.injective (fixedFieldIntegers F) (inertiaFixedField F))
  exact IsIntegralClosure.module_free (fixedFieldIntegers F) (inertiaFixedField F) L
    (integers F L)

instance integers_projective : Module.Projective (fixedFieldIntegers F) (integers F L) :=
  Module.Projective.of_free

/-- `L` is obtained from `O_L` by inverting the nonzero elements of `O`. -/
instance integers_isPushout :
    Algebra.IsPushout (fixedFieldIntegers F) (inertiaFixedField F) (integers F L) L := by
  have : IsLocalization (Algebra.algebraMapSubmonoid (integers F L)
      (nonZeroDivisors (fixedFieldIntegers F))) L :=
    IsIntegralClosure.isLocalization (fixedFieldIntegers F) (inertiaFixedField F) L
      (integers F L)
  exact (Algebra.isPushout_of_isLocalization (R := fixedFieldIntegers F)
    (A := inertiaFixedField F) (nonZeroDivisors (fixedFieldIntegers F))
    (integers F L) L).symm

/-- `K ⊗[O] O_L ≃ L`. -/
def tensorEquiv :
    inertiaFixedField F ⊗[fixedFieldIntegers F] integers F L ≃ₐ[inertiaFixedField F] L :=
  Algebra.IsPushout.equiv (fixedFieldIntegers F) (inertiaFixedField F) (integers F L) L

theorem tensorEquiv_tmul (a : inertiaFixedField F) (b : integers F L) :
    tensorEquiv F L (a ⊗ₜ b) = algebraMap (inertiaFixedField F) L a * (b : L) :=
  Algebra.IsPushout.equiv_tmul (fixedFieldIntegers F) (inertiaFixedField F) (integers F L) L a b

variable (I : Type u) [Fintype I] [DecidableEq I]

/-- `K ⊗[O] (I → O_L) ≃ (I → L)`. -/
def piTensorEquiv :
    inertiaFixedField F ⊗[fixedFieldIntegers F] (I → integers F L) ≃ₐ[inertiaFixedField F]
      (I → L) :=
  (Algebra.TensorProduct.piRight (fixedFieldIntegers F) (inertiaFixedField F)
    (inertiaFixedField F) (fun _ : I => integers F L)).trans
      (AlgEquiv.piCongrRight fun _ => tensorEquiv F L)

theorem piTensorEquiv_tmul (a : inertiaFixedField F) (b : I → integers F L) (i : I) :
    piTensorEquiv F L I (a ⊗ₜ b) i = algebraMap (inertiaFixedField F) L a * (b i : L) := by
  simp [piTensorEquiv, tensorEquiv_tmul]

end Finite

end Langlands.BruhatTits.IntegralModels.ConnectedImage
