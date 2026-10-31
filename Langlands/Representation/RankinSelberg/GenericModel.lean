import Langlands.Representation.RankinSelberg.WhittakerTypeFromMultiplicityProof
import Langlands.Representation.RankinSelberg.WhittakerTypeEquivalence
import Langlands.Representation.RankinSelberg.WhittakerGammaAdapters
import Langlands.Representation.Whittaker.MultiplicityOneProof

/-!
# Intrinsic Whittaker models of generic representations

The existing all-functional Whittaker set is made into an actual
subrepresentation. For p-adic generic representations the full Whittaker-type
hypothesis follows from the published multiplicity theorem.
-/

noncomputable section

namespace Langlands.RankinSelberg

open Whittaker HarmonicAnalysis GeneralLinear

universe uF uV

section IntrinsicModel

variable {F : Type uF} [Field F] [TopologicalSpace F]
  {n : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {ψ : UnitaryAdditiveCharacter F}
  {π : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V}

/-- The intrinsic model: its vectors are exactly the functions in the existing
all-functional Whittaker set. No functional is selected in this definition. -/
def whittakerModel (hπ : IsOfWhittakerType n (standardCharacter ψ n) π) :
    Subrepresentation (functionRepresentation (upperUnipotent (n + 1) F)
      (standardCharacter ψ n)) where
  toSubmodule :=
    { carrier := whittakerSet ψ n π
      zero_mem' := ⟨0, (coefficientModel π 0).toSubmodule.zero_mem⟩
      add_mem' := by
        intro W W' hW hW'
        obtain ⟨ℓ, hℓ⟩ := hπ.exists_ne_zero
        rw [whittakerSet_eq_coefficientModel ℓ (hπ.eq_smul hℓ)] at hW hW' ⊢
        exact (coefficientModel π ℓ).toSubmodule.add_mem hW hW'
      smul_mem' := by
        intro c W hW
        obtain ⟨ℓ, hℓ⟩ := hπ.exists_ne_zero
        rw [whittakerSet_eq_coefficientModel ℓ (hπ.eq_smul hℓ)] at hW ⊢
        exact (coefficientModel π ℓ).toSubmodule.smul_mem c hW }
  apply_mem_toSubmodule := by
    rintro g W ⟨ℓ, hW⟩
    exact ⟨ℓ, (coefficientModel π ℓ).apply_mem_toSubmodule g hW⟩

@[simp] theorem mem_whittakerModel
    (hπ : IsOfWhittakerType n (standardCharacter ψ n) π)
    (W : WhittakerFunctions ψ n) :
    W ∈ whittakerModel hπ ↔ W ∈ whittakerSet ψ n π := Iff.rfl

/-- Every nonzero functional gives exactly the intrinsic model. -/
theorem whittakerModel_eq_coefficientModel
    (hπ : IsOfWhittakerType n (standardCharacter ψ n) π)
    (ℓ : glFunctionals ψ n π) (hℓ : ℓ.val ≠ 0) :
    whittakerModel hπ = coefficientModel π ℓ := by
  apply Subrepresentation.toSubmodule_injective
  apply SetLike.coe_injective
  exact whittakerSet_eq_coefficientModel ℓ (hπ.eq_smul hℓ)

/-- Right translation on the intrinsic function model. -/
def whittakerModelRepresentation
    (hπ : IsOfWhittakerType n (standardCharacter ψ n) π) :
    Representation ℂ (Langlands.GeneralLinear (n + 1) F)
      (whittakerModel hπ).toSubmodule :=
  (whittakerModel hπ).toRepresentation

/-- Evaluation as an actual complex-valued function on the matrix group. -/
def whittakerModelFunction
    (hπ : IsOfWhittakerType n (standardCharacter ψ n) π)
    (W : (whittakerModel hπ).toSubmodule) :
    Langlands.GeneralLinear (n + 1) F → ℂ := W.val.val

@[simp] theorem whittakerModelFunction_translate
    (hπ : IsOfWhittakerType n (standardCharacter ψ n) π)
    (W : (whittakerModel hπ).toSubmodule)
    (s g : Langlands.GeneralLinear (n + 1) F) :
    whittakerModelFunction hπ (whittakerModelRepresentation hπ s W) g =
      whittakerModelFunction hπ W (g * s) := rfl

theorem whittakerModelFunction_equivariance
    (hπ : IsOfWhittakerType n (standardCharacter ψ n) π)
    (W : (whittakerModel hπ).toSubmodule)
    (u : upperUnipotent (n + 1) F) (g : Langlands.GeneralLinear (n + 1) F) :
    whittakerModelFunction hπ W (u.val * g) =
      (standardCharacter ψ n u : ℂ) * whittakerModelFunction hπ W g :=
  W.val.property u g

/-- The actual orbit-function intertwiner into the intrinsic model. -/
def whittakerModelMap
    (hπ : IsOfWhittakerType n (standardCharacter ψ n) π)
    (ℓ : glFunctionals ψ n π) :
    π.IntertwiningMap (whittakerModelRepresentation hπ) where
  toLinearMap := (coefficientMap π ℓ).toLinearMap.codRestrict
    (whittakerModel hπ).toSubmodule (fun v => ⟨ℓ, ⟨v, rfl⟩⟩)
  isIntertwining' g := by
    ext v x
    change ℓ.val (π x (π g v)) = ℓ.val (π (x * g) v)
    rw [map_mul, Module.End.mul_apply]

@[simp] theorem whittakerModelMap_apply
    (hπ : IsOfWhittakerType n (standardCharacter ψ n) π)
    (ℓ : glFunctionals ψ n π) (v : V) (g : Langlands.GeneralLinear (n + 1) F) :
    whittakerModelFunction hπ (whittakerModelMap hπ ℓ v) g = ℓ.val (π g v) := rfl

/-- A nonzero functional maps onto the whole intrinsic model. -/
theorem whittakerModelMap_surjective
    (hπ : IsOfWhittakerType n (standardCharacter ψ n) π)
    (ℓ : glFunctionals ψ n π) (hℓ : ℓ.val ≠ 0) :
    Function.Surjective (whittakerModelMap hπ ℓ) := by
  intro W
  have hW : W.val ∈ (coefficientModel π ℓ).toSubmodule := by
    rw [← whittakerModel_eq_coefficientModel hπ ℓ hℓ]
    exact W.property
  obtain ⟨v, hv⟩ := hW
  exact ⟨v, Subtype.ext hv⟩

/-- The intrinsic right-translation action is smooth, including when the
original representation of Whittaker type is reducible. -/
theorem whittakerModel_isSmooth
    (hπ : IsOfWhittakerType n (standardCharacter ψ n) π) :
    IsSmooth (V := (whittakerModel hπ).toSubmodule) (whittakerModelRepresentation hπ) := by
  intro W
  obtain ⟨ℓ, hℓ⟩ := hπ.exists_ne_zero
  obtain ⟨v, rfl⟩ := whittakerModelMap_surjective hπ ℓ hℓ W
  obtain ⟨K, hK⟩ := hπ.1.1 v
  refine ⟨K, ?_⟩
  intro k
  change whittakerModelRepresentation hπ (k : Langlands.GeneralLinear (n + 1) F)
    (whittakerModelMap hπ ℓ v) = whittakerModelMap hπ ℓ v
  rw [← (whittakerModelMap hπ ℓ).isIntertwining]
  exact congrArg (whittakerModelMap hπ ℓ) (hK k)

/-- For an irreducible representation, the intrinsic model realizes the
original representation. The functional normalizes this equivalence only. -/
def whittakerModelEquiv [Representation.IsIrreducible π]
    (hπ : IsOfWhittakerType n (standardCharacter ψ n) π)
    (ℓ : glFunctionals ψ n π) (hℓ : ℓ.val ≠ 0) :
    π.Equiv (whittakerModelRepresentation hπ) := by
  refine (whittakerModelMap hπ ℓ).ofBijective ⟨?_, whittakerModelMap_surjective hπ ℓ hℓ⟩
  intro v w hvw
  have hmodel : modelMap π ℓ v = modelMap π ℓ w :=
    Subtype.ext (congrArg (fun W : (whittakerModel hπ).toSubmodule => W.val) hvw)
  exact (modelEquiv π ℓ hℓ).toLinearEquiv.injective hmodel

/-- The intrinsic realization has all three clauses of full Whittaker type. -/
theorem whittakerModel_isOfWhittakerType [Representation.IsIrreducible π]
    (hπ : IsOfWhittakerType n (standardCharacter ψ n) π) :
    IsOfWhittakerType (V := (whittakerModel hπ).toSubmodule)
      n (standardCharacter ψ n) (whittakerModelRepresentation hπ) := by
  obtain ⟨ℓ, hℓ⟩ := hπ.exists_ne_zero
  exact hπ.of_equiv (whittakerModelEquiv hπ ℓ hℓ)

/-- Every intrinsic model function is locally constant, using only
admissibility's smoothness clause and its actual coefficient preimage. -/
theorem whittakerModelFunction_isLocallyConstant [IsTopologicalRing F]
    (hπ : IsOfWhittakerType n (standardCharacter ψ n) π)
    (W : (whittakerModel hπ).toSubmodule) :
    IsLocallyConstant (whittakerModelFunction hπ W) := by
  obtain ⟨ℓ, v, hv⟩ := W.property
  have hfun : whittakerModelFunction hπ W = fun g => ℓ.val (π g v) :=
    congrArg Subtype.val hv.symm
  rw [hfun]
  exact Langlands.matrixCoefficient_isLocallyConstant π ℓ.val v (hπ.1.1 v)

/-- Intrinsic model functions are continuous for the usual complex topology. -/
theorem whittakerModelFunction_continuous [IsTopologicalRing F]
    (hπ : IsOfWhittakerType n (standardCharacter ψ n) π)
    (W : (whittakerModel hπ).toSubmodule) :
    Continuous (whittakerModelFunction hπ W) :=
  (whittakerModelFunction_isLocallyConstant hπ W).continuous

end IntrinsicModel

section PadicGeneric

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance : NontriviallyNormedField F.Carrier := F.canonicalNormedField

variable {n : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {ψ : UnitaryAdditiveCharacter F.Carrier}
  {π : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) V}

/-- Genericity over a p-adic field supplies full Whittaker type: scalar
multiplicity is proved by the published theorem, rather than assumed. -/
theorem isOfWhittakerType_of_isGeneric (hπ : Whittaker.IsGeneric ψ n π) :
    IsOfWhittakerType n (standardCharacter ψ n) π := by
  obtain ⟨ℓ, hℓ⟩ := hπ.2.2
  apply whittakerTypeFromMultiplicity F.Carrier n (standardCharacter ψ n) V π hπ.1 hπ.2.1
  refine ⟨ℓ, hℓ, ?_⟩
  intro ℓ'
  exact (multiplicityOne p inferInstance F n V ψ π hπ.2.1 hπ.1 ℓ ℓ' hℓ).exists

/-- A generic p-adic representation also has full inverse-character type,
as required for the second member of a JPSS pair. -/
theorem isOfInverseWhittakerType_of_isGeneric (hπ : Whittaker.IsGeneric ψ n π) :
    IsOfWhittakerType n (inverseStandardCharacter ψ n) π :=
  (isOfWhittakerType_standard_iff_inverse ψ π).mp (isOfWhittakerType_of_isGeneric F hπ)

/-- The actual intrinsic function model of a generic p-adic representation. -/
def genericModel (hπ : Whittaker.IsGeneric ψ n π) :
    Subrepresentation (functionRepresentation (upperUnipotent (n + 1) F.Carrier)
      (standardCharacter ψ n)) :=
  whittakerModel (isOfWhittakerType_of_isGeneric F hπ)

@[simp] theorem mem_genericModel (hπ : Whittaker.IsGeneric ψ n π)
    (W : WhittakerFunctions ψ n) :
    W ∈ genericModel F hπ ↔ W ∈ whittakerSet ψ n π := Iff.rfl

/-- Its actual right-translation action. -/
def genericModelRepresentation (hπ : Whittaker.IsGeneric ψ n π) :
    Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier)
      (genericModel F hπ).toSubmodule :=
  (genericModel F hπ).toRepresentation

/-- A nonzero functional realizes the original generic representation in its
intrinsic model, without an additional multiplicity premise. -/
def genericModelEquiv (hπ : Whittaker.IsGeneric ψ n π)
    (ℓ : glFunctionals ψ n π) (hℓ : ℓ.val ≠ 0) :
    π.Equiv (genericModelRepresentation F hπ) := by
  letI : Representation.IsIrreducible π := hπ.1
  exact whittakerModelEquiv (isOfWhittakerType_of_isGeneric F hπ) ℓ hℓ

@[simp] theorem genericModelEquiv_apply (hπ : Whittaker.IsGeneric ψ n π)
    (ℓ : glFunctionals ψ n π) (hℓ : ℓ.val ≠ 0)
    (v : V) (g : Langlands.GeneralLinear (n + 1) F.Carrier) :
    (genericModelEquiv F hπ ℓ hℓ v).val.val g = ℓ.val (π g v) := rfl

/-- The generic realization retains admissibility, finite type over the group
algebra, and the one-dimensional full Whittaker functional space. -/
theorem genericModel_isOfWhittakerType (hπ : Whittaker.IsGeneric ψ n π) :
    IsOfWhittakerType (V := (genericModel F hπ).toSubmodule)
      n (standardCharacter ψ n) (genericModelRepresentation F hπ) := by
  let : Representation.IsIrreducible π := hπ.1
  exact whittakerModel_isOfWhittakerType (isOfWhittakerType_of_isGeneric F hπ)

end PadicGeneric

end Langlands.RankinSelberg
