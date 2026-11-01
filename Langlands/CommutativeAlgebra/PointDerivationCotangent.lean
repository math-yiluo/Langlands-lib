import Mathlib.RingTheory.Ideal.Cotangent
import Mathlib.LinearAlgebra.Dimension.Basic
import Mathlib.Algebra.Module.Hom

/-! # Point derivations of a local ring and the dual cotangent space -/

noncomputable section

universe u

open IsLocalRing

namespace Langlands.CommutativeAlgebra.PointDerivation

section CommRing

variable {A R K : Type u} [CommRing A] [CommRing R] [CommRing K]
  (ι : A →+* R) (π : R →+* K)

/-- Additive maps `δ : R → K` satisfying the Leibniz rule along `π` and vanishing on the image
of `ι`, as a `K`-submodule of `R →+ K`. -/
def derivations : Submodule K (R →+ K) where
  carrier := {δ | (∀ a b, δ (a * b) = π a * δ b + π b * δ a) ∧ ∀ c, δ (ι c) = 0}
  add_mem' {δ δ'} hδ hδ' :=
    ⟨fun a b => by simp only [AddMonoidHom.add_apply, hδ.1, hδ'.1]; ring,
      fun c => by simp only [AddMonoidHom.add_apply, hδ.2, hδ'.2, add_zero]⟩
  zero_mem' := ⟨fun a b => by simp, fun c => by simp⟩
  smul_mem' c δ hδ :=
    ⟨fun a b => by simp only [AddMonoidHom.smul_apply, smul_eq_mul, hδ.1]; ring,
      fun c' => by simp only [AddMonoidHom.smul_apply, hδ.2, smul_zero]⟩

variable {ι π}

lemma derivations_mul (δ : derivations ι π) (a b : R) :
    (δ : R →+ K) (a * b) = π a * (δ : R →+ K) b + π b * (δ : R →+ K) a :=
  δ.2.1 a b

lemma derivations_base (δ : derivations ι π) (c : A) : (δ : R →+ K) (ι c) = 0 :=
  δ.2.2 c

/-- Transport of point derivations along a ring isomorphism of the coefficient ring. -/
def derivationsCongr {K' : Type u} [CommRing K'] (τ : K ≃+* K') :
    derivations ι π ≃+ derivations ι ((τ : K →+* K').comp π) where
  toFun δ := ⟨AddMonoidHom.mk' (fun r => τ ((δ : R →+ K) r)) (by simp),
    fun a b => by simp [derivations_mul δ], fun c => by simp [derivations_base δ]⟩
  invFun δ := ⟨AddMonoidHom.mk' (fun r => τ.symm ((δ : R →+ K') r)) (by simp),
    fun a b => by
      simp only [AddMonoidHom.mk'_apply, derivations_mul δ, RingHom.coe_comp,
        RingHom.coe_coe, Function.comp_apply, map_add, map_mul, RingEquiv.symm_apply_apply],
    fun c => by simp [derivations_base δ]⟩
  left_inv δ := by ext r; simp
  right_inv δ := by ext r; simp
  map_add' δ δ' := by ext r; simp

@[simp]
lemma derivationsCongr_apply {K' : Type u} [CommRing K'] (τ : K ≃+* K')
    (δ : derivations ι π) (r : R) :
    ((derivationsCongr τ δ : derivations ι ((τ : K →+* K').comp π)) : R →+ K') r =
      τ ((δ : R →+ K) r) := rfl

lemma derivationsCongr_smul {K' : Type u} [CommRing K'] (τ : K ≃+* K') (c : K)
    (δ : derivations ι π) : derivationsCongr τ (c • δ) = τ c • derivationsCongr τ δ := by
  ext r
  simp

end CommRing

variable {A R K : Type u} [CommRing A] [CommRing R] [Field K] {ι : A →+* R} {π : R →+* K}

variable (hbij : Function.Bijective (π.comp ι))
include hbij

lemma surjective_of_bijective : Function.Surjective π := fun y => by
  obtain ⟨c, hc⟩ := hbij.2 y
  exact ⟨ι c, hc⟩

/-- The ring endomorphism `ι ∘ (π ∘ ι)⁻¹ ∘ π`, the "constant part" of an element. -/
def constPart : R →+* R :=
  ι.comp (((RingEquiv.ofBijective _ hbij).symm : K →+* A).comp π)

lemma π_constPart (r : R) : π (constPart hbij r) = π r :=
  (RingEquiv.ofBijective _ hbij).apply_symm_apply (π r)

lemma constPart_ι (c : A) : constPart hbij (ι c) = ι c :=
  congrArg ι ((RingEquiv.ofBijective _ hbij).symm_apply_apply c)

variable [IsLocalRing R]

lemma ker_eq_maximalIdeal : RingHom.ker π = maximalIdeal R :=
  IsLocalRing.eq_maximalIdeal
    (RingHom.ker_isMaximal_of_surjective π (surjective_of_bijective hbij))

/-- The residue field of `R` is identified with `K` by `π`. -/
def residueEquiv : ResidueField R ≃+* K :=
  (Ideal.quotEquivOfEq (ker_eq_maximalIdeal hbij).symm).trans
    (RingHom.quotientKerEquivOfSurjective (surjective_of_bijective hbij))

@[simp]
lemma residueEquiv_residue (r : R) : residueEquiv hbij (residue R r) = π r := rfl

lemma residueEquiv_symm_apply (r : R) : (residueEquiv hbij).symm (π r) = residue R r := by
  rw [RingEquiv.symm_apply_eq, residueEquiv_residue]

lemma sub_constPart_mem (r : R) : r - constPart hbij r ∈ maximalIdeal R := by
  rw [← ker_eq_maximalIdeal hbij, RingHom.mem_ker, map_sub, π_constPart, sub_self]

lemma constPart_eq_zero_of_mem {r : R} (hr : r ∈ maximalIdeal R) : constPart hbij r = 0 := by
  have : π r = 0 := by rwa [← RingHom.mem_ker, ker_eq_maximalIdeal hbij] at *
  simp [constPart, this]

lemma π_eq_zero_of_mem {r : R} (hr : r ∈ maximalIdeal R) : π r = 0 := by
  rwa [← RingHom.mem_ker, ker_eq_maximalIdeal hbij]

/-- The `R`-linear map `m → κ` induced by a point derivation. -/
def maximalIdealMap (δ : derivations ι π) : maximalIdeal R →ₗ[R] ResidueField R where
  toFun a := (residueEquiv hbij).symm ((δ : R →+ K) a)
  map_add' a b := by simp
  map_smul' r a := by
    simp only [Submodule.coe_smul, smul_eq_mul, derivations_mul, RingHom.id_apply,
      π_eq_zero_of_mem hbij a.2, zero_mul, add_zero, map_mul, residueEquiv_symm_apply,
      Algebra.smul_def, IsLocalRing.ResidueField.algebraMap_eq]

/-- The functional on the cotangent space induced by a point derivation. -/
def toDual (δ : derivations ι π) : Module.Dual (ResidueField R) (CotangentSpace R) :=
  LinearMap.extendScalarsOfSurjective IsLocalRing.residue_surjective
    (Ideal.Cotangent.lift (maximalIdealMap hbij δ) fun a b => by
      change (residueEquiv hbij).symm ((δ : R →+ K) ((a : R) * (b : R))) = 0
      rw [derivations_mul, π_eq_zero_of_mem hbij a.2, π_eq_zero_of_mem hbij b.2]
      simp)

@[simp]
lemma toDual_toCotangent (δ : derivations ι π) (a : maximalIdeal R) :
    toDual hbij δ ((maximalIdeal R).toCotangent a) =
      (residueEquiv hbij).symm ((δ : R →+ K) a) := rfl

/-- The additive map `R → m`, `r ↦ r - constPart r`. -/
def subConst : R →+ maximalIdeal R where
  toFun r := ⟨r - constPart hbij r, sub_constPart_mem hbij r⟩
  map_zero' := by ext; simp
  map_add' r s := by ext; simp only [map_add, Submodule.coe_add]; ring

@[simp]
lemma coe_subConst (r : R) : (subConst hbij r : R) = r - constPart hbij r := rfl

lemma toCotangent_subConst_mul (a b : R) :
    (maximalIdeal R).toCotangent (subConst hbij (a * b)) =
      constPart hbij a • (maximalIdeal R).toCotangent (subConst hbij b) +
        constPart hbij b • (maximalIdeal R).toCotangent (subConst hbij a) := by
  rw [← map_smul (maximalIdeal R).toCotangent, ← map_smul (maximalIdeal R).toCotangent,
    ← map_add (maximalIdeal R).toCotangent, Ideal.toCotangent_eq]
  rw [pow_two]
  convert Ideal.mul_mem_mul (sub_constPart_mem hbij a) (sub_constPart_mem hbij b) using 1
  simp only [Submodule.coe_add, Submodule.coe_smul, smul_eq_mul, coe_subConst, map_mul]
  ring

/-- The point derivation induced by a functional on the cotangent space. -/
def ofDual (l : Module.Dual (ResidueField R) (CotangentSpace R)) : derivations ι π :=
  ⟨AddMonoidHom.mk'
    (fun r => residueEquiv hbij (l ((maximalIdeal R).toCotangent (subConst hbij r))))
    (fun r s => by simp only [map_add]),
    fun a b => by
      simp only [AddMonoidHom.mk'_apply, toCotangent_subConst_mul, map_add,
        LinearMap.map_smul_of_tower]
      rw [Algebra.smul_def, Algebra.smul_def, IsLocalRing.ResidueField.algebraMap_eq,
        map_mul, map_mul, residueEquiv_residue, residueEquiv_residue, π_constPart,
        π_constPart],
    fun c => by
      have : subConst hbij (ι c) = 0 := by ext; simp [constPart_ι]
      simp [this]⟩

@[simp]
lemma ofDual_apply (l : Module.Dual (ResidueField R) (CotangentSpace R)) (r : R) :
    ((ofDual hbij l : derivations ι π) : R →+ K) r =
      residueEquiv hbij (l ((maximalIdeal R).toCotangent (subConst hbij r))) := rfl

/-- Point derivations are the functionals on the cotangent space. -/
def equivDual : derivations ι π ≃+ Module.Dual (ResidueField R) (CotangentSpace R) where
  toFun := toDual hbij
  invFun := ofDual hbij
  left_inv δ := by
    apply Subtype.ext
    ext r
    rw [ofDual_apply, toDual_toCotangent, RingEquiv.apply_symm_apply, coe_subConst, map_sub]
    simp [constPart, derivations_base]
  right_inv l := by
    ext a
    obtain ⟨a, rfl⟩ := (maximalIdeal R).toCotangent_surjective a
    rw [toDual_toCotangent, ofDual_apply, RingEquiv.symm_apply_apply]
    congr 2
    ext
    simp [constPart_eq_zero_of_mem hbij a.2]
  map_add' δ δ' := by
    ext a
    obtain ⟨a, rfl⟩ := (maximalIdeal R).toCotangent_surjective a
    simp

lemma equivDual_smul (c : K) (δ : derivations ι π) :
    equivDual hbij (c • δ) = (residueEquiv hbij).symm c • equivDual hbij δ := by
  ext a
  obtain ⟨a, rfl⟩ := (maximalIdeal R).toCotangent_surjective a
  rw [LinearMap.smul_apply]
  change toDual hbij (c • δ) _ = (residueEquiv hbij).symm c • toDual hbij δ _
  rw [toDual_toCotangent, toDual_toCotangent, smul_eq_mul, ← map_mul]
  rfl

/-- The `K`-rank of the point derivations is the `κ`-rank of the dual cotangent space. -/
theorem rank_derivations :
    Module.rank K (derivations ι π) =
      Module.rank (ResidueField R) (Module.Dual (ResidueField R) (CotangentSpace R)) :=
  rank_eq_of_equiv_equiv (residueEquiv hbij).symm (equivDual hbij)
    (residueEquiv hbij).symm.bijective (equivDual_smul hbij)

end Langlands.CommutativeAlgebra.PointDerivation
