import Langlands.Galois.Local.SeparableUnramifiedStatement
import Langlands.Galois.Local.SpectralProof
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.FieldTheory.Normal.Closure

noncomputable section

open IsLocalRing
open scoped NNReal

namespace Langlands.LocalGalois.Separable

universe u

section Exhaustion

variable (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]

theorem finiteGaloisExhaustion_in_inertiaFixedField
    (s : Finset (inertiaFixedField F)) :
    ∃ E : IntermediateField F (SeparableClosure F),
      FiniteDimensional F E ∧ IsGalois F E ∧ E ≤ inertiaFixedField F ∧
        ∀ x ∈ s, fixedFieldToSepClosure F x ∈ E := by
  classical
  let t : Finset (SeparableClosure F) := s.image (fixedFieldToSepClosure F)
  let A := IntermediateField.adjoin F (t : Set (SeparableClosure F))
  have : FiniteDimensional F A :=
    IntermediateField.finiteDimensional_adjoin fun x _ =>
      Algebra.IsIntegral.isIntegral (R := F) x
  let E := IntermediateField.normalClosure F A (SeparableClosure F)
  have hA : A ≤ inertiaFixedField F := by
    apply IntermediateField.adjoin_le_iff.mpr
    intro x hx
    obtain ⟨y, -, rfl⟩ := Finset.mem_image.mp hx
    exact y.property
  have hE : E ≤ inertiaFixedField F :=
    IntermediateField.normalClosure_le_iff_of_normal.mpr hA
  refine ⟨E, inferInstance, IsGalois.normalClosure _ _ _, hE, ?_⟩
  intro x hx
  apply IntermediateField.le_normalClosure A
  apply IntermediateField.subset_adjoin
  exact Finset.mem_image.mpr ⟨x, hx, rfl⟩

theorem finiteUnramifiedGaloisExhaustion_of_maximality
    (h : FiniteUnramifiedMaximality F) :
    FiniteUnramifiedGaloisExhaustion F := by
  intro s
  obtain ⟨E, hfin, hgal, hE, hs⟩ := finiteGaloisExhaustion_in_inertiaFixedField F s
  let := hfin
  exact ⟨E, hfin, hgal, hE, (h E).mp hE, hs⟩

end Exhaustion

end Langlands.LocalGalois.Separable

namespace Langlands.LocalGalois

theorem isGalois_of_finite_base (k L : Type*) [Field k] [Field L]
    [Finite k] [Algebra k L] [Algebra.IsAlgebraic k L] : IsGalois k L := by
  have hnormal : Normal k L := by
    constructor
    intro x
    let E := IntermediateField.adjoin k ({x} : Set L)
    let : FiniteDimensional k E :=
      IntermediateField.adjoin.finiteDimensional
        (Algebra.IsIntegral.isIntegral (R := k) x)
    have : Finite E := Module.finite_of_finite k
    have h := Normal.splits (inferInstance : Normal k E)
      (⟨x, IntermediateField.mem_adjoin_simple_self k x⟩ : E)
    rw [← minpoly.algebraMap_eq E.val.injective] at h
    have h' := h.map (algebraMap E L)
    simpa only [Polynomial.map_map, ← IsScalarTower.algebraMap_eq,
      IntermediateField.algebraMap_apply] using h'
  exact ⟨⟩

section Tower

variable (K L : Type*) [NontriviallyNormedField K] [IsUltrametricDist K]
    [CompleteSpace K] [Field L] [Algebra K L] [Algebra.IsAlgebraic K L]
    (E : IntermediateField K L) [FiniteDimensional K E]

local instance : NontriviallyNormedField E := spectralNorm.nontriviallyNormedField K E
local instance : NormedAlgebra K E := spectralNorm.normedAlgebra K E
local instance : IsUltrametricDist E := IsUltrametricDist.isUltrametricDist_iff_isNonarchimedean_norm.mpr
  (isNonarchimedean_spectralNorm (K := K))
local instance : CompleteSpace E := spectralNorm.completeSpace K E

theorem spectralValuation_tower_eq :
    spectralValuation E L = spectralValuation K L := by
  ext x
  symm
  exact spectralNorm_unique_field_norm_ext
    (f := MulRingNorm.toAbsoluteValue (spectralMulAlgNorm K L).toMulRingNorm)
    (fun y : E => (spectralNorm.eq_of_tower y).symm) x

omit [FiniteDimensional K E] in
theorem spectralBaseIntegers_eq : baseIntegers E = extensionIntegers K E := by
  ext x
  change spectralNorm K E x ≤ 1 ↔ spectralNorm K E x ≤ 1
  rfl

def spectralBaseIntegersEquiv : baseIntegers E ≃+* extensionIntegers K E :=
  RingEquiv.subringCongr
    (congrArg ValuationSubring.toSubring (spectralBaseIntegers_eq K L E))

def spectralBaseResidueEquiv :
    ResidueField (baseIntegers E) ≃+* ResidueField (extensionIntegers K E) :=
  ResidueField.mapEquiv (spectralBaseIntegersEquiv K L E)

def spectralTowerIntegersEquiv :
    extensionIntegers E L ≃+* extensionIntegers K L :=
  RingEquiv.subringCongr
    (congrArg ValuationSubring.toSubring
      (congrArg Valuation.valuationSubring (spectralValuation_tower_eq K L E)))

theorem spectralTowerIntegersEquiv_coe (x : extensionIntegers E L) :
    (spectralTowerIntegersEquiv K L E x : L) = x := rfl

def spectralTowerResidueEquiv :
    ResidueField (extensionIntegers E L) ≃+*
      ResidueField (extensionIntegers K L) :=
  ResidueField.mapEquiv (spectralTowerIntegersEquiv K L E)

theorem spectralTowerResidueEquiv_base
    (x : ResidueField (baseIntegers E)) :
    spectralTowerResidueEquiv K L E
        (algebraMap (ResidueField (baseIntegers E))
          (ResidueField (extensionIntegers E L)) x) =
      residueInclusion K L E (spectralBaseResidueEquiv K L E x) := by
  obtain ⟨x, rfl⟩ := residue_surjective x
  change residue (extensionIntegers K L)
      (spectralTowerIntegersEquiv K L E
        (algebraMap (baseIntegers E) (extensionIntegers E L) x)) =
    residue (extensionIntegers K L) (integerInclusion K L E (spectralBaseIntegersEquiv K L E x))
  congr 1

theorem spectralTowerResidueEquiv_aut
    (σ : Gal(L/E)) (y : ResidueField (extensionIntegers E L)) :
    spectralTowerResidueEquiv K L E (residueHom E L σ y) =
      residueHom K L (σ.restrictScalars K) (spectralTowerResidueEquiv K L E y) := by
  obtain ⟨y, rfl⟩ := residue_surjective y
  change residue (extensionIntegers K L)
      (spectralTowerIntegersEquiv K L E (integerAut E L σ y)) =
    residue (extensionIntegers K L)
      (integerAut K L (σ.restrictScalars K) (spectralTowerIntegersEquiv K L E y))
  congr 1

theorem map_residueHom_fixingSubgroup
    [IsGalois K L] [Finite (ResidueField (extensionIntegers K E))] :
    E.fixingSubgroup.map (residueHom K L) =
      (residueInclusion K L E).fieldRange.fixingSubgroup := by
  ext τ
  constructor
  · rintro ⟨σ, hσ, rfl⟩
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro y hy
    obtain ⟨z, rfl⟩ := AlgHom.mem_fieldRange.mp hy
    obtain ⟨z, rfl⟩ := residue_surjective z
    change residue (extensionIntegers K L)
        (integerAut K L σ (integerInclusion K L E z)) =
      residue (extensionIntegers K L) (integerInclusion K L E z)
    congr 1
    apply Subtype.ext
    exact ((IntermediateField.mem_fixingSubgroup_iff (K := E) σ).mp hσ) z z.1.property
  · intro hτ
    have hfix (y : ResidueField (extensionIntegers K E)) :
        τ (residueInclusion K L E y) = residueInclusion K L E y :=
      ((IntermediateField.mem_fixingSubgroup_iff
        (K := (residueInclusion K L E).fieldRange) τ).mp hτ) _
        (AlgHom.mem_fieldRange.mpr ⟨y, rfl⟩)
    let : Finite (ResidueField (baseIntegers E)) :=
      Finite.of_injective (spectralBaseResidueEquiv K L E)
        (spectralBaseResidueEquiv K L E).injective
    let e := spectralTowerResidueEquiv K L E
    let τ' : Gal(ResidueField (extensionIntegers E L)/ResidueField (baseIntegers E)) :=
      { e.trans (τ.toRingEquiv.trans e.symm) with
        commutes' := by
          intro y
          apply e.injective
          change e (e.symm (τ (e (algebraMap _ _ y)))) = e (algebraMap _ _ y)
          rw [e.apply_symm_apply]
          change τ (spectralTowerResidueEquiv K L E (algebraMap _ _ y)) =
            spectralTowerResidueEquiv K L E (algebraMap _ _ y)
          rw [spectralTowerResidueEquiv_base, hfix] }
    obtain ⟨σ, hσ⟩ := residueHom_surjective E L τ'
    refine ⟨σ.restrictScalars K, ?_, ?_⟩
    · apply (IntermediateField.mem_fixingSubgroup_iff (K := E) _).mpr
      intro x hx
      exact σ.commutes (⟨x, hx⟩ : E)
    · ext y
      obtain ⟨z, rfl⟩ := e.surjective y
      rw [← spectralTowerResidueEquiv_aut, hσ]
      change e (e.symm (τ (e z))) = τ (e z)
      exact e.apply_symm_apply _


theorem fixingSubgroup_sup_inertia_index
    [IsGalois K L] [Finite (ResidueField (baseIntegers K))]
    [Finite (ResidueField (extensionIntegers K E))] :
    (E.fixingSubgroup ⊔ inertia K L).index =
      Module.finrank (ResidueField (baseIntegers K))
        (ResidueField (extensionIntegers K E)) := by
  let : IsGalois (ResidueField (baseIntegers K))
      (ResidueField (extensionIntegers K L)) := isGalois_of_finite_base _ _
  rw [inertia, ← Subgroup.comap_map_eq,
    Subgroup.index_comap_of_surjective _ (residueHom_surjective K L),
    map_residueHom_fixingSubgroup,
    ← IntermediateField.finrank_eq_fixingSubgroup_index]
  exact (AlgHom.equivFieldRange (residueInclusion K L E)).toLinearEquiv.finrank_eq.symm

theorem inertia_le_fixingSubgroup_iff_residue_finrank
    [IsGalois K L] [Finite (ResidueField (baseIntegers K))]
    [Finite (ResidueField (extensionIntegers K E))] :
    inertia K L ≤ E.fixingSubgroup ↔
      Module.finrank (ResidueField (baseIntegers K))
        (ResidueField (extensionIntegers K E)) = Module.finrank K E := by
  have hmul := Subgroup.relIndex_mul_index
    (le_sup_left : E.fixingSubgroup ≤ E.fixingSubgroup ⊔ inertia K L)
  rw [fixingSubgroup_sup_inertia_index,
    ← IntermediateField.finrank_eq_fixingSubgroup_index] at hmul
  constructor
  · intro h
    have hi : (E.fixingSubgroup ⊔ inertia K L).index = E.fixingSubgroup.index := by
      rw [sup_eq_left.mpr h]
    rw [fixingSubgroup_sup_inertia_index,
      ← IntermediateField.finrank_eq_fixingSubgroup_index] at hi
    exact hi
  · intro h
    rw [h] at hmul
    have h1 : E.fixingSubgroup.relIndex (E.fixingSubgroup ⊔ inertia K L) = 1 :=
      Nat.eq_of_mul_eq_mul_right (Module.finrank_pos (R := K) (M := E))
        (hmul.trans (one_mul _).symm)
    exact le_sup_right.trans (Subgroup.relIndex_eq_one.mp h1)

end Tower

end Langlands.LocalGalois
