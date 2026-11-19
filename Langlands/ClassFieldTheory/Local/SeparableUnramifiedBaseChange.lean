import Langlands.ClassFieldTheory.Local.SpectralResidueBaseChange
import Langlands.Galois.Local.SeparableUnramifiedProof
import Mathlib.FieldTheory.PrimitiveElement

/-! # Finite unramified composita and arithmetic Frobenius restriction -/

noncomputable section

open IsLocalRing Langlands.LocalGalois Langlands.LocalGalois.Separable

namespace Langlands.ClassFieldTheory.Local

universe u

variable (K L : Type u) [Field K] [Field L] [Algebra K L]
    [Algebra K (SeparableClosure L)] [IsScalarTower K L (SeparableClosure L)]
    (j : SeparableClosure K →ₐ[K] SeparableClosure L)
    (E : IntermediateField K (SeparableClosure K))

/-- The compositum of the base extension and the image of the chosen
intermediate field, inside the actual upper separable closure. -/
def unramifiedCompositum : IntermediateField L (SeparableClosure L) :=
  IntermediateField.adjoin L (Set.range (j.comp E.val))

local notation "M" => unramifiedCompositum K L j E

/-- The chosen embedding of separable closures restricts to the compositum. -/
def unramifiedCompositumEmbedding : E →ₐ[K] M :=
  (j.comp E.val).codRestrict ((M).restrictScalars K).toSubalgebra
    fun x => IntermediateField.subset_adjoin L _ ⟨x, rfl⟩

/-- The algebra structure on the compositum induced by the chosen embedding. -/
abbrev unramifiedCompositumAlgebra : Algebra E M :=
  (unramifiedCompositumEmbedding K L j E).toRingHom.toAlgebra

theorem unramifiedCompositumTower :
    letI := unramifiedCompositumAlgebra K L j E
    IsScalarTower K E M :=
  IsScalarTower.of_algHom (unramifiedCompositumEmbedding K L j E)

instance unramifiedCompositum_finiteDimensional [FiniteDimensional K E] :
    FiniteDimensional L M := by
  obtain ⟨a, ha⟩ := Field.exists_primitive_element K E
  let f := j.comp E.val
  let B := IntermediateField.adjoin L ({f a} : Set (SeparableClosure L))
  have hB : M ≤ B := by
    apply IntermediateField.adjoin_le_iff.mpr
    rintro _ ⟨x, rfl⟩
    have hle : IntermediateField.adjoin K ({a} : Set E) ≤
        (B.restrictScalars K).comap f :=
      IntermediateField.adjoin_le_iff.mpr (Set.singleton_subset_iff.mpr
        (IntermediateField.mem_adjoin_simple_self L (f a)))
    rw [ha] at hle
    exact hle (IntermediateField.mem_top (x := x))
  let : FiniteDimensional L B :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral (f a))
  exact FiniteDimensional.of_injective (IntermediateField.inclusion hB).toLinearMap
    (IntermediateField.inclusion hB).injective

set_option backward.isDefEq.respectTransparency false in
instance unramifiedCompositum_isGalois [IsGalois K E] : IsGalois L M where
  to_isSeparable := inferInstance
  to_normal := by
    apply IntermediateField.normal_iff_forall_map_le'.mpr
    intro τ
    unfold unramifiedCompositum
    rw [IntermediateField.adjoin_map]
    apply IntermediateField.adjoin_le_iff.mpr
    rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
    let f := j.comp E.val
    let : Algebra E (SeparableClosure L) := f.toRingHom.toAlgebra
    let : IsScalarTower K E (SeparableClosure L) := IsScalarTower.of_algHom f
    let τK := τ.restrictScalars K
    exact IntermediateField.subset_adjoin L _ ⟨τK.restrictNormal E x,
      AlgEquiv.restrictNormal_commutes τK E x⟩

/-- Actual restriction of automorphisms along the lower field's
embedding in the compositum. -/
def unramifiedCompositumRestriction [IsGalois K E] : Gal(M/L) →* Gal(E/K) := by
  let := unramifiedCompositumAlgebra K L j E
  let := unramifiedCompositumTower K L j E
  exact (AlgEquiv.restrictNormalHom E).comp (AlgEquiv.restrictScalarsHom K)

theorem unramifiedCompositumEmbedding_restriction [IsGalois K E]
    (τ : Gal(M/L)) (x : E) :
    unramifiedCompositumEmbedding K L j E (unramifiedCompositumRestriction K L j E τ x) =
      τ (unramifiedCompositumEmbedding K L j E x) := by
  let := unramifiedCompositumAlgebra K L j E
  let := unramifiedCompositumTower K L j E
  exact AlgEquiv.restrictNormal_commutes (τ.restrictScalars K) E x

section Local

variable [ValuativeRel K] [ValuativeRel L] [TopologicalSpace K] [TopologicalSpace L]
    [IsNonarchimedeanLocalField K] [IsNonarchimedeanLocalField L] [ValuativeExtension K L]

local instance unramifiedCompositumBaseNormedField : NontriviallyNormedField K := localNormedField K
local instance unramifiedCompositumUpperNormedField : NontriviallyNormedField L := localNormedField L
local instance unramifiedCompositumBaseUltrametric : IsUltrametricDist K := localNormedField_ultrametric K
local instance unramifiedCompositumUpperUltrametric : IsUltrametricDist L := localNormedField_ultrametric L
local instance unramifiedCompositumBaseComplete : CompleteSpace K := localNormedField_complete K
local instance unramifiedCompositumUpperComplete : CompleteSpace L := localNormedField_complete L
local instance unramifiedCompositumResidueFinite : Finite (ResidueField (baseIntegers K)) := localResidue_finite K

omit [Algebra K (SeparableClosure L)] [IsScalarTower K L (SeparableClosure L)] in
private theorem spectralExtensionResidueMap_commutes
    {X Y : Type u} [Field X] [Field Y] [Algebra K X] [Algebra.IsAlgebraic K X]
    [Algebra L Y] [Algebra.IsAlgebraic L Y] [Algebra K Y] [IsScalarTower K L Y]
    (f : X →ₐ[K] Y) (σ : Gal(X/K)) (τ : Gal(Y/L))
    (h : ∀ x, f (σ x) = τ (f x)) (z : ResidueField (extensionIntegers K X)) :
    spectralExtensionResidueMap K L X Y f (residueHom K X σ z) =
      residueHom L Y τ (spectralExtensionResidueMap K L X Y f z) := by
  obtain ⟨z, rfl⟩ := residue_surjective z
  simp only [residueHom_apply, spectralExtensionResidueMap_residue]
  congr 1
  exact Subtype.ext (h z)

set_option backward.isDefEq.respectTransparency false in
private theorem map_mem_inertiaFixedField {x : SeparableClosure K}
    (hx : x ∈ inertiaFixedField K) : j x ∈ inertiaFixedField L := by
  rw [mem_inertiaFixedField_iff]
  intro τ hτ
  let : Algebra (SeparableClosure K) (SeparableClosure L) := j.toRingHom.toAlgebra
  let : IsScalarTower K (SeparableClosure K) (SeparableClosure L) :=
    IsScalarTower.of_algHom j
  let σ := (τ.restrictScalars K).restrictNormal (SeparableClosure K)
  have hcomm (y : SeparableClosure K) : j (σ y) = τ (j y) :=
    AlgEquiv.restrictNormal_commutes (τ.restrictScalars K) (SeparableClosure K) y
  have hσ : σ ∈ separableInertia K := by
    apply (mem_separableInertia_iff K σ).mpr
    intro z
    apply (spectralExtensionResidueMap K L (SeparableClosure K) (SeparableClosure L) j).injective
    have h := spectralExtensionResidueMap_commutes K L j σ τ hcomm (residue _ z)
    simpa only [residueHom_apply, spectralExtensionResidueMap_residue,
      (mem_separableInertia_iff L τ).mp hτ] using h
  exact (hcomm x).symm.trans (congrArg j ((mem_inertiaFixedField_iff K x).mp hx σ hσ))

/-- The actual compositum is arithmetically unramified over the upper base. -/
theorem unramifiedCompositum_unramified [FiniteDimensional K E]
    (hE : ArithmeticUnramified K E) : ArithmeticUnramified L M := by
  apply (finiteUnramifiedMaximality L M).mp
  apply IntermediateField.adjoin_le_iff.mpr
  rintro _ ⟨x, rfl⟩
  exact map_mem_inertiaFixedField K L j ((finiteUnramifiedMaximality K E).mpr hE x.property)

private theorem residueHom_injective_of_arithmeticUnramified
    [FiniteDimensional K E] [IsGalois K E] (hE : ArithmeticUnramified K E) :
    Function.Injective (residueHom K E) := by
  let : IsGalois (ResidueField (baseIntegers K)) (ResidueField (extensionIntegers K E)) :=
    isGalois_of_finite_base _ _
  apply ((residueHom_surjective K E).bijective_of_nat_card_le ?_).1
  rw [IsGalois.card_aut_eq_finrank, IsGalois.card_aut_eq_finrank,
    (arithmeticUnramified_iff_residue_finrank K E).mp hE]

/-- Restriction carries arithmetic Frobenius of the compositum to the
residue-degree power of arithmetic Frobenius of the lower unramified field. -/
theorem unramifiedCompositumRestriction_frobenius [FiniteDimensional K E] [IsGalois K E]
    (hE : ArithmeticUnramified K E) (σ : Gal(E/K)) (τ : Gal(M/L))
    (hσ : ∀ x, residueHom K E σ x = x ^ Nat.card (ResidueField (baseIntegers K)))
    (hτ : ∀ x, residueHom L M τ x = x ^ Nat.card (ResidueField (baseIntegers L))) :
    unramifiedCompositumRestriction K L j E τ = σ ^ spectralResidueDegree K L := by
  apply residueHom_injective_of_arithmeticUnramified K E hE
  apply AlgEquiv.ext
  intro x
  have hσpow (n : ℕ) (z : ResidueField (extensionIntegers K E)) :
      residueHom K E (σ ^ n) z = z ^ Nat.card (ResidueField (baseIntegers K)) ^ n := by
    induction n generalizing z with
    | zero => simp
    | succ n ih =>
      rw [pow_succ, map_mul, AlgEquiv.mul_apply, hσ, ih, ← pow_mul, ← pow_succ']
  let f := unramifiedCompositumEmbedding K L j E
  apply (spectralExtensionResidueMap K L E M f).injective
  rw [spectralExtensionResidueMap_commutes K L f _ τ
    (unramifiedCompositumEmbedding_restriction K L j E τ), hτ, hσpow,
    ← spectralBaseResidue_card K L, map_pow]

end Local

end Langlands.ClassFieldTheory.Local
