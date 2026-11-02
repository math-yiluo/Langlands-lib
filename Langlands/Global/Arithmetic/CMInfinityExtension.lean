import Langlands.Global.Arithmetic.CMCharacterStatement
import Langlands.ClassField.Global.PrincipalIdeleUnits
import Langlands.ClassField.Global.IntegralIdeleClassQuotientFinite

/-! # Unramified realization of CM infinity types -/

noncomputable section

universe u

namespace Langlands.Global

open NumberField
open scoped NumberField

namespace CMUnramifiedInfinity

variable {K : Type u} [Field K] [NumberField K]

/-- Projection to the archimedean factor of the actual idele group. -/
def infinityProjection : Ideles K →ₜ* (InfiniteAdeles K)ˣ where
  toMonoidHom := Units.map
    (RingHom.fst (InfiniteAdeles K) (FiniteAdeles K)).toMonoidHom
  continuous_toFun := continuous_fst.units_map _

/-- The archimedean part of a principal idele. -/
def infinityDiagonal : Kˣ →* (InfiniteAdeles K)ˣ :=
  Units.map (algebraMap K (InfiniteAdeles K)).toMonoidHom

@[simp]
theorem infinityProjection_diagonal (x : Kˣ) :
    infinityProjection (diagonalUnits K x) = infinityDiagonal x := rfl

@[simp]
theorem infinityProjection_inclusion (x : (InfiniteAdeles K)ˣ) :
    infinityProjection (infiniteIdelesInclusion K x) = x := by
  apply Units.ext
  rfl

theorem toCharacter_scale [IsTotallyComplex K] (a : InfinityType K)
    (m : ℕ) (x : (InfiniteAdeles K)ˣ) :
    InfinityType.toCharacter (fun σ ↦ (m : ℤ) * a σ) x =
      (InfinityType.toCharacter a x) ^ m := by
  simp only [InfinityType.toCharacter_apply, ← Finset.prod_pow, mul_pow]
  apply Finset.prod_congr rfl
  intro v _
  simp only [mul_comm (m : ℤ), zpow_mul, zpow_natCast]

omit [NumberField K] in
theorem coordinate_diagonal_units (v : InfinitePlace K) (x : Kˣ) :
    InfinityType.coordinate v (infinityDiagonal x) =
      Units.map v.embedding.toMonoidHom x := by
  apply Units.ext
  exact InfinityType.coordinate_diagonal v x

theorem coordinate_diagonal_ratio [IsCMField K]
    (v : InfinitePlace K) (ε : (𝓞 K)ˣ) :
    InfinityType.coordinate v
      (infinityDiagonal (Units.map (algebraMap (𝓞 K) K).toMonoidHom ε)) /
      star (InfinityType.coordinate v
        (infinityDiagonal (Units.map (algebraMap (𝓞 K) K).toMonoidHom ε))) =
      Units.map v.embedding.toMonoidHom
        (Units.map (algebraMap (𝓞 K) K).toMonoidHom
          (IsCMField.unitsMulComplexConjInv K ε).val) := by
  rw [coordinate_diagonal_units]
  change _ = Units.map v.embedding.toMonoidHom
    (Units.map (algebraMap (𝓞 K) K).toMonoidHom
      (ε * (IsCMField.unitsComplexConj K ε)⁻¹))
  simp only [map_mul, map_inv, div_eq_mul_inv]
  congr 1
  apply Units.ext
  simp only [Units.val_inv_eq_inv_val]
  change (star (v.embedding (ε : K)))⁻¹ =
    (v.embedding (IsCMField.complexConj K (ε : K)))⁻¹
  rw [IsCMField.complexEmbedding_complexConj]
  rfl

/-- The root-of-unity order kills every global-unit value at once. -/
theorem toCharacter_global_unit [IsCMField K] (a : InfinityType K)
    (ha : a.IsAnticyclotomic) (ε : (𝓞 K)ˣ) :
    InfinityType.toCharacter
        (fun σ ↦ (NumberField.Units.torsionOrder K : ℤ) * a σ)
      (infinityDiagonal (Units.map (algebraMap (𝓞 K) K).toMonoidHom ε)) = 1 := by
  rw [toCharacter_scale, InfinityType.toCharacter_anticyclotomic a ha,
    ← Finset.prod_pow]
  apply Finset.prod_eq_one
  intro v _
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast,
    coordinate_diagonal_ratio, ← map_pow, ← map_pow]
  have h := NumberField.Units.pow_torsionOrder_eq_one K
    (IsCMField.unitsMulComplexConjInv K ε).property
  rw [h, map_one, map_one, one_zpow]

open Langlands.ClassField.Global
open IsDedekindDomain

/-- The subgroup integral and invertible at every finite place is open. -/
theorem isOpen_integralIdeles :
    IsOpen (integralIdeles K : Set (Ideles K)) := by
  have hO : IsOpen {x : FiniteAdeles K |
      ∀ w : FinitePlace K, x.val w ∈ w.adicCompletionIntegers K} :=
    RestrictedProduct.isOpen_forall_mem
      (fun w : FinitePlace K ↦ Valued.isOpen_valuationSubring (FiniteCompletion K w))
  have hval := hO.preimage (show Continuous (fun x : Ideles K ↦ x.val.2) from
    continuous_snd.comp Units.continuous_val)
  have hinv := hO.preimage (show Continuous (fun x : Ideles K ↦ x.inv.2) from
    continuous_snd.comp Units.continuous_coe_inv)
  convert hval.inter hinv using 1
  ext x
  change (∀ w : FinitePlace K,
      Valued.v (ideleCoordinate w x : FiniteCompletion K w) = 1) ↔
    (∀ w : FinitePlace K, x.val.2.val w ∈ w.adicCompletionIntegers K) ∧
    (∀ w : FinitePlace K, x.inv.2.val w ∈ w.adicCompletionIntegers K)
  rw [← forall_and]
  apply forall_congr'
  intro w
  exact (HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one
    (a := ideleCoordinate w x)).symm

/-- The integral-ideles surjection carries the quotient topology on its image. -/
theorem integralIdelesToClasses_isQuotientMap :
    Topology.IsQuotientMap (integralIdelesToClasses K) := by
  have ho : IsOpenMap (integralIdelesToClasses K) :=
    ((QuotientGroup.isOpenQuotientMap_mk
      (N := principalIdeles K)).isOpenMap.domRestrict isOpen_integralIdeles).codRestrict _
  have hc : Continuous (integralIdelesToClasses K) :=
    ((ideleClassMap K).continuous.comp continuous_subtype_val).subtype_mk _
  exact ho.isQuotientMap hc (integralIdelesToClasses_surjective K)

/-- Restrict an infinity character to the integral ideles. -/
def integralInfinityCharacter (η : (InfiniteAdeles K)ˣ →ₜ* ℂˣ) :
    integralIdeles K →ₜ* ℂˣ where
  toMonoidHom := (η.toMonoidHom.comp infinityProjection.toMonoidHom).comp
    (integralIdeles K).subtype
  continuous_toFun :=
    η.continuous.comp (infinityProjection.continuous.comp continuous_subtype_val)

theorem integralInfinityCharacter_ker (η : (InfiniteAdeles K)ˣ →ₜ* ℂˣ)
    (hη : ∀ ε : (𝓞 K)ˣ,
      η (infinityDiagonal (Units.map (algebraMap (𝓞 K) K).toMonoidHom ε)) = 1) :
    (integralIdelesToClasses K).ker ≤ (integralInfinityCharacter η).toMonoidHom.ker := by
  intro x hx
  rw [integralIdelesToClasses_ker] at hx
  change (x : Ideles K) ∈ principalIdeles K at hx
  obtain ⟨z, hz⟩ := hx
  have hint : diagonalUnits K z ∈ integralIdeles K := by
    rw [hz]
    exact x.property
  obtain ⟨ε, hε⟩ := (principalIdeleUnitCriterion K z).mp hint
  change η (infinityProjection (x : Ideles K)) = 1
  rw [← hz, infinityProjection_diagonal, ← hε]
  exact hη ε

/-- Algebraic descent through the principal-unit kernel. -/
def integralClassCharacterHom (η : (InfiniteAdeles K)ˣ →ₜ* ℂˣ)
    (hη : ∀ ε : (𝓞 K)ˣ,
      η (infinityDiagonal (Units.map (algebraMap (𝓞 K) K).toMonoidHom ε)) = 1) :
    integralIdeleClasses K →* ℂˣ :=
  (integralIdelesToClasses K).liftOfSurjective
    (integralIdelesToClasses_surjective K)
    ⟨(integralInfinityCharacter η).toMonoidHom, integralInfinityCharacter_ker η hη⟩

@[simp]
theorem integralClassCharacterHom_apply (η : (InfiniteAdeles K)ˣ →ₜ* ℂˣ)
    (hη : ∀ ε : (𝓞 K)ˣ,
      η (infinityDiagonal (Units.map (algebraMap (𝓞 K) K).toMonoidHom ε)) = 1)
    (x : integralIdeles K) :
    integralClassCharacterHom η hη (integralIdelesToClasses K x) =
      η (infinityProjection (x : Ideles K)) :=
  MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ _

/-- Continuous descent, using the open quotient map onto the integral classes. -/
def integralClassCharacter (η : (InfiniteAdeles K)ˣ →ₜ* ℂˣ)
    (hη : ∀ ε : (𝓞 K)ˣ,
      η (infinityDiagonal (Units.map (algebraMap (𝓞 K) K).toMonoidHom ε)) = 1) :
    integralIdeleClasses K →ₜ* ℂˣ where
  toMonoidHom := integralClassCharacterHom η hη
  continuous_toFun := integralIdelesToClasses_isQuotientMap.continuous_iff.mpr (by
    change Continuous (fun x : integralIdeles K ↦
      integralClassCharacterHom η hη (integralIdelesToClasses K x))
    simp_rw [integralClassCharacterHom_apply]
    exact (integralInfinityCharacter η).continuous)

@[simp]
theorem integralClassCharacter_apply (η : (InfiniteAdeles K)ˣ →ₜ* ℂˣ)
    (hη : ∀ ε : (𝓞 K)ˣ,
      η (infinityDiagonal (Units.map (algebraMap (𝓞 K) K).toMonoidHom ε)) = 1)
    (x : integralIdeles K) :
    integralClassCharacter η hη (integralIdelesToClasses K x) =
      η (infinityProjection (x : Ideles K)) :=
  integralClassCharacterHom_apply η hη x

/-- A common exponent for the finite quotient by integral idele classes. -/
def classExponent (K : Type u) [Field K] [NumberField K] : ℕ :=
  Nat.card (IntegralIdeleClassQuotient K)

theorem classExponent_pos : 0 < classExponent K := by
  let := integralIdeleClassQuotientFinite K
  exact Nat.card_pos

theorem pow_classExponent_mem (c : IdeleClasses K) :
    c ^ classExponent K ∈ integralIdeleClasses K := by
  apply (QuotientGroup.eq_one_iff _).mp
  change (QuotientGroup.mk' (integralIdeleClasses K)) (c ^ classExponent K) = 1
  rw [map_pow]
  exact pow_card_eq_one'

/-- Raising to the residual class-number exponent lands continuously in the
integral-class subgroup. -/
def classPower : IdeleClasses K →ₜ* integralIdeleClasses K where
  toFun c := ⟨c ^ classExponent K, pow_classExponent_mem c⟩
  map_one' := Subtype.ext (one_pow _)
  map_mul' x y := Subtype.ext (mul_pow x y _)
  continuous_toFun := (continuous_pow (classExponent K)).subtype_mk _

/-- Extend an infinity character, after the common finite-class power. -/
def extendedCharacter (η : (InfiniteAdeles K)ˣ →ₜ* ℂˣ)
    (hη : ∀ ε : (𝓞 K)ˣ,
      η (infinityDiagonal (Units.map (algebraMap (𝓞 K) K).toMonoidHom ε)) = 1) :
    HeckeCharacter K :=
  (integralClassCharacter η hη).comp classPower

theorem extendedCharacter_integral (η : (InfiniteAdeles K)ˣ →ₜ* ℂˣ)
    (hη : ∀ ε : (𝓞 K)ˣ,
      η (infinityDiagonal (Units.map (algebraMap (𝓞 K) K).toMonoidHom ε)) = 1)
    (x : integralIdeles K) :
    extendedCharacter η hη (ideleClassMap K (x : Ideles K)) =
      η (infinityProjection (x : Ideles K)) ^ classExponent K := by
  change integralClassCharacter η hη
    (classPower (ideleClassMap K (x : Ideles K))) = _
  have hp : classPower (ideleClassMap K (x : Ideles K)) =
      integralIdelesToClasses K (x ^ classExponent K) := by
    apply Subtype.ext
    exact (map_pow (ideleClassMap K) (x : Ideles K) (classExponent K)).symm
  rw [hp, integralClassCharacter_apply]
  exact map_pow (η.comp infinityProjection) (x : Ideles K) (classExponent K)

theorem infiniteIdelesInclusion_mem (x : (InfiniteAdeles K)ˣ) :
    infiniteIdelesInclusion K x ∈ integralIdeles K := by
  intro w
  change Valued.v (1 : FiniteCompletion K w) = 1
  exact map_one _

/-- The base character realizes a positive multiple of the infinity type and
has the stated value on every integral idele, before antisymmetrization. -/
theorem exists_base_character [IsCMField K] (a : InfinityType K)
    (ha : a.IsAnticyclotomic) :
    ∃ (n : ℕ) (ψ : HeckeCharacter K), 0 < n ∧
      ψ.HasPrescribedInfinityComponent
        (InfinityType.toCharacter (fun σ ↦ (n : ℤ) * a σ)) ∧
      ∀ x : integralIdeles K,
        ψ (ideleClassMap K (x : Ideles K)) =
          InfinityType.toCharacter (fun σ ↦ (n : ℤ) * a σ)
            (infinityProjection (x : Ideles K)) := by
  let t := NumberField.Units.torsionOrder K
  let n := classExponent K * t
  let η := InfinityType.toCharacter (fun σ ↦ (t : ℤ) * a σ)
  have hη : ∀ ε : (𝓞 K)ˣ,
      η (infinityDiagonal (Units.map (algebraMap (𝓞 K) K).toMonoidHom ε)) = 1 :=
    toCharacter_global_unit a ha
  let ψ := extendedCharacter η hη
  have htype : (fun σ ↦ (classExponent K : ℤ) * ((t : ℤ) * a σ)) =
      (fun σ ↦ (n : ℤ) * a σ) := by
    funext σ
    simp only [n, Nat.cast_mul, mul_assoc]
  have hψ (x : integralIdeles K) :
      ψ (ideleClassMap K (x : Ideles K)) =
        InfinityType.toCharacter (fun σ ↦ (n : ℤ) * a σ)
          (infinityProjection (x : Ideles K)) := by
    change extendedCharacter η hη _ = _
    rw [extendedCharacter_integral]
    change (InfinityType.toCharacter (fun σ ↦ (t : ℤ) * a σ)
      (infinityProjection (x : Ideles K))) ^ classExponent K = _
    rw [← toCharacter_scale, htype]
  refine ⟨n, ψ,
    Nat.mul_pos classExponent_pos (NumberField.Units.torsionOrder_pos K), ?_, hψ⟩
  apply ContinuousMonoidHom.ext
  intro x
  change ψ (ideleClassMap K (infiniteIdelesInclusion K x)) = _
  simpa only [infinityProjection_inclusion] using
    hψ ⟨infiniteIdelesInclusion K x, infiniteIdelesInclusion_mem x⟩

end CMUnramifiedInfinity
end Langlands.Global
