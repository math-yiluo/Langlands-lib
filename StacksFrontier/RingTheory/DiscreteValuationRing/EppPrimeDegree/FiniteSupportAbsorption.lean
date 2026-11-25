module

public import StacksFrontier.RingTheory.DiscreteValuationRing.EppConstantNumeratorFamily
public import StacksFrontier.RingTheory.DiscreteValuationRing.EppSharedResidueAbsorption
public import StacksFrontier.RingTheory.DiscreteValuationRing.RamificationTower

set_option autoImplicit false
set_option maxSynthPendingDepth 3

open Stacks.DegreePExtensionLevel
open Stacks.DiscreteValuationRing.EppLevelInduction

/-!
# Prime-degree input: fraction-field towers and finite-support absorption

Fraction-field towers for embedded DVR maps and the finite weakly-unramified residue
absorptions (finite support, mixed level support) used by the prime-degree solvers.
-/

@[expose] public section

open IsLocalRing
open IsDiscreteValuationRing
open scoped TensorProduct

namespace Stacks.EppTheorem

universe u v w uΩ

/-- A module-finite faithful extension `A → A₁` of a DVR induces a finite extension of fraction
fields `K → FractionRing A₁` compatible with the scalar towers. -/
private theorem exists_algebra_fractionRing_tower_of_finite
    {A A₁ K : Type u} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [CommRing A₁] [IsDomain A₁] [Field K] [Algebra A A₁] [Algebra A K] [IsFractionRing A K]
    [Module.Finite A A₁] [FaithfulSMul A A₁] :
    ∃ (_ : Algebra K (FractionRing A₁)), IsScalarTower A K (FractionRing A₁) ∧
      IsScalarTower A A₁ (FractionRing A₁) ∧ Module.Finite K (FractionRing A₁) := by
  have hinj : Function.Injective (algebraMap A A₁) :=
    FaithfulSMul.algebraMap_injective A A₁
  have hnonzero : nonZeroDivisors A ≤
      Submonoid.comap (algebraMap A A₁) (nonZeroDivisors A₁) := by
    intro x hx
    rw [Submonoid.mem_comap, mem_nonZeroDivisors_iff_ne_zero]
    simpa only [map_zero] using hinj.ne (nonZeroDivisors.ne_zero hx)
  let : Algebra K (FractionRing A₁) :=
    (IsFractionRing.map (K := K) (L := FractionRing A₁) hinj).toAlgebra
  let : IsScalarTower A A₁ (FractionRing A₁) := IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower A K (FractionRing A₁) := IsScalarTower.of_algebraMap_eq fun a => by
    calc
      algebraMap A (FractionRing A₁) a = algebraMap A₁ (FractionRing A₁) (algebraMap A A₁ a) :=
        rfl
      _ = IsFractionRing.map (K := K) (L := FractionRing A₁) hinj (algebraMap A K a) :=
        by simpa only [IsFractionRing.map] using
          (IsLocalization.map_eq (Q := FractionRing A₁) hnonzero a).symm
      _ = algebraMap K (FractionRing A₁) (algebraMap A K a) := rfl
  exact ⟨inferInstance, inferInstance, inferInstance,
    finiteDimensional_fractionRing_of_finite A A₁ K (FractionRing A₁) hinj⟩

/-- **Shared residue absorption, together with the fraction-field extension it defines.**

This is
`EppCondition.exists_isWeaklyUnramified_forall_exists_pow_eq_of_residueOverfield`, with
`K₂ = FractionRing R₂` added to its output.  The induced map `K → K₂` is the map of
fraction fields attached to `R → R₂`; module-finiteness of `K₂ / K` follows from
module-finiteness of `R₂ / R`.

The overfield conclusion is unchanged and remains quantified after `R₂` and `K₂` are fixed.
Thus the same normal residue extension supplies the deep roots in every conjugate factor. -/
theorem
  EppCondition.exists_fractionField_isWeaklyUnramified_forall_exists_pow_eq_of_residueOverfield
    {R K : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    [IsAdicComplete (maximalIdeal R) R] [PerfectField (ResidueField R)]
    {ι : Type w} [Finite ι] (S : ι → Type v)
    [∀ i, CommRing (S i)] [∀ i, IsLocalRing (S i)]
    [∀ i, Algebra R (S i)] [∀ i, IsLocalHom (algebraMap R (S i))]
    {p : ℕ} [∀ i, ExpChar (ResidueField (S i)) p]
    (h : ∀ i, EppCondition R (S i) p)
    (s : ∀ i, Finset (ResidueField (S i)))
    (hs : ∀ i, ∀ x ∈ s i, x ∈ perfectCore (ResidueField (S i)) p) (N : ℕ) :
    ∃ (R₂ : Type u) (_ : CommRing R₂) (_ : IsDomain R₂)
      (_ : IsDiscreteValuationRing R₂) (_ : Algebra R R₂) (_ : Module.Finite R R₂)
      (_ : IsDiscreteValuationRing.IsExtension R R₂)
      (_ : IsAdicComplete (maximalIdeal R₂) R₂) (_ : PerfectField (ResidueField R₂))
      (K₂ : Type u) (_ : Field K₂) (_ : Algebra R₂ K₂) (_ : IsFractionRing R₂ K₂)
      (_ : Algebra K K₂) (_ : Algebra R K₂) (_ : IsScalarTower R K K₂)
      (_ : IsScalarTower R R₂ K₂) (_ : Module.Finite K K₂),
      IsDiscreteValuationRing.IsWeaklyUnramified R R₂ ∧
        IsGalois (ResidueField R) (ResidueField R₂) ∧
        ∀ (i : ι) (Ω : Type uΩ) [Field Ω] [Algebra (ResidueField R) Ω]
          [Algebra (ResidueField (S i)) Ω] [Algebra (ResidueField R₂) Ω]
          [IsScalarTower (ResidueField R) (ResidueField (S i)) Ω]
          [IsScalarTower (ResidueField R) (ResidueField R₂) Ω],
          ∀ x ∈ s i, ∃ z : ResidueField R₂,
            algebraMap (ResidueField R₂) Ω z ^ p ^ N =
              algebraMap (ResidueField (S i)) Ω x := by
  obtain ⟨R₂, hR₂comm, hR₂dom, hR₂dvr, hRR₂, hR₂fin, hR₂ext,
      hweak, hgal, hroot⟩ :=
    EppCondition.exists_isWeaklyUnramified_forall_exists_pow_eq_of_residueOverfield
      S h s hs N
  let := hR₂comm
  let := hR₂dom
  let := hR₂dvr
  let := hRR₂
  let := hR₂fin
  let := hR₂ext
  let hR₂complete : IsAdicComplete (maximalIdeal R₂) R₂ :=
    IsDiscreteValuationRing.isAdicComplete_of_finite R R₂
  let hR₂perfect : PerfectField (ResidueField R₂) :=
    IsDiscreteValuationRing.perfectField_residueField_of_finite R R₂
  let K₂ := FractionRing R₂
  obtain ⟨hKK₂, hRKK₂, hRR₂K₂, hK₂fin⟩ :=
    exists_algebra_fractionRing_tower_of_finite (A := R) (A₁ := R₂) (K := K)
  let := hKK₂
  let := hRKK₂
  let := hRR₂K₂
  let := hK₂fin
  refine ⟨R₂, hR₂comm, hR₂dom, hR₂dvr, hRR₂, hR₂fin, hR₂ext,
    hR₂complete, hR₂perfect,
    K₂, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, hweak, hgal, hroot⟩

end Stacks.EppTheorem

end
