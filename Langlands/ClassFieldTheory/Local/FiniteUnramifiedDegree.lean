import Langlands.Galois.Local.AbsoluteProof
import Langlands.Galois.Local.SeparableUnramifiedArithmeticProof
import Langlands.Galois.Local.SeparableUnramifiedProof
import Mathlib.FieldTheory.Finite.Extension

/-! # Finite unramified stages of every positive degree -/

noncomputable section

open IsLocalRing Langlands.LocalGalois Langlands.LocalGalois.Separable Polynomial

namespace Langlands.ClassFieldTheory.Local

universe u

variable (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]

local instance finiteUnramifiedDegreeNormedField : NontriviallyNormedField F := localNormedField F
local instance finiteUnramifiedDegreeUltrametric : IsUltrametricDist F := localNormedField_ultrametric F
local instance finiteUnramifiedDegreeComplete : CompleteSpace F := localNormedField_complete F
local instance finiteUnramifiedDegreeResidueFinite : Finite (ResidueField (baseIntegers F)) := localResidue_finite F

local notation "Ω" => SeparableClosure F
local notation "κ" => ResidueField (baseIntegers F)
local notation "q" => Nat.card κ

private def teichmullerRoot (n : ℕ) (hn : 0 < n) : extensionIntegers F Ω :=
  (exists_teich F hn).choose

private theorem teichmullerRoot_primitive (n : ℕ) (hn : 0 < n) :
    IsPrimitiveRoot (teichmullerRoot F n hn) (q ^ n - 1) :=
  (exists_teich F hn).choose_spec

/-- A finite unramified intermediate field of prescribed positive degree,
obtained by adjoining an actual Teichmüller root in the separable closure. -/
def finiteUnramifiedFieldOfDegree (n : ℕ) (hn : 0 < n) : IntermediateField F Ω :=
  IntermediateField.adjoin F {(teichmullerRoot F n hn : Ω)}

instance finiteUnramifiedFieldOfDegree_finiteDimensional (n : ℕ) (hn : 0 < n) :
    FiniteDimensional F (finiteUnramifiedFieldOfDegree F n hn) :=
  IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral _)

instance finiteUnramifiedFieldOfDegree_isGalois (n : ℕ) (hn : 0 < n) :
    IsGalois F (finiteUnramifiedFieldOfDegree F n hn) where
  to_isSeparable := inferInstance
  to_normal := by
    apply IntermediateField.normal_iff_forall_map_le'.mpr
    intro σ
    unfold finiteUnramifiedFieldOfDegree
    rw [IntermediateField.adjoin_map, Set.image_singleton]
    apply IntermediateField.adjoin_le_iff.mpr
    apply Set.singleton_subset_iff.mpr
    apply mem_adjoin_of_pow_eq_one F hn (teichmullerRoot_primitive F n hn)
    rw [← map_pow, coe_pow_eq_one F (teichmullerRoot_primitive F n hn).pow_eq_one, map_one]

theorem finiteUnramifiedFieldOfDegree_unramified (n : ℕ) (hn : 0 < n) :
    ArithmeticUnramified F (finiteUnramifiedFieldOfDegree F n hn) := by
  apply (finiteUnramifiedMaximality F _).mp
  apply IntermediateField.adjoin_le_iff.mpr
  apply Set.singleton_subset_iff.mpr
  exact mem_inertiaFixedField_of_pow_eq_one F hn _
    (teichmullerRoot_primitive F n hn).pow_eq_one

set_option backward.isDefEq.respectTransparency false in
/-- The field obtained from a primitive root of order `q ^ n - 1` has
degree exactly `n` over the local base. -/
theorem finiteUnramifiedFieldOfDegree_finrank (n : ℕ) (hn : 0 < n) :
    Module.finrank F (finiteUnramifiedFieldOfDegree F n hn) = n := by
  let E := finiteUnramifiedFieldOfDegree F n hn
  let ζ := teichmullerRoot F n hn
  let z := residue _ ζ
  have hζ : IsPrimitiveRoot ζ (q ^ n - 1) := teichmullerRoot_primitive F n hn
  have hz : IsPrimitiveRoot z (q ^ n - 1) := isPrimitiveRoot_residue F hn hζ
  have hq : 1 < q := Finite.one_lt_card
  have hqn : 0 < q ^ n := pow_pos (zero_lt_one.trans hq) _
  apply le_antisymm
  · have hpow : z ^ q ^ n = z := by
      calc
        z ^ q ^ n = z ^ (q ^ n - 1 + 1) := by rw [Nat.sub_add_cancel hqn]
        _ = z := by rw [pow_succ, hz.pow_eq_one, one_mul]
    have hdiv : minpoly κ z ∣ X ^ q ^ n - X := minpoly.dvd κ z (by
      rw [map_sub, map_pow, aeval_X, hpow, sub_self])
    have hint : IsIntegral κ z := Algebra.IsIntegral.isIntegral _
    have hdeg := (minpoly.irreducible hint).natDegree_dvd_of_dvd_X_pow_card_pow_sub_X hdiv
    calc
      Module.finrank F E = (minpoly F (ζ : Ω)).natDegree :=
        IntermediateField.adjoin.finrank (Algebra.IsIntegral.isIntegral _)
      _ ≤ (minpoly κ z).natDegree := natDegree_minpoly_le F hn hζ
      _ ≤ n := Nat.le_of_dvd hn hdeg
  · let ζE : E := ⟨ζ, IntermediateField.mem_adjoin_simple_self F (ζ : Ω)⟩
    let a : extensionIntegers F E := ⟨ζE, by
      have hs := spectralNorm.eq_of_tower (K := F) (L := Ω) ζE
      exact hs.le.trans ζ.property⟩
    let y := residue (extensionIntegers F E) a
    let i := residueInclusion F Ω E
    have hy : IsPrimitiveRoot y (q ^ n - 1) :=
      IsPrimitiveRoot.of_map_of_injective (f := i) (show IsPrimitiveRoot (i y) _ from hz)
        i.injective
    have hy0 : y ≠ 0 := by
      intro h
      have hp := hy.pow_eq_one
      rw [h, zero_pow (teichOrder_ne_zero F hn)] at hp
      exact zero_ne_one hp
    let : Finite (ResidueField (extensionIntegers F E)) := finiteIntermediate_residue_finite F E
    let : Fintype (ResidueField (extensionIntegers F E)) := Fintype.ofFinite _
    have hdvd : q ^ n - 1 ∣ Nat.card (ResidueField (extensionIntegers F E)) - 1 := by
      rw [Nat.card_eq_fintype_card (α := ResidueField (extensionIntegers F E))]
      exact hy.dvd_of_pow_eq_one _ (FiniteField.pow_card_sub_one_eq_one _ hy0)
    have hd := Nat.le_of_dvd (Nat.sub_pos_of_lt
      (show 1 < Nat.card (ResidueField (extensionIntegers F E)) from Finite.one_lt_card)) hdvd
    have hc : Nat.card (ResidueField (extensionIntegers F E)) = q ^ Module.finrank F E := by
      rw [Module.natCard_eq_pow_finrank (K := κ),
        (arithmeticUnramified_iff_residue_finrank F E).mp
          (finiteUnramifiedFieldOfDegree_unramified F n hn)]
    apply (Nat.pow_le_pow_iff_right hq).mp
    calc
      q ^ n = q ^ n - 1 + 1 := (Nat.sub_add_cancel hqn).symm
      _ ≤ Nat.card (ResidueField (extensionIntegers F E)) - 1 + 1 := Nat.add_le_add_right hd 1
      _ = Nat.card (ResidueField (extensionIntegers F E)) := Nat.sub_add_cancel Nat.card_pos
      _ = q ^ Module.finrank F E := hc

/-- Every positive degree occurs for a finite Galois arithmetic-unramified
intermediate field of the separable closure. -/
theorem exists_finiteUnramified_finrank (n : ℕ) (hn : 0 < n) :
    ∃ E : IntermediateField F Ω, FiniteDimensional F E ∧ IsGalois F E ∧
      ArithmeticUnramified F E ∧ Module.finrank F E = n :=
  ⟨finiteUnramifiedFieldOfDegree F n hn, inferInstance, inferInstance,
    finiteUnramifiedFieldOfDegree_unramified F n hn,
    finiteUnramifiedFieldOfDegree_finrank F n hn⟩

end Langlands.ClassFieldTheory.Local
