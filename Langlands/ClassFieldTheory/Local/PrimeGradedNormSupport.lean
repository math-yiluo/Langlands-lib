import Langlands.ClassFieldTheory.Local.PrimeRamifiedGradedNormStatement
import Langlands.ClassFieldTheory.Local.PrimeRamificationArithmeticSupport
import Langlands.ClassFieldTheory.Local.NormOrderProof
import Mathlib.RingTheory.Norm.Transitivity

/-! Elementary residue and norm facts for the graded norm assembly. -/

noncomputable section
namespace Langlands.LocalClassField.PrimeGradedNorm
open Langlands.PadicField.TopologicalData Langlands.Weil.Local
universe u v
variable {p : ℕ} [Fact p.Prime]
variable (F : PadicField.{u} p) (L : PadicField.{v} p)
variable [Algebra F.Carrier L.Carrier] [IsScalarTower (Padic p) F.Carrier L.Carrier]
variable [FiniteDimensional F.Carrier L.Carrier]


variable (htot : L.canonicalTopologicalData.ramificationIndex =
  Module.finrank F.Carrier L.Carrier * F.canonicalTopologicalData.ramificationIndex)
include htot

omit [FiniteDimensional F.Carrier L.Carrier] in
theorem residue_bijective : Function.Bijective (relativeResidueMap F.canonicalTopologicalData L.canonicalTopologicalData) := by
  refine ⟨(relativeResidueMap F.canonicalTopologicalData L.canonicalTopologicalData).injective, ?_⟩
  rw [relativeResidueMap_canonical]
  let := extensionResidueAlgebra F L
    (IsScalarTower.toAlgHom (Padic p) F.Carrier L.Carrier)
  have hr := extensionResidueDegree_supplied_eq_one F L htot
  intro x
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero'
    (1 : L.canonicalTopologicalData.ResidueField) one_ne_zero).mp hr x
  exact ⟨c, by simpa only [Algebra.smul_def, mul_one, RingHom.algebraMap_toAlgebra] using hc⟩

theorem residueDegree_eq : L.canonicalTopologicalData.residueDegree = F.canonicalTopologicalData.residueDegree := by
  have h := L.canonicalTopologicalData.ramificationIndex_mul_residueDegree
  rw [htot, ← Module.finrank_mul_finrank (Padic p) F.Carrier L.Carrier,
    ← F.canonicalTopologicalData.ramificationIndex_mul_residueDegree] at h
  have he : F.canonicalTopologicalData.ramificationIndex * Module.finrank F.Carrier L.Carrier *
      L.canonicalTopologicalData.residueDegree = F.canonicalTopologicalData.ramificationIndex * Module.finrank F.Carrier L.Carrier *
      F.canonicalTopologicalData.residueDegree := by nlinarith [h]
  exact Nat.eq_of_mul_eq_mul_left
    (Nat.mul_pos F.canonicalTopologicalData.ramificationIndex_pos (Module.finrank_pos)) he

theorem ord_norm (x : L.Carrier) : F.canonicalTopologicalData.ord (Algebra.norm F.Carrier x) = L.canonicalTopologicalData.ord x := by
  have h := residueDegree_mul_ord_relative_norm F L F.canonicalTopologicalData L.canonicalTopologicalData x
  rw [residueDegree_eq F L htot] at h
  exact mul_left_cancel₀ (by exact_mod_cast F.canonicalTopologicalData.residueDegree_pos.ne') h

theorem ord_algebraMap (x : F.Carrier) :
    L.canonicalTopologicalData.ord (algebraMap F.Carrier L.Carrier x) =
      (Module.finrank F.Carrier L.Carrier : ℤ) * F.canonicalTopologicalData.ord x := by
  have h := ramificationIndex_mul_ord_relative_algebraMap F L F.canonicalTopologicalData L.canonicalTopologicalData x
  rw [htot, Nat.cast_mul] at h
  apply mul_left_cancel₀ (show (F.canonicalTopologicalData.ramificationIndex : ℤ) ≠ 0 by
    exact_mod_cast F.canonicalTopologicalData.ramificationIndex_pos.ne')
  linear_combination h

omit htot in
theorem norm_integral (x : L.canonicalTopologicalData.Integers) : Algebra.norm F.Carrier (x : L.Carrier) ∈ F.canonicalTopologicalData.Integers := by
  rw [← F.canonicalTopologicalData.normalizedAbs_le_one_iff_mem_integers, normalizedAbs_relative_norm F L F.canonicalTopologicalData L.canonicalTopologicalData]
  exact (L.canonicalTopologicalData.normalizedAbs_le_one_iff_mem_integers _).mpr x.property

omit htot in
def integerNorm (x : L.canonicalTopologicalData.Integers) : F.canonicalTopologicalData.Integers :=
  ⟨Algebra.norm F.Carrier (x : L.Carrier), norm_integral F L x⟩

omit htot in
@[simp] theorem integerNorm_coe (x : L.canonicalTopologicalData.Integers) :
    (integerNorm F L x : F.Carrier) = Algebra.norm F.Carrier (x : L.Carrier) := rfl

variable [IsGalois F.Carrier L.Carrier]

theorem residue_norm (x : L.canonicalTopologicalData.Integers) :
    relativeResidueMap F.canonicalTopologicalData L.canonicalTopologicalData (F.canonicalTopologicalData.residue (integerNorm F L x)) =
      L.canonicalTopologicalData.residue x ^ Module.finrank F.Carrier L.Carrier := by
  classical
  have hg : ∀ σ : Gal(L.Carrier/F.Carrier),
      L.canonicalTopologicalData.residue (Ramification.Padic.integerAutomorphism L.canonicalTopologicalData F.Carrier σ x) = L.canonicalTopologicalData.residue x := by
    intro σ
    have hm : σ ∈ Ramification.Padic.lowerRamificationGroup L.canonicalTopologicalData F.Carrier 0 := by
      rw [Ramification.Padic.lowerRamificationGroup_zero,
        inertia_eq_top_of_canonical_totalRamification F L htot]
      trivial
    have hd := (Ramification.Padic.mem_lowerRamificationGroup L.canonicalTopologicalData F.Carrier 0 σ).mp hm x
    rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff]
    simpa using hd
  have he : relativeIntegerMap F.canonicalTopologicalData L.canonicalTopologicalData (integerNorm F L x) =
      ∏ σ : Gal(L.Carrier/F.Carrier), Ramification.Padic.integerAutomorphism L.canonicalTopologicalData F.Carrier σ x := by
    apply Subtype.ext
    change algebraMap F.Carrier L.Carrier (Algebra.norm F.Carrier (x : L.Carrier)) = _
    rw [Algebra.norm_eq_prod_automorphisms]
    change _ = (L.canonicalTopologicalData.Integers.subtype (∏ σ : Gal(L.Carrier/F.Carrier),
      Ramification.Padic.integerAutomorphism L.canonicalTopologicalData F.Carrier σ x))
    rw [map_prod]
    rfl
  rw [relativeResidueMap_residue, he, map_prod]
  simp only [hg, Finset.prod_const, Finset.card_univ]
  rw [Fintype.card_eq_nat_card, IsGalois.card_aut_eq_finrank]

theorem zero_coordinate (x : L.canonicalTopologicalData.unitFiltration 0) (y : F.canonicalTopologicalData.unitFiltration 0)
    (hxy : (y : F.Carrierˣ) = normUnits F.Carrier L.Carrier (x : L.Carrierˣ)) :
    Units.map (relativeResidueMap F.canonicalTopologicalData L.canonicalTopologicalData).toMonoidHom (F.canonicalTopologicalData.zeroUnitCoordinate y) =
      L.canonicalTopologicalData.zeroUnitCoordinate x ^ Module.finrank F.Carrier L.Carrier := by
  apply Units.ext
  change relativeResidueMap F.canonicalTopologicalData L.canonicalTopologicalData (F.canonicalTopologicalData.residue (F.canonicalTopologicalData.filtrationIntegerUnit 0 y : F.canonicalTopologicalData.Integers)) =
    L.canonicalTopologicalData.residue (L.canonicalTopologicalData.filtrationIntegerUnit 0 x : L.canonicalTopologicalData.Integers) ^ _
  have he : (F.canonicalTopologicalData.filtrationIntegerUnit 0 y : F.canonicalTopologicalData.Integers) =
      integerNorm F L (L.canonicalTopologicalData.filtrationIntegerUnit 0 x : L.canonicalTopologicalData.Integers) := by
    apply Subtype.ext
    rw [F.canonicalTopologicalData.filtrationIntegerUnit_coe, integerNorm_coe, L.canonicalTopologicalData.filtrationIntegerUnit_coe]
    exact congrArg (fun z : F.Carrierˣ => (z : F.Carrier)) hxy
  rw [he]
  exact residue_norm F L htot _

theorem degree_eq_prime_of_positive_break
    (hell : Nat.Prime (Module.finrank F.Carrier L.Carrier))
    (t : ℕ) (ht : 0 < t)
    (hpat : ∀ i : ℕ, Ramification.Padic.lowerRamificationGroup L.canonicalTopologicalData F.Carrier i =
      if i ≤ t then ⊤ else ⊥) : Module.finrank F.Carrier L.Carrier = p := by
  apply (lowerRamificationGroup_one_eq_top_iff_prime_degree F L hell htot).mp
  simpa [Nat.succ_le_iff.mpr ht] using hpat 1

end Langlands.LocalClassField.PrimeGradedNorm
