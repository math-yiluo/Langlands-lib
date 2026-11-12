import Langlands.ClassFieldTheory.Local.NormUnitImagePrimeStep
import Langlands.ClassFieldTheory.Local.NormUnitImageCardinality
import Langlands.ClassFieldTheory.Local.UnitFiltrationConductor
import Langlands.LocalFactor.Ramification.Herbrand.ArithmeticStatement
import Langlands.LocalFactor.Ramification.Herbrand.TransportProof

/-! # Norm images of unit filtrations in finite abelian local extensions

The level claims of `NormUnitImageTower` hold for every finite abelian
extension, by induction on the degree through the fixed field of a subgroup of
prime order. Together with the local norm index they give the order of the
image of every unit level in the norm quotient.
-/

noncomputable section

namespace Langlands.LocalClassField.NormUnitImage

open Ramification Langlands.Weil.Local

universe u v

variable {p : ℕ} [Fact p.Prime]

section DegreeOne

variable (K : PadicField.{u} p) (L : PadicField.{v} p) [Algebra K.Carrier L.Carrier]
  [IsScalarTower (Padic p) K.Carrier L.Carrier] [FiniteDimensional K.Carrier L.Carrier]

/-- An extension of degree one has the ramification index of its base. -/
theorem ramificationIndex_eq_of_finrank_eq_one
    (h1 : Module.finrank K.Carrier L.Carrier = 1) :
    K.canonicalTopologicalData.ramificationIndex =
      L.canonicalTopologicalData.ramificationIndex := by
  have hord := ramificationIndex_mul_ord_relative_algebraMap K L K.canonicalTopologicalData
    L.canonicalTopologicalData K.canonicalTopologicalData.uniformizer
  rw [K.canonicalTopologicalData.ord_uniformizer, mul_one] at hord
  have hdeg := PadicField.ramificationIndex_mul_extensionResidueDegree K L
    (IsScalarTower.toAlgHom (Padic p) K.Carrier L.Carrier)
  rw [extensionDegree_suppliedAlgebra, h1, one_mul] at hdeg
  set TK := K.canonicalTopologicalData
  set TL := L.canonicalTopologicalData
  set c := TL.ord (algebraMap K.Carrier L.Carrier TK.uniformizer)
  set f := extensionResidueDegree K L (IsScalarTower.toAlgHom (Padic p) K.Carrier L.Carrier)
  have heK := TK.ramificationIndex_pos
  have heL := TL.ramificationIndex_pos
  have hf : 0 < f := by
    rcases Nat.eq_zero_or_pos f with hf | hf
    · rw [hf, mul_zero] at hdeg
      omega
    · exact hf
  have hc : 0 < c := by
    by_contra hc
    have h0 : (TK.ramificationIndex : ℤ) * c ≤ 0 :=
      Int.mul_nonpos_of_nonneg_of_nonpos (Int.natCast_nonneg _) (not_lt.mp hc)
    have hL0 : (0 : ℤ) < TL.ramificationIndex := by exact_mod_cast heL
    omega
  have hle : TL.ramificationIndex ≤ TK.ramificationIndex := by
    rw [← hdeg]
    exact Nat.le_mul_of_pos_right _ hf
  have hge : (TK.ramificationIndex : ℤ) ≤ TL.ramificationIndex := by
    rw [← hord]
    exact le_mul_of_one_le_right (Int.natCast_nonneg _) hc
  omega

/-- The level claims for an abelian extension of degree one. -/
theorem levelClaims_of_finrank_eq_one [IsAbelianGalois K.Carrier L.Carrier]
    (h1 : Module.finrank K.Carrier L.Carrier = 1) : LevelClaims K L :=
  levelClaims_of_ramificationIndex_eq K L (ramificationIndex_eq_of_finrank_eq_one K L h1)

end DegreeOne

section Induction

/-- The level claims hold for every finite abelian extension, by strong
induction on the degree. -/
theorem levelClaims_of_finrank_eq (K : PadicField.{u} p) (n : ℕ) :
    ∀ (L : PadicField.{v} p) [Algebra K.Carrier L.Carrier]
      [IsScalarTower (Padic p) K.Carrier L.Carrier] [FiniteDimensional K.Carrier L.Carrier]
      [IsAbelianGalois K.Carrier L.Carrier],
      Module.finrank K.Carrier L.Carrier = n → LevelClaims K L := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro L _ _ _ _ hn
  have hpos : 0 < n := hn ▸ Module.finrank_pos
  rcases Nat.lt_or_ge n 2 with hlt | h2
  · exact levelClaims_of_finrank_eq_one K L (by omega)
  obtain ⟨q, hq, hqn⟩ := Nat.exists_prime_and_dvd (show n ≠ 1 by omega)
  have := Fact.mk hq
  have hcard : Nat.card Gal(L.Carrier/K.Carrier) = n := by
    rw [IsGalois.card_aut_eq_finrank, hn]
  obtain ⟨σ, hσ⟩ := exists_prime_orderOf_dvd_card' q (hcard ▸ hqn)
  set H := Subgroup.zpowers σ
  set E := Padic.fixedPadicField K L H
  have : IsScalarTower (Padic p) K.Carrier E.Carrier :=
    IsScalarTower.of_algebraMap_eq fun x =>
      Subtype.ext (IsScalarTower.algebraMap_apply (Padic p) K.Carrier L.Carrier x)
  have hEL : Module.finrank E.Carrier L.Carrier = q := by
    change Module.finrank (IntermediateField.fixedField H) L.Carrier = q
    rw [IntermediateField.finrank_fixedField_eq_card, Nat.card_zpowers, hσ]
  have hKE : Module.finrank K.Carrier E.Carrier * q = n := by
    rw [← hEL, Module.finrank_mul_finrank, hn]
  have hlt : Module.finrank K.Carrier E.Carrier < n := by
    have hq2 := hq.two_le
    have hKE0 : 0 < Module.finrank K.Carrier E.Carrier := Module.finrank_pos
    nlinarith
  exact levelClaims_tower K L E (ih _ hlt E rfl) (levelClaims_of_prime E L (hEL ▸ hq))

/-- The level claims hold for every finite abelian extension. -/
theorem levelClaims_of_isAbelianGalois (K : PadicField.{u} p) (L : PadicField.{v} p)
    [Algebra K.Carrier L.Carrier] [IsScalarTower (Padic p) K.Carrier L.Carrier]
    [FiniteDimensional K.Carrier L.Carrier] [IsAbelianGalois K.Carrier L.Carrier] :
    LevelClaims K L :=
  levelClaims_of_finrank_eq K _ L rfl

end Induction

section Realization

/-- The unit filtration does not depend on the supplied topological data. -/
theorem unitFiltration_eq_of_topologicalData {F : PadicField.{u} p}
    (T T' : F.TopologicalData) (n : ℕ) : T.unitFiltration n = T'.unitFiltration n := by
  have hv : ∀ x : F.Carrier, T'.discreteValuation x = T.discreteValuation x :=
    NYLL.discreteValuation_eq_of_algEquiv AlgEquiv.refl T T'
  rw [T.unitFiltration_eq_principalUnits, T'.unitFiltration_eq_principalUnits]
  ext x
  change (_ ∧ _) ↔ (_ ∧ _)
  rw [hv, hv]

end Realization

/-- **Norm images of unit levels.** For a finite abelian extension `E/F` of
p-adic fields, arbitrary supplied topological data and every real `a ≥ 0`, the
image of `U_F^{⌈a⌉}` in `Fˣ / N(Eˣ)` has the order of the upper ramification
group `G^a`. -/
theorem finiteAbelianNormUnitImageCardinality :
    FiniteAbelianNormUnitImageCardinality.{u, v} := by
  intro p _ F E _ _ _ T S a ha
  have : FiniteDimensional F.Carrier E.Carrier :=
    Module.Finite.of_restrictScalars_finite (Padic p) F.Carrier E.Carrier
  obtain ⟨-, hV, hWZ⟩ := levelClaims_of_isAbelianGalois F E a ha
  have hidx := normSubgroup_index_eq_finrank F E
  rw [unitFiltration_eq_of_topologicalData T F.canonicalTopologicalData,
    HerbrandBridge.upperRamificationGroup_eq_of_realization S E.canonicalTopologicalData F.Carrier a]
  refine card_map_mk_eq_of_dvd ?_ (Subgroup.map_le_range _ _) hV ?_
  · rw [hidx]
    exact Module.finrank_pos.ne'
  · rw [hidx]
    exact hWZ

end Langlands.LocalClassField.NormUnitImage
