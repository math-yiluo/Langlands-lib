import Langlands.BushnellKutzko.SubfieldLayerObstructions

/-! # Coprimality and residue generation on the layers -/

noncomputable section

open ValuativeRel IsLocalRing IsDiscreteValuationRing

namespace Langlands.BushnellKutzko.LatticeChain

universe uF uV uE

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {V : Type uV} [AddCommGroup V] [Module F V]
  (𝓛 : LatticeChain 𝒪[F] F V) (E : Type uE) [Field E] [Algebra F E]
  [Module E V] [IsScalarTower F E V]
  (hE : ∀ a : Eˣ, subfieldUnits F E V a ∈ 𝓛.stabilizer)

local notation "𝒪ₑ[" F "," E "]" => subfieldIntegers F E
local notation "kₑ[" F "," E "]" => ResidueField (subfieldIntegers F E)

/-- For the given pair of units, intertwining them forces intertwining every field unit. -/
def subfieldLayerGeneration (b c : Eˣ) : Prop :=
  ∀ D : ∀ i, Module.End 𝒪[F] (𝓛.Layer i),
    b ∈ 𝓛.subfieldLayerCommutingSubgroup E hE D →
    c ∈ 𝓛.subfieldLayerCommutingSubgroup E hE D →
    ∀ a : Eˣ, a ∈ 𝓛.subfieldLayerCommutingSubgroup E hE D

private theorem bezout_unit_relations {G : Type*} [CommGroup G]
    (b c : G) (ν e r s : ℤ) (h : ν * r + e * s = 1) :
    b = (b ^ r * c ^ s) ^ ν * (c ^ (-ν) * b ^ e) ^ s ∧
    c = (b ^ r * c ^ s) ^ e * (c ^ (-ν) * b ^ e) ^ (-r) := by
  constructor
  · symm
    calc
      _ = (b ^ (r * ν) * c ^ (s * ν)) * (c ^ (-ν * s) * b ^ (e * s)) := by
        simp only [mul_zpow, ← zpow_mul]
      _ = b ^ (r * ν + e * s) * c ^ (s * ν + -ν * s) := by
        rw [zpow_add, zpow_add]
        ac_rfl
      _ = b := by
        rw [mul_comm r ν, h, show s * ν + -ν * s = 0 by ring, zpow_one, zpow_zero, mul_one]
  · symm
    calc
      _ = (b ^ (r * e) * c ^ (s * e)) * (c ^ (-ν * -r) * b ^ (e * -r)) := by
        simp only [mul_zpow, ← zpow_mul]
      _ = b ^ (r * e + e * -r) * c ^ (s * e + -ν * -r) := by
        rw [zpow_add, zpow_add]
        ac_rfl
      _ = c := by
        rw [show r * e + e * -r = 0 by ring, show s * e + -ν * -r = 1 by linarith [h],
          zpow_zero, one_mul, zpow_one]

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- The shift of a product of powers is the corresponding integer linear combination. -/
theorem fieldShift_zpow_mul (b c : Eˣ) (r s : ℤ) :
    (𝓛.fieldShift E hE (b ^ r * c ^ s)).toAdd =
      (𝓛.fieldShift E hE b).toAdd * r + (𝓛.fieldShift E hE c).toAdd * s := by
  rw [map_mul, map_zpow, map_zpow]
  change ((𝓛.fieldShift E hE b) ^ r).toAdd + ((𝓛.fieldShift E hE c) ^ s).toAdd = _
  rw [Int.toAdd_zpow, Int.toAdd_zpow]

variable [IsDiscreteValuationRing 𝒪ₑ[F,E]] [IsFractionRing 𝒪ₑ[F,E] E]

/-- The two shift generators test all field units exactly when the exponents are
coprime and the shift-zero combination generates the residue field. -/
theorem subfieldLayerGeneration_iff (b c : Eˣ) {ϖ : 𝒪ₑ[F,E]} (hϖ : Irreducible ϖ) (t ν e : ℤ)
    (ht : 0 < t) (hϖt : (𝓛.fieldShift E hE (subfieldIntegerUnit E hϖ.ne_zero)).toAdd = t)
    (hb : (𝓛.fieldShift E hE b).toAdd = t * ν) (hc : (𝓛.fieldShift E hE c).toAdd = t * e)
    (u : 𝒪ₑ[F,E]ˣ) (hu : c ^ (-ν) * b ^ e = subfieldIntegerUnits E u) :
    𝓛.subfieldLayerGeneration E hE b c ↔ Int.gcd ν e = 1 ∧
      Algebra.adjoin 𝒪[F] ({residue (𝒪ₑ[F,E]) (u : 𝒪ₑ[F,E])} : Set kₑ[F,E]) = ⊤ := by
  let S := Algebra.adjoin 𝒪[F] ({residue (𝒪ₑ[F,E]) (u : 𝒪ₑ[F,E])} : Set kₑ[F,E])
  have hres : residue (𝒪ₑ[F,E]) (u : 𝒪ₑ[F,E]) ∈ S :=
    Algebra.subset_adjoin (Set.mem_singleton _)
  let r := Int.gcdA ν e
  let s := Int.gcdB ν e
  let a := b ^ r * c ^ s
  have hbez (h : Int.gcd ν e = 1) : ν * r + e * s = 1 := by
    have h' := Int.gcd_eq_gcd_ab ν e
    rw [h, Nat.cast_one] at h'
    exact h'.symm
  have hat (h : Int.gcd ν e = 1) : (𝓛.fieldShift E hE a).toAdd = t := by
    rw [fieldShift_zpow_mul, hb, hc, mul_assoc, mul_assoc, ← mul_add, hbez h, mul_one]
  constructor
  · intro hgen
    have hgcd : Int.gcd ν e = 1 := by
      let m := t * (Int.gcd ν e : ℤ)
      let D := 𝓛.layerIndicator m
      have hbD : b ∈ 𝓛.subfieldLayerCommutingSubgroup E hE D := by
        apply (𝓛.layerIndicator_commutes_iff m (𝓛.subfieldStabilizer E hE b)).mpr
        rw [subfieldStabilizer_shift, hb]
        exact mul_dvd_mul_left t (Int.gcd_dvd_left ν e)
      have hcD : c ∈ 𝓛.subfieldLayerCommutingSubgroup E hE D := by
        apply (𝓛.layerIndicator_commutes_iff m (𝓛.subfieldStabilizer E hE c)).mpr
        rw [subfieldStabilizer_shift, hc]
        exact mul_dvd_mul_left t (Int.gcd_dvd_right ν e)
      have hpD : subfieldIntegerUnit E hϖ.ne_zero ∈ 𝓛.subfieldLayerCommutingSubgroup E hE D :=
        hgen D hbD hcD _
      have hd := (𝓛.layerIndicator_commutes_iff m _).mp hpD
      rw [subfieldStabilizer_shift, hϖt] at hd
      obtain ⟨k, hk⟩ := hd
      have hdvd : (Int.gcd ν e : ℤ) ∣ (1 : ℤ) := by
        refine ⟨k, mul_left_cancel₀ ht.ne' ?_⟩
        rw [mul_one, ← mul_assoc]
        exact hk
      exact Nat.dvd_one.mp (Int.natCast_dvd_natCast.mp hdvd)
    refine ⟨hgcd, ?_⟩
    by_contra hS
    obtain ⟨D, haD, hS_le, hD⟩ := 𝓛.exists_subfieldOrbitFamily_of_ne_top E hE a (hat hgcd) ht S hS
    let H := 𝓛.subfieldLayerCommutingSubgroup E hE D
    have huD : subfieldIntegerUnits E u ∈ H :=
      (𝓛.integerUnit_mem_subfieldLayerCommutingSubgroup_iff E hE D u).mpr (hS_le hres)
    have hyD : c ^ (-ν) * b ^ e ∈ H := hu ▸ huD
    obtain ⟨hbr, hcr⟩ := bezout_unit_relations b c ν e r s (hbez hgcd)
    have hbD : b ∈ H := hbr ▸ H.mul_mem (H.zpow_mem haD ν) (H.zpow_mem hyD s)
    have hcD : c ∈ H := hcr ▸ H.mul_mem (H.zpow_mem haD e) (H.zpow_mem hyD (-r))
    apply hD (top_unique ?_)
    intro z _
    by_cases hz : z = 0
    · rw [hz]
      exact zero_mem _
    · obtain ⟨x, rfl⟩ := residue_surjective z
      obtain ⟨w, rfl⟩ := (residue_ne_zero_iff_isUnit x).mp hz
      exact (𝓛.integerUnit_mem_subfieldLayerCommutingSubgroup_iff E hE D w).mp (hgen D hbD hcD _)
  · rintro ⟨hgcd, hS⟩ D hbD hcD
    let H := 𝓛.subfieldLayerCommutingSubgroup E hE D
    have haD : a ∈ H := H.mul_mem (H.zpow_mem hbD r) (H.zpow_mem hcD s)
    have huD : subfieldIntegerUnits E u ∈ H := hu ▸ H.mul_mem (H.zpow_mem hcD (-ν)) (H.zpow_mem hbD e)
    have hC : 𝓛.commutingResidueScalars E hE D = ⊤ := by
      apply top_unique
      rw [← hS]
      apply Algebra.adjoin_le
      intro z hz
      obtain rfl := Set.mem_singleton_iff.mp hz
      exact (𝓛.integerUnit_mem_subfieldLayerCommutingSubgroup_iff E hE D u).mp huD
    have hunit (w : 𝒪ₑ[F,E]ˣ) : subfieldIntegerUnits E w ∈ H := by
      apply (𝓛.integerUnit_mem_subfieldLayerCommutingSubgroup_iff E hE D w).mpr
      rw [hC]
      simp
    obtain ⟨n, w, haw⟩ := subfieldUnit_factorization E hϖ a
    have hn : n = 1 := by
      have ha := 𝓛.fieldShift_eq_mul_of_factorization E hE hϖ.ne_zero haw
      rw [hat hgcd, hϖt] at ha
      exact (mul_left_cancel₀ ht.ne' ((mul_one t).trans ha)).symm
    have hpD : subfieldIntegerUnit E hϖ.ne_zero ∈ H := by
      have h := H.mul_mem (H.inv_mem (hunit w)) haD
      rwa [haw, hn, zpow_one, ← mul_assoc, inv_mul_cancel, one_mul] at h
    intro v
    obtain ⟨n', w', h'⟩ := subfieldUnit_factorization E hϖ v
    exact h' ▸ H.mul_mem (hunit w') (H.zpow_mem hpD n')

end Langlands.BushnellKutzko.LatticeChain
