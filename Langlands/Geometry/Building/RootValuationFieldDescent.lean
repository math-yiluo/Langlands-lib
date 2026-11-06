import Langlands.Geometry.Building.PositiveConeFieldDescent

/-! # Full valuation descent on the actual restricted root family -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace
open Langlands.GroupScheme.GaloisPointComparison
open Langlands.LinearAlgebra.RationalSpan

namespace Langlands.GroupScheme.RelativeRoot

variable {k : Type u} [Field k]
  {S : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] [Smooth G.X.hom] (i : S.toGrp ⟶ G)
  [Mono i.hom.hom.left]

/-- On one positive root ray, a natural multiple which is an actual root has
coefficient at most two. -/
theorem HasOppositeFactorPairs.nat_multiple_le_two
    (hS : IsSplitTorus S.toGrp) (hE : HasOppositeFactorPairs i)
    {a : characterLattice S} (ha : a ∈ relativeRoots i)
    {n : ℕ} (hn : 0 < n) (hnroot : n • a ∈ relativeRoots i) : n ≤ 2 := by
  let ν := hE.rootCoroot i hS ⟨a, ha⟩
  have hself : latticePairing S a ν = 2 := hE.rootCoroot_pairing i hS ⟨a, ha⟩
  rcases hE.root_eq_or_twice_of_common_positive_multiple i hS hnroot ha
      (by omega : 0 < (1 : ℕ)) hn (by simp only [one_smul]) with h | h | h
  all_goals
    have hp := congrArg (fun c => latticePairing S c ν) h
    simp only [map_nsmul, LinearMap.smul_apply, nsmul_eq_mul, hself,
      Nat.cast_ofNat] at hp
    omega

/-- Nonopposite dependent actual roots agree up to doubling. -/
theorem HasOppositeFactorPairs.root_eq_or_twice_of_not_independent
    (hS : IsSplitTorus S.toGrp) (hE : HasOppositeFactorPairs i)
    {a a' : characterLattice S} (ha : a ∈ relativeRoots i) (ha' : a' ∈ relativeRoots i)
    (hnon : ∀ t : ℝ, 0 < t → ((1 : ℝ) ⊗ₜ[ℤ] a' : Vstar S) ≠
      -(t • (1 : ℝ) ⊗ₜ[ℤ] a))
    (hlin : ¬ LinearIndependent ℚ ![toRat a, toRat a']) :
    a = a' ∨ a = 2 • a' ∨ a' = 2 • a := by
  have haQ : toRat a ≠ 0 := by
    intro h
    exact ha.1 (hS.character_toRat_injective (h.trans (map_zero toRat).symm))
  obtain ⟨q, hq⟩ : ∃ q : ℚ, q • toRat a = toRat a' := by
    simpa only [LinearIndependent.pair_iff' haQ, not_forall, not_not] using hlin
  have hq0 : q ≠ 0 := by
    intro h
    have : toRat a' = 0 := by simpa [h] using hq.symm
    exact ha'.1 (hS.character_toRat_injective (this.trans (map_zero toRat).symm))
  have hqpos : 0 < q := by
    apply lt_of_le_of_ne _ hq0.symm
    apply le_of_not_gt
    intro hneg
    have hreal := congrArg (toReal (characterLattice S)) hq.symm
    rw [toReal_toRat, map_smul, toReal_toRat, ← Rat.cast_smul_eq_qsmul ℝ] at hreal
    apply hnon (-(q : ℝ)) (by exact_mod_cast neg_pos.mpr hneg)
    simpa only [neg_smul, TensorProduct.neg_tmul, neg_neg] using hreal
  have hnum : 0 < q.num := Rat.num_pos.mpr hqpos
  have hnat : (q.num.toNat : ℚ) = (q.num : ℚ) := by
    exact_mod_cast Int.toNat_of_nonneg hnum.le
  have hcoef : (q.num.toNat : ℚ) = (q.den : ℚ) * q := by
    rw [hnat]
    have hrep := (div_eq_iff (Nat.cast_ne_zero.mpr q.den_nz)).mp (Rat.num_div_den q)
    simpa only [mul_comm] using hrep
  have hmult : q.num.toNat • a = q.den • a' := by
    apply hS.character_toRat_injective
    simp only [map_nsmul]
    calc
      q.num.toNat • toRat a = (q.num.toNat : ℚ) • toRat a := by rw [Nat.cast_smul_eq_nsmul]
      _ = ((q.den : ℚ) * q) • toRat a := by rw [hcoef]
      _ = (q.den : ℚ) • toRat a' := by rw [mul_smul, hq]
      _ = q.den • toRat a' := by rw [Nat.cast_smul_eq_nsmul]
  exact hE.root_eq_or_twice_of_common_positive_multiple i hS ha ha'
    (by omega) q.pos hmult

end Langlands.GroupScheme.RelativeRoot

namespace Langlands.Geometry.Building

variable {k : Type u} [Field k]
  {S : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] [Smooth G.X.hom] (i : S.toGrp ⟶ G)
  [Mono i.hom.hom.left]

/-- Every nonopposite actual root pair admits one additive depth with exactly
the required values on all actual positive integral output roots. -/
theorem exists_additive_outputDepth
    (hS : IsSplitTorus S.toGrp) (hE : RelativeRoot.HasOppositeFactorPairs i)
    {a a' : characterLattice S} (ha : a ∈ relativeRoots i) (ha' : a' ∈ relativeRoots i)
    (hnon : ∀ t : ℝ, 0 < t → ((1 : ℝ) ⊗ₜ[ℤ] a' : Vstar S) ≠
      -(t • (1 : ℝ) ⊗ₜ[ℤ] a)) (r s : ℝ) :
    ∃ f : characterLattice S →+ ℝ,
      ∀ p q : ℕ, 0 < p → 0 < q → p • a + q • a' ∈ relativeRoots i →
        f (p • a + q • a') = p * r + q * s := by
  by_cases hlin : LinearIndependent ℚ ![toRat a, toRat a']
  · obtain ⟨f, hfa, hfa'⟩ := exists_additiveDepth_of_independent a a' hlin r s
    exact ⟨f, fun p q _ _ _ => by simp only [map_add, map_nsmul, nsmul_eq_mul, hfa, hfa']⟩
  · rcases hE.root_eq_or_twice_of_not_independent i hS ha ha' hnon hlin with h | h | h
    · subst a'
      let ν := hE.rootCoroot i hS ⟨a, ha⟩
      let f : characterLattice S →+ ℝ := ((r + s) / 4) •
        ((Int.castAddHom ℝ).comp ((latticePairing S).flip ν).toAddMonoidHom)
      refine ⟨f, ?_⟩
      intro p q hp hq hc
      have hroot : (p + q) • a ∈ relativeRoots i := by rwa [add_smul]
      have hle := hE.nat_multiple_le_two i hS ha (by omega) hroot
      have hp1 : p = 1 := by omega
      have hq1 : q = 1 := by omega
      have hself : latticePairing S a ν = 2 := hE.rootCoroot_pairing i hS ⟨a, ha⟩
      subst p
      subst q
      simp only [f, one_smul, AddMonoidHom.smul_apply, AddMonoidHom.comp_apply,
        Int.coe_castAddHom, LinearMap.toAddMonoidHom_coe, LinearMap.flip_apply,
        map_add, hself, Int.cast_ofNat, smul_eq_mul,
        Nat.cast_one, one_mul]
      ring
    · refine ⟨0, ?_⟩
      intro p q hp hq hc
      have hroot : (p * 2 + q) • a' ∈ relativeRoots i := by
        simpa only [h, smul_smul, ← add_smul] using hc
      have hle := hE.nat_multiple_le_two i hS ha' (by omega) hroot
      omega
    · refine ⟨0, ?_⟩
      intro p q hp hq hc
      have hroot : (p + q * 2) • a ∈ relativeRoots i := by
        simpa only [h, smul_smul, ← add_smul] using hc
      have hle := hE.nat_multiple_le_two i hS ha (by omega) hroot
      omega

section FieldExtension

variable {K : Type u} [Field K] [Algebra k K]

local notation "b" => algebraBaseMap k K
local notation "S_K" => CategoryTheory.Functor.obj (CommGroupScheme.baseChange b) S
local notation "G_K" => baseChanged k K G
local notation "i_K" => CategoryTheory.Functor.map (GroupScheme.baseChange b) i

private instance extendedAffine : IsAffineHom (G_K).X.hom := by
  change IsAffineHom (CategoryTheory.Limits.pullback.snd G.X.hom b)
  infer_instance

private instance extendedMono : Mono (i_K).hom.hom.left := by
  let : Mono i.hom.hom := Over.mono_of_mono_left _
  change Mono ((Over.pullback b).map i.hom.hom).left
  infer_instance

namespace IsRootDatumValuation

/-- V3 on the literal restricted family follows for every nonopposite root
pair and every real pair of depths, using collection only upstairs. -/
theorem fieldRestrict_commutator
    (hS : IsSplitTorus S.toGrp) (hE : RelativeRoot.HasOppositeFactorPairs i)
    {ψ : RootFunctionFamily S_K G_K} (hψ : IsRootDatumValuation (S := S_K) i_K ψ)
    (a : characterLattice S) (ha : a ∈ relativeRoots i)
    (a' : characterLattice S) (ha' : a' ∈ relativeRoots i)
    (hnon : ∀ t : ℝ, 0 < t → ((1 : ℝ) ⊗ₜ[ℤ] a' : Vstar S) ≠
      -(t • (1 : ℝ) ⊗ₜ[ℤ] a)) (r s : ℝ) :
    ⁅Subgroup.closure (rootFiltration i (RootFunctionFamily.fieldRestrict (k := k) ψ) a r),
      Subgroup.closure (rootFiltration i (RootFunctionFamily.fieldRestrict (k := k) ψ) a' s)⁆ ≤
      Subgroup.closure (⋃ (p : ℕ) (q : ℕ) (_ : 0 < p) (_ : 0 < q)
        (_ : p • a + q • a' ∈ relativeRoots i),
        rootFiltration i (RootFunctionFamily.fieldRestrict (k := k) ψ)
          (p • a + q • a') (p * r + q * s)) := by
  obtain ⟨ν, hapos, ha'pos⟩ :=
    hS.exists_cocharacter_pos_pair_of_not_opposite a a' ha.1 ha'.1 hnon
  obtain ⟨f, hf⟩ := exists_additive_outputDepth i hS hE ha ha' hnon r s
  exact fieldRestrict_commutator_of_outputDepth i hS hE ν a a' ha ha'
    hapos ha'pos hψ r s f hf

/-- Construct the valuation on the literal restricted family. The nontrivial
unit condition supplies V0; the original opposite pairs supply full V3. -/
def fieldRestrictValuation
    (hS : IsSplitTorus S.toGrp) (hE : RelativeRoot.HasOppositeFactorPairs i)
    {ψ : RootFunctionFamily S_K G_K} (hψ : IsRootDatumValuation (S := S_K) i_K ψ)
    (ω : Kˣ →* Multiplicative ℝ)
    (hcompat : IsSplitTorusCompatible (S := S_K) i_K (fun t => (ω t).toAdd) ψ)
    (hω : ∃ t : kˣ, (ω (Units.map (algebraMap k K).toMonoidHom t)).toAdd ≠ 0) :
    {φ : RootFunctionFamily S G // IsRootDatumValuation i φ} :=
  fieldRestrictValuationOfCommutator i hS hψ ω hcompat hω
    (fieldRestrict_commutator i hS hE hψ)

@[simp] theorem fieldRestrictValuation_val
    (hS : IsSplitTorus S.toGrp) (hE : RelativeRoot.HasOppositeFactorPairs i)
    {ψ : RootFunctionFamily S_K G_K} (hψ : IsRootDatumValuation (S := S_K) i_K ψ)
    (ω : Kˣ →* Multiplicative ℝ)
    (hcompat : IsSplitTorusCompatible (S := S_K) i_K (fun t => (ω t).toAdd) ψ)
    (hω : ∃ t : kˣ, (ω (Units.map (algebraMap k K).toMonoidHom t)).toAdd ≠ 0) :
    (fieldRestrictValuation i hS hE hψ ω hcompat hω).val =
      RootFunctionFamily.fieldRestrict (k := k) ψ := rfl

end IsRootDatumValuation

end FieldExtension

end Langlands.Geometry.Building
