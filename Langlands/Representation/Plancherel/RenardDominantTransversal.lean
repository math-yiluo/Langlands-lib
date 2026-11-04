import Langlands.Representation.Plancherel.RenardDominantValuation
import Mathlib.GroupTheory.Index
import Mathlib.Order.ConditionallyCompleteLattice.Basic

/-! # Dominant representatives by positive uniformizer translation -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct
open Langlands.GroupScheme Langlands.BruhatTits.Cartan
open scoped CategoryTheory.MonObj Pointwise TensorProduct

namespace Langlands.Plancherel.RenardCartan

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {Z : GroupScheme (Spec (CommRingCat.of F))}
  (s : S.toGrp ⟶ Z)

/-- Left translation by the uniformizer value of a natural cocharacter multiple. -/
def uniformizerTranslate (ν : cocharacterLattice S) (n : ℕ)
    (z : rationalPoints Z) : rationalPoints Z :=
  rationalPoints.map s (uniformizerSection S (Multiplicative.ofAdd (n • ν))) * z

/-- Actual uniformizer values have trivial full-lattice residue. -/
theorem latticeResidue_eq_one_of_mem_C0 {c : rationalPoints Z} (hc : c ∈ C0 S s) :
    latticeResidue s c = 1 := by
  apply (QuotientGroup.eq_one_iff (N := splitValuationImage s) _).mpr
  obtain ⟨n, rfl⟩ := (mem_C0 S s c).mp hc
  exact ⟨uniformizerSection S (Multiplicative.ofAdd n), rfl⟩

/-- Uniformizer translation preserves the actual quotient residue. -/
theorem latticeResidue_uniformizerTranslate (ν : cocharacterLattice S) (n : ℕ)
    (z : rationalPoints Z) :
    latticeResidue s (uniformizerTranslate s ν n z) = latticeResidue s z := by
  rw [uniformizerTranslate, map_mul,
    latticeResidue_eq_one_of_mem_C0 s ((mem_C0 S s _).mpr ⟨n • ν, rfl⟩), one_mul]

variable (h : Function.Bijective (restrictionEvaluation s))
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  (i : S.toGrp ⟶ G) (ν : cocharacterLattice S)

/-- Finitely many positive-root orders become nonnegative after a common
positive uniformizer shift. -/
theorem exists_uniformizerTranslate_mem_dominant
    (hroots : (positiveRelativeRoots i ν).Finite) (z : rationalPoints Z) :
    ∃ n : ℕ, uniformizerTranslate s ν n z ∈ dominantCentralizer i ν s h := by
  obtain ⟨R, hR⟩ := (hroots.image (fun α =>
    -RealTorusSpace.eval S α (centralizerValuation s h z).toAdd)).bddAbove
  obtain ⟨n, hn⟩ := exists_nat_ge R
  refine ⟨n, ?_⟩
  intro α hα
  have hαone : (1 : ℝ) ≤ (latticePairing S α ν : ℝ) := by
    have hαint : (1 : ℤ) ≤ latticePairing S α ν := by
      have := hα.2
      omega
    exact_mod_cast hαint
  have hαbound := hR (Set.mem_image_of_mem _ hα)
  have hnnonneg : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hnpair : (n : ℝ) ≤ (n : ℝ) * (latticePairing S α ν : ℝ) := by
    nlinarith
  change 0 ≤ RealTorusSpace.eval S α
    (centralizerValuation s h (uniformizerTranslate s ν n z)).toAdd
  rw [uniformizerTranslate, map_mul, toAdd_mul, map_add,
    centralizerValuation_uniformizerSection, RealTorusSpace.eval_tmul, one_mul,
    map_nsmul, nsmul_eq_mul, Int.cast_mul, Int.cast_natCast]
  linarith

/-- Every actual residue class has a dominant actual-point representative. -/
theorem latticeResidue_surjOn_dominant
    (hroots : (positiveRelativeRoots i ν).Finite) :
    Set.SurjOn (latticeResidue s) (dominantCentralizer i ν s h) Set.univ := by
  intro q _
  obtain ⟨v, hv⟩ := QuotientGroup.mk'_surjective (splitValuationImage s) q
  obtain ⟨z, hz⟩ := (rationalCharacterValuation Z).rangeRestrict_surjective v
  obtain ⟨n, hn⟩ := exists_uniformizerTranslate_mem_dominant s h i ν hroots z
  refine ⟨uniformizerTranslate s ν n z, hn, ?_⟩
  rw [latticeResidue_uniformizerTranslate]
  exact (congrArg (QuotientGroup.mk' (splitValuationImage s)) hz).trans hv

/-- Finiteness of the quotient gives one dominant point in every full-lattice
residue class. No chamber-compatibility or product uniqueness is asserted. -/
theorem exists_finite_dominant_latticeTransversal
    (hroots : (positiveRelativeRoots i ν).Finite)
    (hindex : (splitValuationImage s).FiniteIndex) :
    ∃ B : Set (rationalPoints Z), IsFiniteLatticeTransversal s B ∧
      B ⊆ dominantCentralizer i ν s h := by
  classical
  let : (splitValuationImage s).FiniteIndex := hindex
  have hq (q : rationalCharacterValuationImage Z ⧸ splitValuationImage s) :
      ∃ z : rationalPoints Z, z ∈ dominantCentralizer i ν s h ∧ latticeResidue s z = q :=
    latticeResidue_surjOn_dominant s h i ν hroots (Set.mem_univ q)
  choose rep hrepD hres using hq
  refine ⟨Set.range rep, ⟨Set.finite_range rep, ?_, ?_⟩, ?_⟩
  · intro x y hxy
    apply Subtype.ext
    obtain ⟨qx, hqx⟩ := x.property
    obtain ⟨qy, hqy⟩ := y.property
    have hqeq : qx = qy := by
      rw [← hres qx, hqx, ← hres qy, hqy]
      exact hxy
    rw [← hqx, ← hqy, hqeq]
  · intro q
    exact ⟨⟨rep q, ⟨q, rfl⟩⟩, hres q⟩
  · rintro _ ⟨q, rfl⟩
    exact hrepD q

end Langlands.Plancherel.RenardCartan
