/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.Depth
public import Mathlib.Algebra.Homology.LocalCohomology
import Mathlib.RingTheory.Depth.Rees
import Mathlib.CategoryTheory.Abelian.Projective.Ext
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-! # DepthThreeLocalCohomologyVanishing

## References

* Stacks Project, Tags 0AVY and 0BK0
* Stacks Project, Tag 0AVY, Lemma 47.11.1
-/

@[expose] public section

universe u

namespace AlgebraicGeometry.Scheme

/-- If `Abelian.Ext N M 2` vanishes, then so does the degree-two `Ext` computed by the derived
functor `Ext R (ModuleCat R) 2`. -/
private theorem old_ext_two_isZero {R : Type u} [CommRing R]
    (N M : ModuleCat.{u} R)
    (h : Subsingleton (CategoryTheory.Abelian.Ext N M 2)) :
    CategoryTheory.Limits.IsZero
      (((_root_.Ext R (ModuleCat.{u} R) 2).obj (Opposite.op N)).obj M) := by
  let P := CategoryTheory.projectiveResolution N
  apply CategoryTheory.Limits.IsZero.of_iso ?_ (P.isoExt 2 M)
  rw [← HomologicalComplex.exactAt_iff_isZero_homology,
    HomologicalComplex.exactAt_iff' _ 1 2 3
      (ComplexShape.prev_eq' _ (by decide)) (ComplexShape.next_eq' _ (by decide))]
  rw [CategoryTheory.ShortComplex.moduleCat_exact_iff]
  change ∀ (f : P.complex.X 2 ⟶ M), CategoryTheory.CategoryStruct.comp (P.complex.d 3 2) f = 0 →
    ∃ (g : P.complex.X 1 ⟶ M), CategoryTheory.CategoryStruct.comp (P.complex.d 2 1) g = f
  intro f hf
  obtain ⟨g, hg⟩ := (P.extMk_eq_zero_iff f 3 rfl hf 1 rfl).mp
    (h.elim _ 0)
  exact ⟨g, hg⟩

/-- Algebraic vanishing of second local cohomology under depth at least three. -/
theorem depth_three_local_cohomology_vanishing
    (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (hdepth : (3 : ℕ∞) ≤ IsLocalRing.depth (R := R) R) :
    Subsingleton ((localCohomology (IsLocalRing.maximalIdeal R) 2).obj
      ((ModuleCat.of R R : ModuleCat.{u} R))).carrier := by
  classical
  let m := IsLocalRing.maximalIdeal R
  let M := ModuleCat.of R R
  have hm : m • (⊤ : Submodule R R) ≠ ⊤ :=
    (Submodule.top_ne_ideal_smul_of_le_jacobson_annihilator
      (IsLocalRing.maximalIdeal_le_jacobson (Module.annihilator R R))).symm
  have hdef : IsLocalRing.depth (R := R) R = sSup {n : ℕ∞ | ∃ rs : List R,
      RingTheory.Sequence.IsRegular R rs ∧ (∀ r ∈ rs, r ∈ m) ∧
        n = (rs.length : ℕ∞)} := by
    simp only [m] at hm
    simp only [IsLocalRing.depth, Ideal.depth, ite_eq_right hm, m]
  have hlt : (2 : ℕ∞) < IsLocalRing.depth (R := R) R :=
    lt_of_lt_of_le (by decide : (2 : ℕ∞) < 3) hdepth
  rw [hdef] at hlt
  -- A length greater than two suffices; attaining the full depth is unnecessary.
  obtain ⟨n, ⟨rs, hreg, hmem, rfl⟩, hlen⟩ := lt_sSup_iff.mp hlt
  have hlen' : 2 < rs.length := by exact_mod_cast hlen
  let D := localCohomology.diagram (localCohomology.idealPowersDiagram m) 2
  let F := D.comp ((CategoryTheory.evaluation (ModuleCat.{u} R) (ModuleCat.{u} R)).obj M)
  apply ModuleCat.isZero_iff_subsingleton.mp
  change CategoryTheory.Limits.IsZero ((CategoryTheory.Limits.colimit D).obj M)
  apply CategoryTheory.Limits.IsZero.of_iso ?_
    (CategoryTheory.Limits.colimitObjIsoColimitCompEvaluation D M)
  apply (CategoryTheory.Limits.colimit.isColimit F).isZero_pt
  apply (CategoryTheory.Functor.isZero_iff F).mpr
  intro j
  let k := Opposite.unop (Opposite.unop j)
  let N := ModuleCat.of R (R ⧸ m ^ k)
  change CategoryTheory.Limits.IsZero
      (((_root_.Ext R (ModuleCat.{u} R) 2).obj (Opposite.op N)).obj M)
  apply old_ext_two_isZero
  have hsupp : Module.support R N ⊆ PrimeSpectrum.zeroLocus m := by
    change Module.support R (R ⧸ m ^ k) ⊆ PrimeSpectrum.zeroLocus m
    rw [Module.support_eq_zeroLocus, Ideal.annihilator_quotient]
    -- Mathlib includes the zeroth ideal power, whose quotient has empty support.
    by_cases hk : k = 0
    · simp [hk, Ideal.one_eq_top]
    · rw [PrimeSpectrum.zeroLocus_pow m hk]
  exact ModuleCat.subsingleton_ext_of_exists_isRegular m N hsupp M hm.lt_top
    rs hmem hreg 2 hlen'

end AlgebraicGeometry.Scheme
