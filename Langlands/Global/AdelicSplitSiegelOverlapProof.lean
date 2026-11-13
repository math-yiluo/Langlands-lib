import Langlands.Global.AdelicSplitSiegelOverlap
import Langlands.Global.AdelicSplitOverlapHeight
import Langlands.GroupScheme.Rational.DominantWeylDisplacementRoots
import Langlands.GroupScheme.Rational.MaximalParabolicLineDominance
import Langlands.GroupScheme.Rational.RationalBruhatProof
import Langlands.GroupScheme.Rational.MinimalStandardDynamicComparison
import Langlands.GroupScheme.Rational.RelativeWeylCoxeterProof
import Langlands.GroupScheme.Rational.StandardCocharacterProof
import Langlands.GroupScheme.Rational.StandardParabolicOrderProof

/-! # Proof of Springer's Siegel-set overlap estimate for split groups -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj NNReal

namespace Langlands.Global.AdelicSiegelFactors

open Langlands.GroupScheme AdelicGroupPoints
open Langlands.Aubert.General.RationalPointFamily Langlands.Group.RelativeWeylIndexing

section TorusLog

variable {F : Type u} [Field F] [NumberField F] {T : CommGroupScheme (Spec (CommRingCat.of F))}

/-- The logarithms of the normalized character norms at an adelic torus point, as an
additive map on the character lattice. -/
def torusLog (t : AdelicGroupPoints F T.toGrp) : characterLattice T →+ ℝ :=
  characterLog F T.toGrp t

theorem torusLog_apply (t : AdelicGroupPoints F T.toGrp) (χ : characterLattice T) :
    torusLog t χ = Real.log ((PositiveRealTorus.normCharacter F T χ t : ℝ≥0) : ℝ) :=
  rfl

theorem normCharacter_coe_pos (χ : characterLattice T) (t : AdelicGroupPoints F T.toGrp) :
    0 < ((PositiveRealTorus.normCharacter F T χ t : ℝ≥0) : ℝ) :=
  NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr (Units.ne_zero _))

/-- A character whose norm is at most `c` has logarithm at most `log (max c 1)`. -/
theorem torusLog_le_of_normCharacter_le {χ : characterLattice T} {t : AdelicGroupPoints F T.toGrp}
    {c : ℝ≥0ˣ} (h : PositiveRealTorus.normCharacter F T χ t ≤ c) :
    torusLog t χ ≤ Real.log (max ((c : ℝ≥0) : ℝ) 1) := by
  rw [torusLog_apply]
  apply Real.log_le_log (normCharacter_coe_pos χ t)
  exact le_trans (NNReal.coe_le_coe.mpr (Units.val_le_val.mpr h)) (le_max_left _ _)

/-- Bounded norms on a set `Δ` of characters bound the logarithm of every sum of elements of
`Δ`, linearly in a number of summands independent of the torus point. -/
theorem exists_torusLog_le_of_mem_closure {Δ : Set (characterLattice T)} (c : ℝ≥0ˣ)
    {χ : characterLattice T} (hχ : χ ∈ AddSubmonoid.closure Δ) :
    ∃ N : ℕ, ∀ t : AdelicGroupPoints F T.toGrp,
      (∀ β ∈ Δ, PositiveRealTorus.normCharacter F T β t ≤ c) →
        torusLog t χ ≤ N * Real.log (max ((c : ℝ≥0) : ℝ) 1) := by
  induction hχ using AddSubmonoid.closure_induction with
  | mem β hβ =>
    refine ⟨1, fun t ht => ?_⟩
    rw [Nat.cast_one, one_mul]
    exact torusLog_le_of_normCharacter_le (ht β hβ)
  | zero => exact ⟨0, fun t _ => by simp⟩
  | add χ₁ χ₂ _ _ h₁ h₂ =>
    obtain ⟨N₁, hN₁⟩ := h₁
    obtain ⟨N₂, hN₂⟩ := h₂
    refine ⟨N₁ + N₂, fun t ht => ?_⟩
    rw [map_add, Nat.cast_add, add_mul]
    exact add_le_add (hN₁ t ht) (hN₂ t ht)

/-- The bound of `exists_torusLog_le_of_mem_closure`, uniformly over a finite family. -/
theorem exists_uniform_torusLog_le {W : Type*} [Finite W] {Δ : Set (characterLattice T)}
    (c : ℝ≥0ˣ) (φ : W → characterLattice T) (hφ : ∀ w, φ w ∈ AddSubmonoid.closure Δ) :
    ∃ N : ℕ, ∀ w (t : AdelicGroupPoints F T.toGrp),
      (∀ β ∈ Δ, PositiveRealTorus.normCharacter F T β t ≤ c) →
        torusLog t (φ w) ≤ N * Real.log (max ((c : ℝ≥0) : ℝ) 1) := by
  have := Fintype.ofFinite W
  choose Nf hNf using fun w => exists_torusLog_le_of_mem_closure (F := F) c (hφ w)
  refine ⟨Finset.univ.sup Nf, fun w t ht => (hNf w t ht).trans ?_⟩
  apply mul_le_mul_of_nonneg_right _ (Real.log_nonneg (le_max_right _ _))
  exact Nat.cast_le.mpr (Finset.le_sup (Finset.mem_univ w))

end TorusLog

/-- **Springer's Proposition 2.6 for split groups.** The published statement
`SplitSiegelOverlapStatement`: in two Siegel factorizations of one adelic point whose torus
factors have bounded simple-root norms, if `|α(s)|` is small enough then the rational quotient
lies in the standard maximal parabolic `P_(Δ \ {α})`. -/
theorem splitSiegelOverlap : SplitSiegelOverlapStatement.{u} := by
  intro F _ _ G _ _ hG T i ν hi hmax hν C hC c α hα
  have : Mono i.hom.hom.left := hi.isSplitSubtorus.mono
  obtain ⟨a, rfl⟩ : ∃ a : SimpleRoot i ν, a.1 = α := ⟨⟨α, hα⟩, rfl⟩
  have hJ : simpleRelativeRoots i ν \ {a.1} ⊆ simpleRelativeRoots i ν := Set.sdiff_subset
  -- The Coxeter structure of the relative Weyl group.
  obtain ⟨hWfin, hSfin, M, cs, hcs⟩ := relativeWeylCoxeter F G hG T i hi ν hν
  let : Fintype (SimpleRoot i ν) := Fintype.ofFinite _
  -- A dominant line character for the maximal parabolic of `a`.
  obtain ⟨dd, j, ρ, hP, hT, hfixJ, hpos⟩ :=
    exists_maximalParabolic_dominant_line hG i hi ν hν a.1 a.2
  obtain ⟨ζ, hζ⟩ := (standardCocharacter F G hG T i hi ν hν _ hJ).1
  obtain ⟨f, hf2, hfact⟩ := hcs.1 a
  have hfpos : 0 < f (ρ.torusCoordinateLineCharacter i j hT) :=
    hpos f hf2 (cs.simple a) (hcs.simple_mem_standardRelativeWeylGroup a) hfact
  have hfix : ∀ b : SimpleRoot i ν, b ≠ a → schemeWeylCharacterAction i (cs.simple b)
      (ρ.torusCoordinateLineCharacter i j hT) = ρ.torusCoordinateLineCharacter i j hT := by
    intro b hb
    apply hfixJ
    rw [DominantDisplacement.standardRelativeWeylGroup_complement_eq hcs a]
    exact simple_mem_standardSubgroup cs (DominantDisplacement.mem_complementLabels.mpr hb)
  have hαψ : ρ.torusCoordinateLineCharacter i j hT - schemeWeylCharacterAction i (cs.simple a)
      (ρ.torusCoordinateLineCharacter i j hT) =
        (f (ρ.torusCoordinateLineCharacter i j hT)).toNat • a.1 := by
    rw [hfact, sub_sub_cancel, ← natCast_zsmul, Int.toNat_of_nonneg hfpos.le]
  have hdisp := DominantDisplacement.displacement_mem_closure hcs a hζ
    (ρ.torusCoordinateLineCharacter i j hT) hfix _ (by omega) hαψ
  -- Uniform bounds for the displacements over the finite relative Weyl group.
  have := hWfin
  obtain ⟨N₁, hN₁⟩ := exists_uniform_torusLog_le (F := F) c
    (fun w : relativeWeylGroup i => ρ.torusCoordinateLineCharacter i j hT -
      schemeWeylCharacterAction i w (ρ.torusCoordinateLineCharacter i j hT))
    (fun w => (hdisp w).1)
  obtain ⟨N₂, hN₂⟩ := exists_uniform_torusLog_le (F := F) c
    (fun w : {w : relativeWeylGroup i //
        w ∉ standardRelativeWeylGroup i ν (simpleRelativeRoots i ν \ {a.1})} =>
      ρ.torusCoordinateLineCharacter i j hT -
        schemeWeylCharacterAction i w (ρ.torusCoordinateLineCharacter i j hT) - a.1)
    (fun w => (hdisp w).2 w.2)
  -- The height comparison constant.
  obtain ⟨D, hD, hDb⟩ := exists_bruhat_height_bound hG i ν hi hmax hν ρ j hP hT hC
  set lc := Real.log (max ((c : ℝ≥0) : ℝ) 1) with hlc
  set K₀ : ℝ := 2 * Real.log D + ((N₁ : ℝ) + N₂) * lc with hK₀
  have hd0 : (⟨Real.exp (-K₀ - 1), (Real.exp_pos _).le⟩ : ℝ≥0) ≠ 0 := by
    intro h
    have h' := congrArg NNReal.toReal h
    simp only [NNReal.coe_zero] at h'
    exact (Real.exp_pos _).ne' h'
  refine ⟨Units.mk0 _ hd0, ?_⟩
  intro x hx x' hx' s s' p p' q q' _ _ hsc hsc' hαd heq
  -- The logarithm of `|α(s)|` is very negative.
  have hαlog : torusLog s a.1 ≤ -K₀ - 1 := by
    rw [torusLog_apply]
    have h1 : ((PositiveRealTorus.normCharacter F T a.1 s : ℝ≥0) : ℝ) ≤ Real.exp (-K₀ - 1) :=
      NNReal.coe_le_coe.mpr (Units.val_le_val.mpr hαd)
    calc _ ≤ Real.log (Real.exp (-K₀ - 1)) := Real.log_le_log (normCharacter_coe_pos _ _) h1
      _ = -K₀ - 1 := Real.log_exp _
  -- The two factorizations, with the rational quotient on the right.
  have heq1 : x * map F T.toGrp G i s * map F _ G (Standard.parabolicHom i ν ∅) p =
      x' * map F T.toGrp G i s' * map F _ G (Standard.parabolicHom i ν ∅) p' *
        rational F G (q' * q⁻¹) := by
    rw [map_mul, map_inv, ← mul_assoc, ← heq, mul_inv_cancel_right]
  have heq2 : x' * map F T.toGrp G i s' * map F _ G (Standard.parabolicHom i ν ∅) p' =
      x * map F T.toGrp G i s * map F _ G (Standard.parabolicHom i ν ∅) p *
        rational F G (q * q'⁻¹) := by
    rw [map_mul, map_inv, ← mul_assoc, heq, mul_inv_cancel_right]
  -- Bruhat decomposition of the rational quotient.
  obtain ⟨n, hn, b₁, hb₁, b₂, hb₂, hγ⟩ :=
    (rationalBruhat F G hG T i hi ν hν).1 (basePointEquiv.symm (q' * q⁻¹))
  rw [← standardParabolic_empty_eq_dynamic_of_generic i ν hG hi hν] at hb₁ hb₂
  have hγ' : q' * q⁻¹ = basePointEquiv (b₁ * ((⟨n, hn⟩ : normalizerPoints i) :
      Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ G.X) * b₂) := by
    rw [← hγ, MulEquiv.apply_symm_apply]
  have hγinv : q * q'⁻¹ = basePointEquiv (b₂⁻¹ * (((⟨n, hn⟩ : normalizerPoints i)⁻¹ :
      normalizerPoints i) : Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ G.X) * b₁⁻¹) := by
    have h : b₂⁻¹ * (((⟨n, hn⟩ : normalizerPoints i)⁻¹ : normalizerPoints i) :
        Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ G.X) * b₁⁻¹ =
        (b₁ * ((⟨n, hn⟩ : normalizerPoints i) :
          Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ G.X) * b₂)⁻¹ := by
      rw [Subgroup.coe_inv]
      group
    rw [h, map_inv, ← hγ', mul_inv_rev, inv_inv]
  -- The two height comparisons.
  have h1 := hDb x hx x' hx' s s' p p' ⟨n, hn⟩ b₁ b₂ hb₁ hb₂ (by rw [← hγ']; exact heq1)
  have h2 := hDb x' hx' x hx s' s p' p (⟨n, hn⟩ : normalizerPoints i)⁻¹ b₂⁻¹ b₁⁻¹
    (Subgroup.inv_mem _ hb₂) (Subgroup.inv_mem _ hb₁) (by rw [← hγinv]; exact heq2)
  have hlog : ∀ {u v : ℝ}, 0 < u → 0 < v → u ≤ D * v → Real.log u ≤ Real.log D + Real.log v := by
    intro u v hu hv h
    rw [← Real.log_mul hD.ne' hv.ne']
    exact Real.log_le_log hu h
  set w : relativeWeylGroup i := QuotientGroup.mk (⟨n, hn⟩ : normalizerPoints i) with hw_def
  have l1 : torusLog s' (schemeWeylCharacterAction i w (ρ.torusCoordinateLineCharacter i j hT)) ≤
      Real.log D + torusLog s (ρ.torusCoordinateLineCharacter i j hT) := by
    rw [hw_def, schemeWeylCharacterAction_mk, torusLog_apply, torusLog_apply]
    exact hlog (normCharacter_coe_pos _ _) (normCharacter_coe_pos _ _) h1
  have l2 : torusLog s (schemeWeylCharacterAction i w⁻¹ (ρ.torusCoordinateLineCharacter i j hT)) ≤
      Real.log D + torusLog s' (ρ.torusCoordinateLineCharacter i j hT) := by
    rw [hw_def, ← QuotientGroup.mk_inv, schemeWeylCharacterAction_mk, torusLog_apply,
      torusLog_apply]
    exact hlog (normCharacter_coe_pos _ _) (normCharacter_coe_pos _ _) h2
  -- The Weyl element lies in the standard Weyl subgroup of `Δ \ {a}`.
  have hwJ : w ∈ standardRelativeWeylGroup i ν (simpleRelativeRoots i ν \ {a.1}) := by
    by_contra hwn
    have hwn' : w⁻¹ ∉ standardRelativeWeylGroup i ν (simpleRelativeRoots i ν \ {a.1}) :=
      fun h => hwn (by simpa only [inv_inv] using Subgroup.inv_mem _ h)
    have d1 : torusLog s' (ρ.torusCoordinateLineCharacter i j hT -
        schemeWeylCharacterAction i w (ρ.torusCoordinateLineCharacter i j hT)) ≤ N₁ * lc :=
      hN₁ w s' hsc'
    have d2 : torusLog s (ρ.torusCoordinateLineCharacter i j hT -
        schemeWeylCharacterAction i w⁻¹ (ρ.torusCoordinateLineCharacter i j hT) - a.1) ≤
          N₂ * lc :=
      hN₂ ⟨w⁻¹, hwn'⟩ s hsc
    rw [map_sub] at d1
    rw [map_sub, map_sub] at d2
    linarith
  -- Hence the normalizing point lies in the standard Levi of `Δ \ {a}`.
  obtain ⟨n', hn'L, hn'w⟩ := (mem_standardRelativeWeylGroup_iff i ν).mp hwJ
  have hc : ((n'⁻¹ * ⟨n, hn⟩ : normalizerPoints i) :
      Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ G.X) ∈ centralizerPoints i :=
    Subgroup.mem_subgroupOf.mp (QuotientGroup.eq.mp hn'w)
  have hnL : n ∈ standardLeviPoints i ν (simpleRelativeRoots i ν \ {a.1}) := by
    have hcL : ((n'⁻¹ * ⟨n, hn⟩ : normalizerPoints i) :
        Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ G.X) ∈
          standardLeviPoints i ν (simpleRelativeRoots i ν \ {a.1}) :=
      torusCentralizer_le_standardLevi i ν _ _ (by beta_reduce; rw [torusCentralizer_carrier_base]; exact hc)
    have h := (standardLeviPoints i ν (simpleRelativeRoots i ν \ {a.1})).mul_mem hn'L hcL
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_cancel_left] using h
  -- The rational quotient lies in the standard maximal parabolic.
  have hle := ((standardParabolicOrder F G hG T i hi ν hν).1 ∅ _ (Set.empty_subset _) hJ).1.mp
    (Set.empty_subset _)
  have hmem : b₁ * n * b₂ ∈ standardParabolicPoints i ν (simpleRelativeRoots i ν \ {a.1}) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ (hle _ hb₁)
      (standardLevi_le_standardParabolic i ν _ _ hnL)) (hle _ hb₂)
  obtain ⟨r₀, hr₀⟩ : ∃ r₀, r₀ ≫ (Standard.parabolicHom i ν
      (simpleRelativeRoots i ν \ {a.1})).hom.hom = b₁ * n * b₂ := by
    have h : b₁ * n * b₂ ∈ (SubgroupFunctor.range
        (Standard.parabolicHom i ν (simpleRelativeRoots i ν \ {a.1}))).carrier _ := by
      rw [(Standard.isRepresentedBy_parabolicHom i ν _).2]
      exact hmem
    exact h
  refine ⟨basePointEquiv r₀, ?_⟩
  rw [← basePointEquiv_comp, hr₀, ← hγ, MulEquiv.apply_symm_apply]

end Langlands.Global.AdelicSiegelFactors
