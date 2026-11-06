import Langlands.Representation.Plancherel.ParabolicIntertwiningConeReduction
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.LeviProjectionHeight

/-! # The cone decay from a character decay on the opposite chart -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory Filter Topology
open scoped NNReal CategoryTheory.MonObj

namespace Langlands.Plancherel

open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open Langlands.GroupScheme.MatrixRepresentation
open Aubert.General Induction StandardIntertwining

section Host

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {A : CommGroupScheme (Spec (CommRingCat.of F))}
  {M G P U : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom] [Smooth G.X.hom]
  [IsAffine M.X.left]
  {p : P ⟶ G} {l : M ⟶ P} {a : A.toGrp ⟶ M}
  (r : ParabolicRootPresentation p l a)
  {n : U ⟶ P} (hn : LeviSubgroup.IsGeometricUnipotentRadical n)

local instance characterDecayAffine : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
local instance characterDecayTopology : TopologicalSpace (rationalPoints G) :=
  rationalPointTopology F G.X
local instance characterDecayTopologicalGroup : IsTopologicalGroup (rationalPoints G) :=
  rationalPoint_isTopologicalGroup F G

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
  [T2Space (rationalPoints G)]
  {Ppt Upt U'pt : Subgroup (rationalPoints G)}
  (hPpt : Ppt = (SubgroupFunctor.range p).carrier (Over.mk (𝟙 _)))
  (hUpt : Upt = (SubgroupFunctor.range (n ≫ p)).carrier (Over.mk (𝟙 _)))

/-- **The character decay on the opposite chart.** The cone decay without the coefficient
envelope: for every `s` there is `R` such that along the section of `(U ∩ U') \ U'` with values
in `Ū(F)` the weights `‖δ(m)‖ ‖χ(m)‖` are bounded by a multiple of `‖σ q‖ ^ (-s)`, locally
uniformly on `C R`. -/
def ParabolicOppositeCharacterDecay
    (h : IsSemidirectDecomposition Ppt (parabolicLeviPointSubgroup p l) Upt)
    (hU : IsClosed (Upt : Set (rationalPoints G))) (K : OpenSubgroup (rationalPoints G))
    {N : ℕ} [Nonempty (Fin N)] (ρ₀ : MatrixRepresentation G (Fin N))
    (C : ℝ → Set (unramifiedCharacters (parabolicLeviRationalNormCharacters r))) : Prop :=
  ∀ s : ℝ, ∃ R : ℝ,
    ∀ σ : QuotientSpace (U := Upt) U'pt → U'pt, (∀ q, Quotient.mk _ (σ q) = q) →
      (∀ q, ((σ q : U'pt) : rationalPoints G) ∈ parabolicOppositeRadicalPoints r) →
      IsLocallyUniformQuotientDecayOn h hU K (parabolicLeviRationalNormCharacters r) U'pt σ
        (fun _ => 1)
        (fun q => rationalMatrixNorm F ρ₀ ((σ q : U'pt) : rationalPoints G) ^ (-s)) (C R)

omit [IsAffine M.X.left] [LocallyCompactSpace (rationalPoints G)]
  [NonarchimedeanGroup (rationalPoints G)] [T2Space (rationalPoints G)] in
include r hn hPpt hUpt in
/-- **Linear height bound for Iwasawa Levi components.** For a compact `K`, there is `c ≥ 0`
such that whenever `x = p κ` with `p ∈ Ppt` and `κ ∈ K`, the Levi projection of `p` has height
at most `c` times the height of `x`. -/
theorem exists_rationalMatrixNorm_projection_le
    (h : IsSemidirectDecomposition Ppt (parabolicLeviPointSubgroup p l) Upt)
    (K : OpenSubgroup (rationalPoints G)) (hK : IsCompact (K : Set (rationalPoints G)))
    {N : ℕ} [Nonempty (Fin N)] (ρ₀ : MatrixRepresentation G (Fin N)) (hρ₀ : IsClosedSubgroup ρ₀) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ (x : rationalPoints G) (q : Ppt) (κ : K),
      x = (q : rationalPoints G) * (κ : rationalPoints G) →
      rationalMatrixNorm F ρ₀ ((h.projection q : parabolicLeviPointSubgroup p l) :
        rationalPoints G) ≤ c * rationalMatrixNorm F ρ₀ x := by
  set χ := CommGroupScheme.groupHom r.splitComponentCocharacter ≫ a ≫ l ≫ p with hχ
  have hP : Ppt = (Dynamic.parabolic χ).rationalPoints := by
    rw [hPpt, r.parabolic_eq_splitComponentCocharacter]
  have hU : Upt = (Dynamic.unipotent χ).rationalPoints := by
    rw [hUpt, r.range_comp_radical_eq hn]
  have hM : parabolicLeviPointSubgroup p l = (Dynamic.centralizer χ).rationalPoints := by
    change (SubgroupFunctor.range (l ≫ p)).carrier (Over.mk (𝟙 _)) = _
    rw [r.levi_eq_splitComponentCocharacter]
  obtain ⟨C₁, hC₁⟩ := exists_rationalMatrixNorm_levi_le F χ ρ₀ hρ₀
  have hC₁0 : 0 ≤ C₁ := by
    have h1 := hC₁ 1 1 (one_mem _) (one_mem _) (by simp)
    simp only [rationalMatrixNorm_one, mul_one] at h1
    linarith
  obtain ⟨B, hB⟩ := hK.bddAbove_image
    ((continuous_rationalMatrixNorm F ρ₀).continuousOn (s := (K : Set (rationalPoints G))))
  have hB1 : 1 ≤ B := (one_le_rationalMatrixNorm F ρ₀ 1).trans (hB ⟨1, one_mem K, rfl⟩)
  refine ⟨C₁ * B, mul_nonneg hC₁0 (zero_le_one.trans hB1), fun x q κ hx => ?_⟩
  have hqx : (q : rationalPoints G) = x * (κ : rationalPoints G)⁻¹ := by
    rw [hx]; group
  have hκ : rationalMatrixNorm F ρ₀ ((κ : rationalPoints G)⁻¹) ≤ B := by
    rw [rationalMatrixNorm_inv]
    exact hB ⟨κ, κ.2, rfl⟩
  have hqle : rationalMatrixNorm F ρ₀ (q : rationalPoints G) ≤
      rationalMatrixNorm F ρ₀ x * B := by
    rw [hqx]
    exact (rationalMatrixNorm_mul_le F ρ₀ _ _).trans
      (mul_le_mul_of_nonneg_left hκ (zero_le_one.trans (one_le_rationalMatrixNorm F ρ₀ x)))
  have hqP : (q : rationalPoints G) ∈ (Dynamic.parabolic χ).rationalPoints := hP ▸ q.2
  have hmM : ((h.projection q : parabolicLeviPointSubgroup p l) : rationalPoints G) ∈
      (Dynamic.centralizer χ).rationalPoints := hM ▸ (h.projection q).2
  have hmU : ((h.projection q : parabolicLeviPointSubgroup p l) : rationalPoints G)⁻¹ *
      (q : rationalPoints G) ∈ (Dynamic.unipotent χ).rationalPoints :=
    hU ▸ h.projection_inv_mul_mem q
  calc rationalMatrixNorm F ρ₀ ((h.projection q : parabolicLeviPointSubgroup p l) :
        rationalPoints G)
      ≤ C₁ * rationalMatrixNorm F ρ₀ (q : rationalPoints G) := hC₁ _ _ hqP hmM hmU
    _ ≤ C₁ * (rationalMatrixNorm F ρ₀ x * B) := mul_le_mul_of_nonneg_left hqle hC₁0
    _ = C₁ * B * rationalMatrixNorm F ρ₀ x := by ring

omit [T2Space (rationalPoints G)] in
include hn hPpt hUpt in
/-- **The cone decay from the character decay.** The linear height bound for Levi components
absorbs the coefficient envelope `‖m‖ ^ d` into the decay exponent. -/
theorem parabolicOppositeConeDecay_of_characterDecay
    (h : IsSemidirectDecomposition Ppt (parabolicLeviPointSubgroup p l) Upt)
    (hU : IsClosed (Upt : Set (rationalPoints G)))
    (K : OpenSubgroup (rationalPoints G)) (hK : IsCompact (K : Set (rationalPoints G)))
    {N : ℕ} [Nonempty (Fin N)] (ρ₀ : MatrixRepresentation G (Fin N)) (hρ₀ : IsClosedSubgroup ρ₀)
    (C : ℝ → Set (unramifiedCharacters (parabolicLeviRationalNormCharacters r)))
    (hchar : ParabolicOppositeCharacterDecay r (U'pt := U'pt) h hU K ρ₀ C) :
    ParabolicOppositeConeDecay r (U'pt := U'pt) h hU K ρ₀ C := by
  intro d s
  obtain ⟨R, hR⟩ := hchar (s + d)
  obtain ⟨c, hc0, hc⟩ := exists_rationalMatrixNorm_projection_le r hn hPpt hUpt h K hK ρ₀ hρ₀
  refine ⟨R, fun σ hσ hσŪ χ₀ hχ₀ => ?_⟩
  obtain ⟨Nb, hNb, C₀, hC₀⟩ := hR σ hσ hσŪ χ₀ hχ₀
  refine ⟨Nb, hNb, C₀ * c ^ d, fun χ hχ q pp κ hpκ => ?_⟩
  set w := rationalMatrixNorm F ρ₀ ((σ q : U'pt) : rationalPoints G) with hw
  have hw1 : 1 ≤ w := one_le_rationalMatrixNorm F ρ₀ _
  have hw0 : 0 < w := zero_lt_one.trans_le hw1
  set mm := ((h.projection pp : parabolicLeviPointSubgroup p l) : rationalPoints G)
  have h1 := hC₀ χ hχ q pp κ hpκ
  simp only [mul_one] at h1
  have hm1 : 1 ≤ rationalMatrixNorm F ρ₀ mm := one_le_rationalMatrixNorm F ρ₀ _
  have h2 : rationalMatrixNorm F ρ₀ mm ^ d ≤ (c * w) ^ d :=
    pow_le_pow_left₀ (zero_le_one.trans hm1) (hc _ pp κ hpκ) d
  have hlhs0 : 0 ≤ ‖(HaarModulus.closedHalfCharacter Upt hU (parabolicLeviPointSubgroup p l)
      h.levi_le_normalizer (h.projection pp) : ℂ)‖ * ‖(χ.val (h.projection pp) : ℂ)‖ :=
    mul_nonneg (norm_nonneg _) (norm_nonneg _)
  have hrpow : w ^ (-(s + (d : ℝ))) * (c * w) ^ d = c ^ d * w ^ (-s) := by
    rw [mul_pow, ← Real.rpow_natCast w d, mul_left_comm, ← Real.rpow_add hw0]
    congr 2
    ring
  calc ‖(HaarModulus.closedHalfCharacter Upt hU (parabolicLeviPointSubgroup p l)
        h.levi_le_normalizer (h.projection pp) : ℂ)‖ *
        (‖(χ.val (h.projection pp) : ℂ)‖ * rationalMatrixNorm F ρ₀ mm ^ d)
      = (‖(HaarModulus.closedHalfCharacter Upt hU (parabolicLeviPointSubgroup p l)
          h.levi_le_normalizer (h.projection pp) : ℂ)‖ * ‖(χ.val (h.projection pp) : ℂ)‖) *
          rationalMatrixNorm F ρ₀ mm ^ d := by ring
    _ ≤ (C₀ * w ^ (-(s + (d : ℝ)))) * (c * w) ^ d :=
        mul_le_mul h1 h2 (pow_nonneg (zero_le_one.trans hm1) d) (hlhs0.trans h1)
    _ = C₀ * c ^ d * w ^ (-s) := by rw [mul_assoc, hrpow]; ring

end Host

end Langlands.Plancherel
