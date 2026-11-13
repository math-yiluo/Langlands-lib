import Langlands.Global.AdelicRationalHeightReductionStatement
import Langlands.Global.AdelicSiegelNormMinimalityStatement
import Langlands.Global.AdelicCentralPositiveHeightStatement
import Langlands.Global.AdelicPositiveTorusCompatibility
import Langlands.Automorphic.GroupSchemeAdelicSliceGrowth
import Langlands.Automorphic.GroupSchemeSliceAdelicGrowthReduction

/-! # Rational height reduction from Siegel coverage, norm minimality and central factors -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain
open scoped Classical CategoryTheory.MonObj NNReal Pointwise Matrix.Norms.Operator

set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.AdelicMatrixHeight

variable (F : Type u) [Field F] [NumberField F] (n : ℕ)

/-- The mixed-space norm is at most a common bound on all archimedean components. -/
theorem mixedSpace_norm_le (x : InfiniteAdeleRing F) {B : ℝ} (hB : 0 ≤ B)
    (h : ∀ v : InfinitePlace F, ‖x v‖ ≤ B) :
    ‖InfiniteAdeleRing.ringEquiv_mixedSpace F x‖ ≤ B := by
  refine norm_prod_le_iff.mpr ⟨(pi_norm_le_iff_of_nonneg hB).mpr fun w => ?_,
    (pi_norm_le_iff_of_nonneg hB).mpr fun w => ?_⟩
  · change ‖InfinitePlace.Completion.extensionEmbeddingOfIsReal w.2 (x w.1)‖ ≤ B
    rw [(InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal w.2).norm_map_of_map_zero
      (map_zero _)]
    exact h w.1
  · change ‖InfinitePlace.Completion.extensionEmbedding w.1 (x w.1)‖ ≤ B
    rw [(InfinitePlace.Completion.isometry_extensionEmbedding w.1).norm_map_of_map_zero
      (map_zero _)]
    exact h w.1

variable {n} (hn : 0 < n)

include hn in
/-- Each scaled archimedean local maximum is at most the full height. -/
theorem nat_mul_infiniteLocal_le_height (g : AdelicGL F n) (v : InfinitePlace F) :
    (n : ℝ) * infiniteLocal F n g v ≤ height F n g := by
  have h1 (w : InfinitePlace F) : 1 ≤ (n : ℝ) * infiniteLocal F n g w :=
    MatrixInverseHeight.one_le_nat_mul_localMaximum (infiniteProjection F w) hn g
  have hprod : (n : ℝ) * infiniteLocal F n g v ≤
      ∏ w : InfinitePlace F, ((n : ℝ) * infiniteLocal F n g w) ^ w.mult := by
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ v)]
    calc
      (n : ℝ) * infiniteLocal F n g v ≤ ((n : ℝ) * infiniteLocal F n g v) ^ v.mult :=
        le_self_pow₀ (h1 v) (InfinitePlace.mult_ne_zero (w := v))
      _ ≤ _ := le_mul_of_one_le_right (pow_nonneg (zero_le_one.trans (h1 v)) _)
        (Finset.one_le_prod₀ fun w _ => one_le_pow₀ (h1 w))
  exact hprod.trans (le_mul_of_one_le_right
    (Finset.prod_nonneg fun w _ => pow_nonneg (zero_le_one.trans (h1 w)) _)
    (one_le_finprod (one_le_finiteLocal F n hn g)))

include hn in
/-- The operator norm of the archimedean coordinates is bounded by the full height. -/
theorem norm_archimedean_val_le_height (g : AdelicGL F n) :
    ‖(archimedeanGLCoordinates F n (AdelicGL.infinite F n g)).val‖ ≤
      height F n g := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hH : 0 ≤ height F n g := zero_le_one.trans (one_le_height F n hn g)
  set B : ℝ := height F n g / n with hB
  have hB0 : 0 ≤ B := div_nonneg hH hn'.le
  have hentry (i j : Fin n) :
      ‖(archimedeanGLCoordinates F n (AdelicGL.infinite F n g)).val i j‖ ≤ B := by
    change ‖InfiniteAdeleRing.ringEquiv_mixedSpace F (g i j).1‖ ≤ B
    apply mixedSpace_norm_le F _ hB0
    intro v
    have h := MatrixInverseHeight.entry_le_localMaximum (infiniteProjection F v) g i j
    change ‖(g i j).1 v‖ ≤ infiniteLocal F n g v at h
    rw [hB, le_div_iff₀ hn', mul_comm]
    exact (mul_le_mul_of_nonneg_left h (Nat.cast_nonneg _)).trans
      (nat_mul_infiniteLocal_le_height F hn g v)
  let B' : ℝ≥0 := ⟨B, hB0⟩
  have hB' : (B' : ℝ) = B := rfl
  rw [Matrix.linfty_opNorm_def]
  have hsup : ((Finset.univ : Finset (Fin n)).sup fun i : Fin n =>
      ∑ j : Fin n, ‖(archimedeanGLCoordinates F n
        (AdelicGL.infinite F n g)).val i j‖₊) ≤ (n : ℝ≥0) * B' := by
    apply Finset.sup_le
    intro i _
    calc
      ∑ j : Fin n, ‖(archimedeanGLCoordinates F n
          (AdelicGL.infinite F n g)).val i j‖₊ ≤ ∑ _j : Fin n, B' :=
        Finset.sum_le_sum fun j _ => hentry i j
      _ = (n : ℝ≥0) * B' := by simp
  calc
    _ ≤ (((n : ℝ≥0) * B' : ℝ≥0) : ℝ) := by exact_mod_cast hsup
    _ = height F n g := by
      rw [NNReal.coe_mul, NNReal.coe_natCast, hB', hB]
      field_simp

include hn in
/-- The archimedean matrix height of the infinite component is at most the full height. -/
theorem matrixHeight_infinite_le_height (g : AdelicGL F n) :
    ArchimedeanGL.matrixHeight F n (AdelicGL.infinite F n g) ≤ height F n g := by
  apply max_le (one_le_height F n hn g)
  apply max_le (norm_archimedean_val_le_height F hn g)
  have h := norm_archimedean_val_le_height F hn g⁻¹
  rw [height_inv, map_inv, map_inv] at h
  exact h

end Langlands.Global.AdelicMatrixHeight

namespace Langlands.Global.RepresentationGrowth

variable (F : Type u) [Field F] [NumberField F]
  (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left]
  {N : ℕ} (rho : GroupScheme.MatrixRepresentation G (Fin N))

/-- The archimedean height of the infinite component is at most the full adelic height. -/
theorem height_infinite_le_adelicHeight (hN : 0 < N) (x : AdelicGroupPoints F G) :
    height F G rho (AdelicGroupPoints.infinite F G x) ≤ adelicHeight F G rho x := by
  unfold height adelicHeight
  rw [infiniteMatrix_infinite]
  exact AdelicMatrixHeight.matrixHeight_infinite_le_height F hN _

end Langlands.Global.RepresentationGrowth

namespace Langlands.Global.AdelicSiegelFactors

open Langlands.GroupScheme AdelicGroupPoints

variable (F : Type u) [Field F] [NumberField F]
  (G : GroupScheme (Spec (CommRingCat.of F)))
  (T : CommGroupScheme (Spec (CommRingCat.of F)))
  [IsAffineHom G.X.hom] [IsAffine G.X.left] (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)
  (T₀ : CommGroupScheme (Spec (CommRingCat.of F))) (j : T₀ ⟶ T)

omit [IsAffineHom G.X.hom] in
/-- Evaluation of the finite component is the finite part of the adelic evaluation. -/
theorem evaluation_finite (x : AdelicGroupPoints F G) (b : Γ(G.X.left, ⊤)) :
    G.affinePointEvaluation (CommAlgCat.of F (FiniteAdeleRing (𝓞 F) F))
        (AdelicGroupPoints.finite F G x) b =
      (G.affinePointEvaluation (CommAlgCat.of F (AdeleRing (𝓞 F) F)) x b).2 :=
  G.affinePointEvaluation_map
    (CommAlgCat.ofHom (AlgHom.snd F (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F))) x b

omit [IsAffineHom G.X.hom] in
/-- The positive image of a split torus has trivial finite component. -/
theorem finite_positiveMap (hT₀ : IsSplitTorus T₀.toGrp)
    (a : PositiveRealTorus.intrinsicSubgroup F T₀) :
    AdelicGroupPoints.finite F G (positiveMap F G T i T₀ j a) = 1 := by
  rw [← map_one (AdelicGroupPoints.finite F G)]
  apply G.affinePointEvaluation_injective (CommAlgCat.of F (FiniteAdeleRing (𝓞 F) F))
  funext b
  dsimp only
  rw [evaluation_finite, evaluation_finite]
  refine FiniteAdeleRing.ext _ fun v => ?_
  have h1 := atFinitePlace_evaluation F G v (positiveMap F G T i T₀ j a) b
  have h2 := atFinitePlace_evaluation F G v 1 b
  rw [atFinitePlace_positiveMap F G T i T₀ j hT₀ v a] at h1
  rw [map_one] at h2
  exact h1.symm.trans h2

/-- The finite components of a weak Siegel product lie in one compact set. -/
theorem exists_isCompact_finite_weakSiegelProduct (hT₀ : IsSplitTorus T₀.toGrp)
    (D : StandardFactorData F G T i ν) (C : CompactFactors F G D.unipotent D.levi)
    (t : ℝ≥0ˣ) :
    ∃ Ω : Set (FiniteAdelicGroupPoints F G), IsCompact Ω ∧
      ∀ s ∈ weakSiegelProduct F G T i ν D C T₀ j t, AdelicGroupPoints.finite F G s ∈ Ω := by
  have hprefix : IsCompact (compactPrefix F G T i ν D C) :=
    (C.compact_omegaN.image (map F D.unipotent G D.unipotentInclusion).continuous).mul
      (C.compact_omegaM.image
        ((map F D.levi G D.leviInclusion).continuous.comp continuous_subtype_val))
  refine ⟨AdelicGroupPoints.finite F G '' compactPrefix F G T i ν D C *
      AdelicGroupPoints.finite F G '' (C.compactSubgroup : Set (AdelicGroupPoints F G)),
    (hprefix.image (AdelicGroupPoints.finite F G).continuous).mul
      (C.compact_compactSubgroup.image (AdelicGroupPoints.finite F G).continuous), ?_⟩
  intro s hs
  obtain ⟨_, ⟨p, hp, _, ⟨a, -, rfl⟩, rfl⟩, k, hk, rfl⟩ := hs
  refine ⟨_, ⟨p, hp, rfl⟩, _, ⟨k, hk, rfl⟩, ?_⟩
  rw [map_mul, map_mul, finite_positiveMap F G T i T₀ j hT₀ a, mul_one]

end Langlands.Global.AdelicSiegelFactors

namespace Langlands.Global.RepresentationGrowth

open Langlands.GroupScheme AdelicGroupPoints AdelicSiegelFactors

/-- Siegel coverage of the norm-one group, polynomial norm minimality on Siegel products and
polynomially bounded central factors together give rational height reduction. -/
theorem adelicRationalHeightReductionStatement_of_siegel
    (hsiegel : AdelicSiegelReductionStatement.{u})
    (hmin : SiegelNormMinimalityStatement.{u})
    (hcentral : CentralNormOneHeightFactorStatement.{u}) :
    AdelicRationalHeightReductionStatement.{u} := by
  intro F _ _ G _ N rho hG hrho hN
  have : Smooth G.X.hom := hG.smooth
  obtain ⟨T, i, ν, T₀, j, hS, C, t, hcover⟩ := hsiegel F G hG
  obtain ⟨cm, em, hm⟩ := hmin F G rho hG hrho hN T i ν T₀ j hS C t
  obtain ⟨cz, ez, hz⟩ := hcentral F G rho hG hrho hN
  have hT₀ : IsSplitTorus T₀.toGrp := by
    obtain ⟨_, _, _, _, ht₀, _⟩ := hS.2.2.2.2.2.2.2.1
    exact ht₀.1.1
  obtain ⟨Ω, hΩ, hΩs⟩ := exists_isCompact_finite_weakSiegelProduct F G T i ν T₀ j hT₀
    (canonicalStandardFactors F G T i ν) C t
  have hH1 (x : AdelicGroupPoints F G) : 1 ≤ adelicHeight F G rho x :=
    one_le_adelicHeight F G rho hN x
  have hH0 (x : AdelicGroupPoints F G) : 0 ≤ adelicHeight F G rho x :=
    zero_le_one.trans (hH1 x)
  set cz' : ℝ := max cz 1 with hcz'
  set cm' : ℝ := max cm 1 with hcm'
  have hcz0 : 0 < cz' := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hcm0 : 0 < cm' := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  refine ⟨Ω, cm' * cz' ^ (1 + em), ez + em * (ez + 1), hΩ,
    mul_pos hcm0 (pow_pos hcz0 _), fun g => ?_⟩
  obtain ⟨z, hzc, hzf, hz1, hzH⟩ := hz g
  have hmem : z⁻¹ * g ∈ (rationalSubgroup F G : Set (AdelicGroupPoints F G)) *
      weakSiegelProduct F G T i ν (canonicalStandardFactors F G T i ν) C T₀ j t := by
    rw [hcover.2]
    exact hz1
  obtain ⟨_, ⟨q₀, rfl⟩, s, hs, hrs⟩ := hmem
  replace hrs : rational F G q₀ * s = z⁻¹ * g := hrs
  have hg : g = z * (rational F G q₀ * s) := by rw [hrs, mul_inv_cancel_left]
  have hx : rational F G q₀⁻¹ * g = z * s := by
    calc
      rational F G q₀⁻¹ * g = rational F G q₀⁻¹ * z * (rational F G q₀ * s) := by
        rw [hg, mul_assoc]
      _ = z * rational F G q₀⁻¹ * (rational F G q₀ * s) := by
        rw [← (hzc (rational F G q₀⁻¹)).eq]
      _ = z * s := by rw [map_inv, mul_assoc, inv_mul_cancel_left]
  refine ⟨q₀⁻¹, ?_, ?_⟩
  · rw [hx, map_mul, hzf, one_mul]
    exact hΩs s hs
  · have hHz : adelicHeight F G rho z ≤ cz' * adelicHeight F G rho g ^ ez :=
      hzH.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg (hH0 g) _))
    have hHg₁ : adelicHeight F G rho (rational F G q₀ * s) ≤
        cz' * adelicHeight F G rho g ^ ez * adelicHeight F G rho g := by
      rw [hrs]
      calc
        adelicHeight F G rho (z⁻¹ * g) ≤
            adelicHeight F G rho z⁻¹ * adelicHeight F G rho g :=
          adelicHeight_mul_le F G rho hN _ _
        _ ≤ cz' * adelicHeight F G rho g ^ ez * adelicHeight F G rho g := by
          rw [adelicHeight_inv]
          exact mul_le_mul_of_nonneg_right hHz (hH0 g)
    have hHs : adelicHeight F G rho s ≤
        cm' * (cz' * adelicHeight F G rho g ^ ez * adelicHeight F G rho g) ^ em := by
      calc
        adelicHeight F G rho s ≤ cm * adelicHeight F G rho (rational F G q₀ * s) ^ em :=
          hm s hs q₀
        _ ≤ cm' * adelicHeight F G rho (rational F G q₀ * s) ^ em :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg (hH0 _) _)
        _ ≤ cm' * (cz' * adelicHeight F G rho g ^ ez * adelicHeight F G rho g) ^ em :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (hH0 _) hHg₁ em) hcm0.le
    calc
      height F G rho (infinite F G (rational F G q₀⁻¹ * g)) ≤
          adelicHeight F G rho (rational F G q₀⁻¹ * g) :=
        height_infinite_le_adelicHeight F G rho hN _
      _ = adelicHeight F G rho (z * s) := by rw [hx]
      _ ≤ adelicHeight F G rho z * adelicHeight F G rho s := adelicHeight_mul_le F G rho hN _ _
      _ ≤ (cz' * adelicHeight F G rho g ^ ez) *
          (cm' * (cz' * adelicHeight F G rho g ^ ez * adelicHeight F G rho g) ^ em) :=
        mul_le_mul hHz hHs (hH0 s)
          (mul_nonneg hcz0.le (pow_nonneg (hH0 g) _))
      _ = cm' * cz' ^ (1 + em) * adelicHeight F G rho g ^ (ez + em * (ez + 1)) := by ring

end Langlands.Global.RepresentationGrowth

namespace Langlands.Automorphic.GroupSchemeFunctions

open Langlands.Global

/-- Siegel coverage, polynomial norm minimality and polynomially bounded central factors give
the slice-to-global moderate-growth comparison. -/
theorem adelicSliceModerateGrowthStatement_of_siegel
    (hsiegel : AdelicSiegelFactors.AdelicSiegelReductionStatement.{u})
    (hmin : AdelicSiegelFactors.SiegelNormMinimalityStatement.{u})
    (hcentral : RepresentationGrowth.CentralNormOneHeightFactorStatement.{u}) :
    AdelicSliceModerateGrowthStatement.{u} :=
  adelicSliceModerateGrowthStatement_of_rationalHeightReduction
    (RepresentationGrowth.adelicRationalHeightReductionStatement_of_siegel hsiegel hmin hcentral)

end Langlands.Automorphic.GroupSchemeFunctions
