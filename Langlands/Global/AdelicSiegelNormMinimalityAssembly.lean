import Langlands.Global.AdelicSiegelConjugationBound
import Langlands.Global.AdelicSiegelNormMinimalityStatement
import Langlands.Global.AdelicPositiveTorusCompatibility

/-!
# Norm minimality on a weak Siegel product from a diagonal height inequality

`exists_adelicHeight_le_mul_rational_of_diagonal` shows that on an actual weak Siegel product
the full adelic height of a point `s` is at most a constant times the height of each rational
left translate `q s`, provided the positive torus image satisfies the same inequality. The
constant comes from the compact factors and from the conjugation bound
`exists_adelicHeight_conj_unipotent_le`. The paired Markdown records the argument.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Topology
open scoped CategoryTheory.MonObj NNReal

namespace Langlands.Global.AdelicSiegelFactors

open Langlands.GroupScheme AdelicGroupPoints

variable (F : Type u) [Field F] [NumberField F]
  (G : GroupScheme (Spec (CommRingCat.of F)))
  (T : CommGroupScheme (Spec (CommRingCat.of F)))
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)
  (T₀ : CommGroupScheme (Spec (CommRingCat.of F))) (j : T₀ ⟶ T)

/-- **Norm minimality from the diagonal inequality.** Suppose the height of every positive
torus image point is at most `c` times the height of each of its rational left translates.
Then on the weak Siegel product of an actual algebraic Siegel setup, the height of every point
is at most a constant times the height of each of its rational left translates. -/
theorem exists_adelicHeight_le_mul_rational_of_diagonal (hG : IsConnectedReductive G)
    (hsetup : IsSiegelAlgebraicSetup F G T i ν T₀ j) {N : ℕ}
    (rho : MatrixRepresentation G (Fin N)) (hN : 0 < N)
    (C : CompactFactors F G (Standard.unipotentScheme i ν ∅) (Standard.leviScheme i ν ∅))
    (t : ℝ≥0ˣ) {c : ℝ} (hc : 0 ≤ c)
    (hdiag : ∀ (a : PositiveRealTorus.intrinsicSubgroup F T₀) (q : RationalGroupPoints F G),
      RepresentationGrowth.adelicHeight F G rho (positiveMap F G T i T₀ j a) ≤
        c * RepresentationGrowth.adelicHeight F G rho
          (rational F G q * positiveMap F G T i T₀ j a)) :
    ∃ c' : ℝ, ∀ s ∈ weakSiegelProduct F G T i ν (canonicalStandardFactors F G T i ν) C T₀ j t,
      ∀ q : RationalGroupPoints F G,
        RepresentationGrowth.adelicHeight F G rho s ≤
          c' * RepresentationGrowth.adelicHeight F G rho (rational F G q * s) := by
  classical
  have hlevi : standardLevi i ν ∅ = torusCentralizer i := hsetup.2.2.2.2.2.1
  let H := RepresentationGrowth.adelicHeight F G rho
  have hHc : Continuous H := RepresentationGrowth.continuous_adelicHeight F G rho hN
  have hH1 (x : AdelicGroupPoints F G) : 1 ≤ H x :=
    RepresentationGrowth.one_le_adelicHeight F G rho hN x
  have hH0 (x : AdelicGroupPoints F G) : 0 ≤ H x := zero_le_one.trans (hH1 x)
  have hmul (x y : AdelicGroupPoints F G) : H (x * y) ≤ H x * H y :=
    RepresentationGrowth.adelicHeight_mul_le F G rho hN x y
  have hinv (x : AdelicGroupPoints F G) : H x⁻¹ = H x :=
    RepresentationGrowth.adelicHeight_inv F G rho x
  let ιN := map F (Standard.unipotentScheme i ν ∅) G (Standard.unipotentHom i ν ∅)
  let ιM : normOneSubgroup F (Standard.leviScheme i ν ∅) → AdelicGroupPoints F G :=
    fun m => map F (Standard.leviScheme i ν ∅) G (Standard.leviHom i ν ∅) m
  have hιM : Continuous ιM :=
    (map F (Standard.leviScheme i ν ∅) G (Standard.leviHom i ν ∅)).continuous.comp
      continuous_subtype_val
  -- bounds on the compact factors
  obtain ⟨BN, hBN⟩ := C.compact_omegaN.bddAbove_image (hHc.comp ιN.continuous).continuousOn
  obtain ⟨BM, hBM⟩ := C.compact_omegaM.bddAbove_image (hHc.comp hιM).continuousOn
  obtain ⟨BK, hBK⟩ := C.compact_compactSubgroup.bddAbove_image hHc.continuousOn
  -- the conjugation bound for the unipotent factor
  obtain ⟨B, hB⟩ := exists_adelicHeight_conj_unipotent_le F G T i ν T₀ j hG hsetup rho hN
    C.omegaN C.compact_omegaN t
  refine ⟨BN * BM * (c * (BK * BM * B)) * BK, fun s hs q => ?_⟩
  obtain ⟨n, hn, m, hm, a, ha, k, hk, rfl⟩ :=
    (mem_productSet_iff F G T i ν (canonicalStandardFactors F G T i ν) C T₀ j _ _).mp hs
  change H (ιN n * ιM m * positiveMap F G T i T₀ j a * k) ≤
    BN * BM * (c * (BK * BM * B)) * BK *
      H (rational F G q * (ιN n * ιM m * positiveMap F G T i T₀ j a * k))
  set A := positiveMap F G T i T₀ j a with hA
  set s := ιN n * ιM m * A * k with hs_def
  -- individual bounds
  have hn' : H (ιN n) ≤ BN := hBN ⟨n, hn, rfl⟩
  have hm' : H (ιM m) ≤ BM := hBM ⟨m, hm, rfl⟩
  have hk' : H k ≤ BK := hBK ⟨k, hk, rfl⟩
  have hconj : H (A⁻¹ * ιN n * A) ≤ B := hB n hn a ha
  have hBN0 : 0 ≤ BN := (hH0 _).trans hn'
  have hBM0 : 0 ≤ BM := (hH0 _).trans hm'
  have hBK0 : 0 ≤ BK := (hH0 _).trans hk'
  have hB0 : 0 ≤ B := (hH0 _).trans hconj
  -- the Levi factor commutes with the torus factor
  have hcomm : Commute (ιM m) A :=
    commute_of_mem_standardLevi_image F G T i ν T₀ j hlevi (CommAlgCat.of F (Adeles F))
      (ιM m) ⟨m.val, rfl⟩ a.val
  -- the torus factor expressed through `s`
  have hAeq : A = s * k⁻¹ * (ιM m)⁻¹ * (A⁻¹ * ιN n * A)⁻¹ := by
    have h1 : s * k⁻¹ * (ιM m)⁻¹ = ιN n * A := by
      rw [hs_def, mul_inv_cancel_right, mul_assoc (ιN n), hcomm.eq, ← mul_assoc,
        mul_inv_cancel_right]
    rw [h1]
    group
  -- upper bound for `H s`
  have hs1 : H s ≤ H (ιN n) * H (ιM m) * H A * H k := by
    refine (hmul _ _).trans (mul_le_mul_of_nonneg_right ?_ (hH0 _))
    refine (hmul _ _).trans (mul_le_mul_of_nonneg_right (hmul _ _) (hH0 _))
  -- upper bound for `H (q A)` through `H (q s)`
  have hqA : H (rational F G q * A) ≤ H (rational F G q * s) * (BK * BM * B) := by
    have heq : rational F G q * A =
        rational F G q * s * k⁻¹ * (ιM m)⁻¹ * (A⁻¹ * ιN n * A)⁻¹ := by
      conv_lhs => rw [hAeq]
      simp only [mul_assoc]
    rw [heq]
    calc H (rational F G q * s * k⁻¹ * (ιM m)⁻¹ * (A⁻¹ * ιN n * A)⁻¹)
        ≤ H (rational F G q * s) * H k⁻¹ * H (ιM m)⁻¹ * H (A⁻¹ * ιN n * A)⁻¹ := by
          refine (hmul _ _).trans (mul_le_mul_of_nonneg_right ?_ (hH0 _))
          refine (hmul _ _).trans (mul_le_mul_of_nonneg_right (hmul _ _) (hH0 _))
      _ = H (rational F G q * s) * (H k * H (ιM m) * H (A⁻¹ * ιN n * A)) := by
          rw [hinv, hinv, hinv]
          ring
      _ ≤ H (rational F G q * s) * (BK * BM * B) := by
          refine mul_le_mul_of_nonneg_left ?_ (hH0 _)
          exact mul_le_mul (mul_le_mul hk' hm' (hH0 _) hBK0) hconj (hH0 _)
            (mul_nonneg hBK0 hBM0)
  calc H s ≤ H (ιN n) * H (ιM m) * H A * H k := hs1
    _ ≤ BN * BM * (c * (H (rational F G q * s) * (BK * BM * B))) * BK := by
        have hA' : H A ≤ c * (H (rational F G q * s) * (BK * BM * B)) :=
          (hdiag a q).trans (mul_le_mul_of_nonneg_left hqA hc)
        refine mul_le_mul ?_ hk' (hH0 _)
          (mul_nonneg (mul_nonneg hBN0 hBM0) (hA'.trans' (hH0 _)))
        exact mul_le_mul (mul_le_mul hn' hm' (hH0 _) hBN0) hA' (hH0 _) (mul_nonneg hBN0 hBM0)
    _ = BN * BM * (c * (BK * BM * B)) * BK * H (rational F G q * s) := by ring

end Langlands.Global.AdelicSiegelFactors

namespace Langlands.Global.AdelicSiegelFactors

open Langlands.GroupScheme AdelicGroupPoints

/-- **Norm minimality from the diagonal inequality for split tori.** If, for every split torus
`T₀` and every homomorphism `f : T₀ → G`, the height of the image of each intrinsic positive
point is at most a constant times the height of each of its rational left translates, then
`SiegelNormMinimalityStatement` holds, with exponent `1`. -/
theorem siegelNormMinimalityStatement_of_diagonal
    (hA : ∀ (F : Type u) [Field F] [NumberField F]
      (G : GroupScheme (Spec (CommRingCat.of F)))
      [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom] {N : ℕ}
      (rho : MatrixRepresentation G (Fin N)), 0 < N →
      ∀ (T₀ : CommGroupScheme (Spec (CommRingCat.of F))), IsSplitTorus T₀.toGrp →
      ∀ f : T₀.toGrp ⟶ G, ∃ c : ℝ, 0 ≤ c ∧
        ∀ (a : PositiveRealTorus.intrinsicSubgroup F T₀) (q : RationalGroupPoints F G),
          RepresentationGrowth.adelicHeight F G rho (map F T₀.toGrp G f a) ≤
            c * RepresentationGrowth.adelicHeight F G rho
              (rational F G q * map F T₀.toGrp G f a)) :
    SiegelNormMinimalityStatement.{u} := by
  intro F _ _ G _ _ N rho hG _ hN T i ν T₀ j hsetup C t
  have hT₀ : IsSplitTorus T₀.toGrp := by
    obtain ⟨_, _, _, _, ht₀, _⟩ := hsetup.2.2.2.2.2.2.2.1
    exact ht₀.1.1
  obtain ⟨c, hc, hdiag⟩ := hA F G rho hN T₀ hT₀ (CommGroupScheme.groupHom j ≫ i)
  obtain ⟨c', hc'⟩ := exists_adelicHeight_le_mul_rational_of_diagonal F G T i ν T₀ j hG hsetup
    rho hN C t hc hdiag
  exact ⟨c', 1, fun s hs q => by simpa only [pow_one] using hc' s hs q⟩

end Langlands.Global.AdelicSiegelFactors
