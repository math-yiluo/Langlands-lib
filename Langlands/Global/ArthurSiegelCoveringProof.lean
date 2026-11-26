import Langlands.Global.ArthurSiegelNormMinimality
import Langlands.Global.ArthurSiegelRelativeChamber
import Langlands.Global.ArthurSiegelSetsIwasawaStatement
import Langlands.Global.AdelicSiegelChamberReduction
import Langlands.Global.AdelicSpringerCentralCompactnessProof
import Langlands.GroupScheme.Rational.StandardParabolicOrderProof

/-! # Siegel covering for every compact Iwasawa subgroup

See the paired Markdown file for the statement and the proof. -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Opposite TensorProduct
open scoped CategoryTheory.MonObj NNReal Pointwise

namespace Langlands.Global.ArthurTruncation

open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace AdelicGroupPoints
  ArthurParabolicSpaces AdelicSiegelFactors

variable {F : Type u} [Field F] [NumberField F] {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom]
  {T : CommGroupScheme (Spec (CommRingCat.of F))} {i : T.toGrp ⟶ G} [Mono i.hom.hom.left]
  {ν : cocharacterLattice T}

omit [IsAffineHom G.X.hom] [Mono i.hom.hom.left] in
/-- The embedding `A_0(ℝ)^0 → G(𝔸)` of the Siegel sets is the adelic map of `i` on the
underlying torus point. -/
theorem positiveTorusMap_apply (a : PositiveRealTorus.intrinsicSubgroup F T) :
    positiveTorusMap F i a = map F T.toGrp G i (a : AdelicGroupPoints F T.toGrp) := by
  change map F T.toGrp G (CommGroupScheme.groupHom (𝟙 T) ≫ i) _ = _
  rw [show CommGroupScheme.groupHom (𝟙 T) = 𝟙 T.toGrp from rfl, Category.id_comp]
  rfl

omit [NumberField F] [IsAffineHom G.X.hom] [Mono i.hom.hom.left] in
/-- Pairing a parameter with the image of a real character dual under `f` is pairing its
restriction along `f`. -/
theorem realParameterPairing_realCharacterDualMap {P Q : GroupScheme (Spec (CommRingCat.of F))}
    (f : P ⟶ Q) (m : RealCharacterParameter F Q) (H : RealCharacterDual F P) :
    realParameterPairing F Q m (realCharacterDualMap F P Q f H) =
      realParameterPairing F P (rationalCharacterRestrictReal f m) H := by
  induction m using TensorProduct.inductionOn with
  | tmul t χ =>
    rw [rationalCharacterRestrictReal_tmul, realParameterPairing_tmul, realParameterPairing_tmul]
    rfl
  | add a b ha hb => simp only [map_add, LinearMap.add_apply, ha, hb]

omit [Mono i.hom.hom.left] in
/-- A rational point of `G` lying in the standard parabolic `P` is in `P(F)`. -/
theorem rational_mem_parabolicRationalImage {S : Set (characterLattice T)}
    {q : RationalGroupPoints F G}
    (hq : q ∈ (SubgroupFunctor.range (Standard.parabolicHom i ν S)).carrier
      ((algSpec (CommRingCat.of F)).obj (op (CommAlgCat.of F F)))) :
    rational F G q ∈ parabolicRationalImage (Standard.parabolicHom i ν S) := by
  obtain ⟨y, hy⟩ := SubgroupFunctor.mem_range.mp hq
  refine ⟨⟨rational F G q, ⟨q, rfl⟩⟩, ⟨rational F _ y, ⟨y, rfl⟩, ?_⟩, rfl⟩
  have h := DFunLike.congr_fun (rational_naturality F _ (Standard.parabolicHom i ν S)) y
  change map F _ G (Standard.parabolicHom i ν S) (rational F _ y) = rational F G q
  rw [← hy]
  exact h.symm

/-- **Siegel covering for every compact Iwasawa subgroup** (Arthur 1978, §6, p.941; Arthur 2005,
Theorem 8.1 for `P_1 = G`): for every compact `K` with `P_0(𝔸)K = G(𝔸)` there are compact factor
data `ω` with the compact subgroup `K` and `T_1 ∈ 𝔞_0` such that `G(𝔸) = P_1(F) S^{P_1}(T_1, ω)`
for every standard `P_1`. -/
theorem iwasawaSiegelCovering : IwasawaSiegelCoveringStatement.{u} := by
  intro F _ _ G _ _ T i _ ν hG hi hν K hK hρ
  classical
  obtain ⟨T₀, j, hS⟩ := exists_siegelAlgebraicSetup_of_generic F i ν hG hi hν
  obtain ⟨ΩN, hΩN, hcovN⟩ := exists_unipotentCompactCover_of_setup hS
  obtain ⟨ΩM, hΩM, hcovM⟩ := exists_leviCompactCover_of_setup centralSplitCompactQuotient hS
  let C : CompactFactors F G (Standard.unipotentScheme i ν ∅) (Standard.leviScheme i ν ∅) :=
    ⟨ΩN, ΩM, hΩN, hΩM, K, hK.isCompact⟩
  have hsub (S : (simpleFinset ν hG hi).powerset) :
      ((S : Finset (characterLattice T)) : Set (characterLattice T)) ⊆
        simpleRelativeRoots i ν := by
    intro β hβ
    exact (mem_simpleFinset hG hi).mp (Finset.mem_powerset.mp S.2 hβ)
  choose t ht using fun S : (simpleFinset ν hG hi).powerset =>
    exists_relativeChamberReduction F G T i ν T₀ j hG hS hK S (hsub S)
  obtain ⟨t₀, ht₀⟩ := (Set.finite_range t).bddBelow
  let c : ℝ := min (Real.log ((t₀ : ℝ≥0) : ℝ)) 0 - 1
  refine ⟨C, c ⊗ₜ[ℤ] ν, rfl, ?_⟩
  intro S₁ hS₁
  refine Set.eq_univ_of_forall fun x => ?_
  obtain ⟨q, hq, n, m, a, ha, k, hk, heq⟩ := ht ⟨S₁, hS₁⟩ x
  have hS₁' := hsub ⟨S₁, hS₁⟩
  -- the compact sets meeting the cosets of `M_0(F)` in `M_0(𝔸)^1` and of `N_0(F)` in `N_0(𝔸)`
  obtain ⟨mu, hmu⟩ := hcovM m
  set ιN := map F (Standard.unipotentScheme i ν ∅) G (Standard.unipotentHom i ν ∅) with hιN
  set ιM := map F (Standard.leviScheme i ν ∅) G (Standard.leviHom i ν ∅) with hιM
  set muG : RationalGroupPoints F G :=
    (Standard.leviScheme i ν ∅).affinePointsTarget (Standard.leviHom i ν ∅)
      (CommAlgCat.of F F) mu with hmuGdef
  have hmuG : ιM (rational F _ mu) = rational F G muG :=
    (DFunLike.congr_fun (rational_naturality F (Standard.leviScheme i ν ∅)
      (Standard.leviHom i ν ∅)) mu).symm
  have hconj : rational F G muG * ιN n * (rational F G muG)⁻¹ ∈
      standardUnipotentImage F G T i ν := by
    have hp : rational F G muG ∈ standardParabolicImage F G T i ν :=
      standardLeviImage_le_parabolic F G T i ν ⟨rational F _ mu, hmuG⟩
    exact (Subgroup.mem_normalizer_iff.mp
      (standardParabolicImage_le_normalizer F G T i ν hp) (ιN n)).mp ⟨n, rfl⟩
  obtain ⟨n₂, hn₂⟩ := hconj
  obtain ⟨_, ⟨ρN, rfl⟩, hρN⟩ := hcovN n₂
  set ρG : RationalGroupPoints F G :=
    (Standard.unipotentScheme i ν ∅).affinePointsTarget (Standard.unipotentHom i ν ∅)
      (CommAlgCat.of F F) ρN with hρGdef
  have hρG : ιN (rational F _ ρN) = rational F G ρG :=
    (DFunLike.congr_fun (rational_naturality F (Standard.unipotentScheme i ν ∅)
      (Standard.unipotentHom i ν ∅)) ρN).symm
  -- the rational translate lies in `P_1(F)`
  have hle : standardParabolic i ν ∅ ≤
      standardParabolic i ν (S₁ : Set (characterLattice T)) :=
    ((standardParabolicOrder F G hG T i hi ν hν).1 ∅ _ (Set.empty_subset _) hS₁').1.mp
      (Set.empty_subset _)
  have hmuP : muG ∈ (SubgroupFunctor.range
      (Standard.parabolicHom i ν (S₁ : Set (characterLattice T)))).carrier
        ((algSpec (CommRingCat.of F)).obj (op (CommAlgCat.of F F))) := by
    rw [(Standard.isRepresentedBy_parabolicHom i ν _).2]
    apply hle
    apply standardLevi_le_standardParabolic i ν ∅
    rw [← (Standard.isRepresentedBy_leviHom i ν ∅).2]
    exact ⟨mu, rfl⟩
  have hρP : ρG ∈ (SubgroupFunctor.range
      (Standard.parabolicHom i ν (S₁ : Set (characterLattice T)))).carrier
        ((algSpec (CommRingCat.of F)).obj (op (CommAlgCat.of F F))) := by
    rw [(Standard.isRepresentedBy_parabolicHom i ν _).2]
    apply hle
    apply standardUnipotent_le_standardParabolic i ν ∅
    rw [← (Standard.isRepresentedBy_unipotentHom i ν ∅).2]
    exact ⟨ρN, rfl⟩
  have hγ : ρG * muG * q ∈ (SubgroupFunctor.range
      (Standard.parabolicHom i ν (S₁ : Set (characterLattice T)))).carrier
        ((algSpec (CommRingCat.of F)).obj (op (CommAlgCat.of F F))) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ hρP hmuP) hq
  have hγ' := rational_mem_parabolicRationalImage hγ
  refine Set.mem_mul.mpr ⟨(rational F G (ρG * muG * q))⁻¹,
    (parabolicRationalImage _).inv_mem hγ', rational F G (ρG * muG * q) * x, ?_, by group⟩
  rw [mem_siegelSet_iff]
  refine ⟨rational F _ ρN * n₂, hρN, rationalNormOne F _ mu * m, hmu, a, fun β hβ => ?_, k,
    hk, ?_⟩
  · -- the chamber condition
    rw [map_sub, eval_height_positiveTorusMap hi hK hρ β a, eval_tmul]
    have hβΔ : β ∈ simpleRelativeRoots i ν := hS₁' hβ
    have hpair : (1 : ℝ) ≤ (latticePairing T β ν : ℝ) := by
      have h1 : (1 : ℤ) ≤ latticePairing T β ν := hβΔ.1.2
      exact_mod_cast h1
    have hta : t₀ ≤ PositiveRealTorus.normCharacter F T β (a : AdelicGroupPoints F T.toGrp) :=
      (ht₀ ⟨⟨S₁, hS₁⟩, rfl⟩).trans (ha β hβ)
    have hpos₀ : (0 : ℝ) < ((t₀ : ℝ≥0) : ℝ) :=
      NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr t₀.ne_zero)
    have hlog : Real.log ((t₀ : ℝ≥0) : ℝ) ≤ Real.log ((PositiveRealTorus.normCharacter F T β
        (a : AdelicGroupPoints F T.toGrp) : ℝ≥0) : ℝ) :=
      Real.log_le_log hpos₀ (NNReal.coe_le_coe.mpr (Units.val_le_val.mpr hta))
    have hc0 : c ≤ 0 := by
      have := min_le_right (Real.log ((t₀ : ℝ≥0) : ℝ)) 0
      simp only [c]
      linarith
    have hc1 : c < Real.log ((t₀ : ℝ≥0) : ℝ) := by
      have := min_le_left (Real.log ((t₀ : ℝ≥0) : ℝ)) 0
      simp only [c]
      linarith
    have hc2 : c * (latticePairing T β ν : ℝ) ≤ c := by nlinarith
    linarith
  · rw [positiveTorusMap_apply]
    change ιN (rational F _ ρN * n₂) *
        ιM ((rationalNormOne F _ mu * m : normOneSubgroup F _) : AdelicGroupPoints F _) *
        map F T.toGrp G i (a : AdelicGroupPoints F T.toGrp) * k =
      rational F G (ρG * muG * q) * x
    have hn₃ : ιN n₂ = rational F G muG * ιN n * (rational F G muG)⁻¹ := hn₂
    rw [Subgroup.coe_mul, rationalNormOne_val, map_mul, map_mul, hρG, hmuG, hn₃, map_mul,
      map_mul, mul_assoc (rational F G ρG * rational F G muG), ← heq]
    group

end Langlands.Global.ArthurTruncation
