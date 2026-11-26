import Langlands.Global.ArthurSiegelSets
import Langlands.Global.ArthurTruncationCentralTranslation
import Langlands.Global.AdelicSiegelNormMinimalityAssembly
import Langlands.Global.AdelicSiegelDiagonalHeightBound

/-! # Norm minimality on Arthur's Siegel sets -/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory NumberField TensorProduct
open scoped CategoryTheory.MonObj NNReal

namespace Langlands.Global.ArthurTruncation

open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace AdelicGroupPoints
  ArthurParabolicSpaces AdelicSiegelFactors PositiveRealTorus RepresentationGrowth

variable {F : Type u} [Field F] [NumberField F] {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  {T : CommGroupScheme (Spec (CommRingCat.of F))} {i : T.toGrp ⟶ G} [Mono i.hom.hom.left]
  {ν : cocharacterLattice T} {K : Subgroup (AdelicGroupPoints F G)}
  (hi : IsMaximalSplitTorus i) (hK : IsIwasawaCompact (Standard.parabolicHom i ν ∅) K)
  (hρ : Function.Bijective (restrictToTorus F i ν ∅))

omit [LocallyOfFiniteType G.X.hom] [Mono i.hom.hom.left] in
/-- A root coordinate of the Iwasawa height on the torus is the logarithm of the
normalized idelic norm. -/
theorem eval_height_positiveTorusMap (α : characterLattice T) (a : intrinsicSubgroup F T) :
    eval T α (height hi hK hρ (positiveTorusMap F i a)) =
      Real.log ((normCharacter F T α a : ℝ≥0) : ℝ) := by
  change eval T α (height hi hK hρ
    (map F T.toGrp G (CommGroupScheme.groupHom (𝟙 T) ≫ i) a.val)) = _
  have hid : CommGroupScheme.groupHom (𝟙 T) = 𝟙 T.toGrp := rfl
  rw [hid, Category.id_comp, eval_height_torus, realParameterPairing_tmul, one_mul,
    characterLog_apply]
  rfl

/-- Arthur's shifted chamber is contained in a weak simple-root chamber for one positive
threshold. -/
theorem exists_siegelChamber_subset_weak (hG : IsConnectedReductive G) (T₁ : V T) :
    ∃ t : ℝ≥0ˣ, siegelChamber hi hK hρ (simpleFinset ν hG hi) T₁ ⊆
      weakSimpleRootChamber F T T (𝟙 T) G i ν t := by
  have hfinite := hi.isSplitSubtorus.1.finite_simpleRelativeRoots i ν
  obtain ⟨b, hb⟩ := (hfinite.image (fun α => eval T α T₁)).bddBelow
  let r : ℝ≥0 := ⟨Real.exp b, (Real.exp_pos b).le⟩
  have hr : 0 < r := NNReal.coe_pos.mp (Real.exp_pos b)
  let t : ℝ≥0ˣ := Units.mk0 r hr.ne'
  refine ⟨t, fun a ha α hα => ?_⟩
  have hbα : b ≤ eval T α T₁ := hb ⟨α, hα, rfl⟩
  have hα' := ha α ((mem_simpleFinset hG hi).mpr hα)
  rw [map_sub, eval_height_positiveTorusMap hi hK hρ] at hα'
  have hn : 0 < ((normCharacter F T α a : ℝ≥0) : ℝ) :=
    NNReal.coe_pos.mpr (normCharacter F T α a).ne_zero.bot_lt
  change t ≤ normCharacter F T ((𝟙 T) ≫ α) a
  rw [Category.id_comp]
  apply Units.val_le_val.mp
  apply NNReal.coe_le_coe.mp
  change Real.exp b ≤ ((normCharacter F T α a : ℝ≥0) : ℝ)
  rw [← Real.exp_log hn]
  exact Real.exp_le_exp.mpr (hbα.trans (sub_pos.mp hα').le)

/-- On Arthur's full Siegel set, the height is at most a fixed multiple of the
height of each rational left translate. -/
def ArthurSiegelNormMinimalityStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom]
    [LocallyOfFiniteType G.X.hom]
    (T : CommGroupScheme (Spec (CommRingCat.of F))) (i : T.toGrp ⟶ G) [Mono i.hom.hom.left]
    (ν : cocharacterLattice T) (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i),
    IsGenericCocharacter i ν →
    ∀ (K : Subgroup (AdelicGroupPoints F G))
      (hK : IsIwasawaCompact (Standard.parabolicHom i ν ∅) K)
      (hρ : Function.Bijective (restrictToTorus F i ν ∅)) {N : ℕ}
      (rho : MatrixRepresentation G (Fin N)), 0 < N →
      ∀ (C : CompactFactors F G (Standard.unipotentScheme i ν ∅) (Standard.leviScheme i ν ∅))
        (T₁ : V T), ∃ B : ℝ, 1 ≤ B ∧
        ∀ x ∈ siegelSet hi hK hρ C (simpleFinset ν hG hi) T₁, ∀ q : RationalGroupPoints F G,
          adelicHeight F G rho x ≤ B * adelicHeight F G rho (rational F G q * x)

/-- The diagonal bound and compact unipotent conjugation give the full-torus estimate. -/
theorem arthurSiegelNormMinimality : ArthurSiegelNormMinimalityStatement.{u} := by
  intro F _ _ G _ _ T i _ ν hG hi hν K hK hρ N rho hN C T₁
  obtain ⟨t, ht⟩ := exists_siegelChamber_subset_weak hi hK hρ hG T₁
  obtain ⟨c, hc, hdiag⟩ := exists_adelicHeight_map_le_rational_mul F G rho hN T
    hi.isSplitSubtorus.1 (CommGroupScheme.groupHom (𝟙 T) ≫ i)
  obtain ⟨B, hB⟩ := exists_adelicHeight_le_mul_rational_of_maximalSplit F G T i ν T (𝟙 T)
    hG hi hν rho hN C t hc hdiag
  refine ⟨max 1 B, le_max_left _ _, fun x hx q => ?_⟩
  obtain ⟨n, hn, m, hm, a, ha, k, hk, hx⟩ := (mem_siegelSet_iff hi hK hρ C _ T₁ x).mp hx
  have hmem := (mem_productSet_iff F G T i ν (canonicalStandardFactors F G T i ν) C T (𝟙 T)
    _ x).mpr ⟨n, hn, m, hm, a, ht ha, k, hk, hx⟩
  exact (hB x hmem q).trans (mul_le_mul_of_nonneg_right (le_max_right _ _)
    (zero_le_one.trans (one_le_adelicHeight F G rho hN _)))

end Langlands.Global.ArthurTruncation
