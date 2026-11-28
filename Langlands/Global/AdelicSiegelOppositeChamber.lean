import Langlands.Global.AdelicLocalFinitenessChamberCoordinates
import Langlands.Global.AdelicWavePacketRapidDecaySiegelReduction
import Langlands.GroupScheme.Dynamic.RootSystemDeterminantRestriction

/-! # Reversal of a Siegel chamber -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj NNReal

set_option autoImplicit false

namespace Langlands.Global.AdelicSiegelFactors

open Langlands.GroupScheme PositiveRealTorus

variable {F : Type} [Field F] [NumberField F]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  {T T₀ : CommGroupScheme (Spec (CommRingCat.of F))}
  (i : T.toGrp ⟶ G) (ν : cocharacterLattice T) (j : T₀ ⟶ T)

omit [NumberField F] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom] in
private theorem neg_mem_positiveRoots_iff [Mono i.hom.hom.left]
    (hroot : HasRelativeRootSystem i) (hT : IsSplitTorus T.toGrp) (α : characterLattice T) :
    -α ∈ positiveRelativeRoots i (-ν) ↔ α ∈ positiveRelativeRoots i ν := by
  have hmem : -α ∈ relativeRoots i ↔ α ∈ relativeRoots i :=
    ⟨fun h => by simpa only [neg_neg] using hroot.neg_mem_relativeRoots i hT h,
      hroot.neg_mem_relativeRoots i hT⟩
  change (-α ∈ relativeRoots i ∧ 0 < latticePairing T (-α) (-ν)) ↔
    (α ∈ relativeRoots i ∧ 0 < latticePairing T α ν)
  simp only [hmem, map_neg, LinearMap.neg_apply, neg_neg]

omit [NumberField F] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom] in
private theorem neg_mem_simpleRoots [Mono i.hom.hom.left]
    (hroot : HasRelativeRootSystem i) (hT : IsSplitTorus T.toGrp)
    {α : characterLattice T} (hα : α ∈ simpleRelativeRoots i ν) :
    -α ∈ simpleRelativeRoots i (-ν) := by
  refine ⟨(neg_mem_positiveRoots_iff i ν hroot hT α).mpr hα.1, ?_⟩
  rintro ⟨β, hβ, χ, hχ, hsum⟩
  refine hα.2 ⟨-β, ?_, -χ, ?_, ?_⟩
  · simpa only [neg_neg] using (neg_mem_positiveRoots_iff i (-ν) hroot hT β).mpr hβ
  · simpa only [neg_neg] using (neg_mem_positiveRoots_iff i (-ν) hroot hT χ).mpr hχ
  · simpa only [neg_neg, neg_add] using congrArg Neg.neg hsum

private theorem normCharacter_neg_inv
    (a : intrinsicSubgroup F T₀) (α : characterLattice T) :
    normCharacter F T₀ (j ≫ (-α)) a⁻¹ = normCharacter F T₀ (j ≫ α) a := by
  have hneg : normCharacter F T₀ (j ≫ (-α)) a = (normCharacter F T₀ (j ≫ α) a)⁻¹ := by
    rw [eq_inv_iff_mul_eq_one, normCharacter_apply, normCharacter_apply, ← map_mul,
      ← characterValue_add', ← Preadditive.comp_add, neg_add_cancel, Limits.comp_zero,
      characterValue_zero', map_one]
  change normCharacter F T₀ (j ≫ (-α)) a.val⁻¹ = _
  rw [map_inv, hneg, inv_inv]

omit [NumberField F] [IsAffine G.X.left] in
/-- The opposite generic cocharacter retains the same split data. -/
theorem IsSiegelAlgebraicSetup.opposite
    (hG : IsConnectedReductive G) (h : IsSiegelAlgebraicSetup F G T i ν T₀ j) :
    IsSiegelAlgebraicSetup F G T i (-ν) T₀ j := by
  obtain ⟨hi, hν, _, _, _, _, _, hD, hZ⟩ := h
  have hν' : IsGenericCocharacter i (-ν) := by
    intro α hα
    simpa only [map_neg, neg_ne_zero] using hν α hα
  obtain ⟨_, hL, hU⟩ := standardMinimalLeviStructure F G T i (-ν) hG hi hν'
  exact ⟨hi, hν',
    Standard.isMinimalParabolicSubgroup_parabolicHom_of_genericMinimal i (-ν)
      genericMinimalParabolic hG hi hν',
    hL, hU, standardLevi_empty_eq_torusCentralizer_of_generic i (-ν) hG hi hν',
    relativeRoots_torusToStandardParabolic F G T i (-ν) hG hi hν', hD, hZ⟩

omit [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom] in
/-- Inverse torus points lie in the opposite chamber with the same threshold. -/
theorem inv_mem_weakSimpleRootChamber_opposite [Mono i.hom.hom.left]
    (hroot : HasRelativeRootSystem i) (hT : IsSplitTorus T.toGrp)
    {t : ℝ≥0ˣ} {a : intrinsicSubgroup F T₀}
    (ha : a ∈ weakSimpleRootChamber F T₀ T j G i ν t) :
    a⁻¹ ∈ weakSimpleRootChamber F T₀ T j G i (-ν) t := by
  intro β hβ
  have hb := ha (-β) (by
    simpa only [neg_neg] using neg_mem_simpleRoots i (-ν) hroot hT hβ)
  rw [← normCharacter_neg_inv j a (-β), neg_neg] at hb
  exact hb

omit [IsAffine G.X.left] in
/-- The Siegel modulus for the opposite cocharacter at an inverse point equals
the original modulus at the point. -/
theorem siegelModulus_opposite_inv [Mono i.hom.hom.left]
    (hroot : HasRelativeRootSystem i) (hT : IsSplitTorus T.toGrp)
    (a : intrinsicSubgroup F T₀) :
    siegelModulus F G T i (-ν) T₀ j a⁻¹ = siegelModulus F G T i ν T₀ j a := by
  classical
  have hfin (cochar : cocharacterLattice T) := hT.finite_positiveRelativeRoots i cochar
  rw [siegelModulus, siegelModulus, finprod_mem_eq_finite_toFinset_prod _ (hfin (-ν)),
    finprod_mem_eq_finite_toFinset_prod _ (hfin ν)]
  refine Finset.prod_bij' (fun β _ => -β) (fun β _ => -β) ?_ ?_ ?_ ?_ ?_
  · intro β hβ
    exact (hfin ν).mem_toFinset.mpr (by
      simpa only [neg_neg] using
        (neg_mem_positiveRoots_iff i (-ν) hroot hT β).mpr ((hfin (-ν)).mem_toFinset.mp hβ))
  · intro β hβ
    exact (hfin (-ν)).mem_toFinset.mpr
      ((neg_mem_positiveRoots_iff i ν hroot hT β).mpr ((hfin ν).mem_toFinset.mp hβ))
  · intro β _
    exact neg_neg β
  · intro β _
    exact neg_neg β
  · intro β _
    have hnorm := normCharacter_neg_inv j a (-β)
    rw [neg_neg] at hnorm
    rw [hroot.finrank_weightSpace_neg hT, Subgroup.coe_inv, hnorm]

end Langlands.Global.AdelicSiegelFactors

namespace Langlands.Global

open Langlands.GroupScheme AdelicSiegelFactors PositiveRealTorus

/-- Opposite Siegel data on the same maximal split torus identify the weak
chambers by inversion, with the same value of the modulus. -/
def AdelicSiegelOppositeChamberStatement : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (G : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom],
    IsConnectedReductive G →
    ∀ (T : CommGroupScheme (Spec (CommRingCat.of F))) (i : T.toGrp ⟶ G)
      (ν : cocharacterLattice T) (T₀ : CommGroupScheme (Spec (CommRingCat.of F))) (j : T₀ ⟶ T),
    IsSiegelAlgebraicSetup F G T i ν T₀ j →
    IsSiegelAlgebraicSetup F G T i (-ν) T₀ j ∧
      ∀ (a : intrinsicSubgroup F T₀) (t : ℝ≥0ˣ),
        (a⁻¹ ∈ weakSimpleRootChamber F T₀ T j G i (-ν) t ↔
          a ∈ weakSimpleRootChamber F T₀ T j G i ν t) ∧
        siegelModulus F G T i (-ν) T₀ j a⁻¹ = siegelModulus F G T i ν T₀ j a

theorem adelicSiegelOppositeChamber : AdelicSiegelOppositeChamberStatement := by
  intro F _ _ G _ _ _ hG T i ν T₀ j hSetup
  have hi := hSetup.1
  let : Mono i.hom.hom.left := hi.isSplitSubtorus.mono
  have hroot := relativeRootSystem F G hG T i hi
  have hT := hi.isSplitSubtorus.1
  refine ⟨IsSiegelAlgebraicSetup.opposite i ν j hG hSetup,
    fun a t => ⟨⟨?_, ?_⟩, siegelModulus_opposite_inv i ν j hroot hT a⟩⟩
  · intro ha
    simpa only [neg_neg, inv_inv] using inv_mem_weakSimpleRootChamber_opposite i (-ν) j hroot hT ha
  · exact inv_mem_weakSimpleRootChamber_opposite i ν j hroot hT

end Langlands.Global
