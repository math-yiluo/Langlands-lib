import Langlands.Global.AdelicTemperedVanishingReduction
import Langlands.Global.AdelicWavePacketRapidDecaySiegelReduction
import Langlands.Global.AdelicParabolicModulusProof
import Langlands.Global.AdelicSiegelDominatedIntegrabilityProof
import Langlands.Global.AdelicWeakConstantTermTransitivity
import Langlands.GroupScheme.Rational.PositiveTorusTriangularCoordinatesProof

/-! # Comparison of the Siegel modulus and the standard half modulus -/

noncomputable section

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj NNReal

set_option autoImplicit false

namespace Langlands.Global.StandardParabolicFamily

open GroupScheme AdelicGroupPoints AdelicSiegelFactors

variable {F : Type} [Field F] [NumberField F] {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  (fam : StandardParabolicFamily F G)

/-- The positive square root of the Siegel modulus agrees with the half modulus
at the corresponding point of the minimal parabolic. -/
theorem halfModulus_bot_eq_siegelSqrt
    {T₀ : CommGroupScheme (Spec (CommRingCat.of F))} {j : T₀ ⟶ fam.T}
    (hsetup : IsSiegelAlgebraicSetup F G fam.T fam.i fam.ν T₀ j)
    (a : PositiveRealTorus.intrinsicSubgroup F T₀) :
    fam.halfModulus fam.bot (map F T₀.toGrp (fam.P fam.bot)
        (CommGroupScheme.groupHom j ≫ fam.torus fam.bot ≫ fam.l fam.bot) a.val) =
      (Real.sqrt (siegelModulus F G fam.T fam.i fam.ν T₀ j a) : ℂ) := by
  let P := fam.P fam.bot
  let p := fam.p fam.bot
  let U := Standard.unipotentScheme fam.i fam.ν ∅
  let u := Standard.unipotentHom fam.i fam.ν ∅
  obtain ⟨ζ, hζ, hP, _⟩ := (fam.isCompatible fam.bot).realization
  let χ := CommGroupScheme.groupHom ζ ≫ fam.i
  have hPr : (Dynamic.parabolic χ).IsRepresentedBy p := by
    rw [← hP]
    exact (fam.isCompatible fam.bot).parabolic.isClosedSubgroup.isRepresentedBy_range
  have hUr : (Dynamic.unipotent χ).IsRepresentedBy u := by
    rw [← ((standardCocharacter F G fam.connectedReductive fam.T fam.i fam.maximalSplit fam.ν
      fam.generic ∅ (Set.empty_subset _)).2 ζ hζ).2.2]
    exact Standard.isRepresentedBy_unipotentHom fam.i fam.ν ∅
  have : Smooth G.X.hom := fam.connectedReductive.smooth
  have : IsAffine U.X.left := isAffine_left_of_isClosedSubgroup F u
    (Standard.isClosedSubgroup_unipotentHom fam.i fam.ν ∅)
  have : LocallyOfFiniteType U.X.hom := locallyOfFiniteType_unipotent F hUr
  let y : AdelicGroupPoints F P := map F T₀.toGrp P
    (CommGroupScheme.groupHom j ≫ fam.torus fam.bot ≫ fam.l fam.bot) a.val
  have hy : map F P G p y = positiveMap F G fam.T fam.i T₀ j a := by
    dsimp only [y]
    rw [← map_comp_apply_of_hom, Category.assoc, Category.assoc, fam.torus_comp]
    rfl
  have hconn : ConnectedSpace P.X.left :=
    ((dynamicConnected F G χ P p).2 fam.connectedReductive.connectedSpace).1 hPr
  have hm := (adelicParabolicModulus F G fam.connectedReductive χ P U p u hPr hUr _
    (Lie.finiteCoordinates U)).2 y
  have hs := positiveTorusUnipotentModulus_of_coordinates positiveTorusTriangularCoordinates
    F G fam.connectedReductive fam.T fam.i fam.ν T₀ j hsetup a
  have he :
      (⟨map F P G p y, map_parabolic_mem_normalizer F hPr hUr y⟩ :
          Subgroup.normalizer (standardUnipotentImage F G fam.T fam.i fam.ν : Set _)) =
        ⟨positiveMap F G fam.T fam.i T₀ j a,
          positiveMap_mem_normalizer F G fam.T fam.i fam.ν T₀ j a⟩ :=
    Subtype.ext hy
  rw [parabolicModulus_apply] at hm
  let c := HaarModulus.closedNormalizerCharacter (standardUnipotentImage F G fam.T fam.i fam.ν)
    (isClosed_standardUnipotentImage F G fam.T fam.i fam.ν)
  have hmod : Measure.modularCharacter y = siegelModulusNN (i := fam.i) (ν := fam.ν) (j := j) a :=
    hm.trans ((congrArg (fun x => (c x : ℝ≥0)) he).trans hs)
  change fam.halfModulus fam.bot y = _
  rw [fam.halfModulus_eq_sqrt_modularCharacter fam.bot hconn y, hmod, coe_siegelModulusNN]

/-- When the torus point lies in the positive split component of a standard parabolic,
the same comparison holds for the half modulus of that parabolic. -/
theorem halfModulus_eq_siegelSqrt_of_positiveSplitComponent
    (hδ : StandardNestedHalfModulusCompatibilityStatement)
    {T₀ : CommGroupScheme (Spec (CommRingCat.of F))} {j : T₀ ⟶ fam.T}
    (hsetup : IsSiegelAlgebraicSetup F G fam.T fam.i fam.ν T₀ j)
    (J : StandardIndex F G fam.i fam.ν) (a : PositiveRealTorus.intrinsicSubgroup F T₀)
    (x : fam.positiveSplitComponent J)
    (hx : map F (fam.P J) G (fam.p J) x.val = positiveMap F G fam.T fam.i T₀ j a) :
    fam.halfModulus J x.val = (Real.sqrt (siegelModulus F G fam.T fam.i fam.ν T₀ j a) : ℂ) := by
  obtain ⟨y, hy, _⟩ := fam.exists_positiveSplitComponent_lift_with_values
    (show fam.bot ≤ J from Set.empty_subset _) x
  have hcmp := hδ F G fam fam.bot J (Set.empty_subset _) x y hy
  let z := map F T₀.toGrp (fam.P fam.bot)
    (CommGroupScheme.groupHom j ≫ fam.torus fam.bot ≫ fam.l fam.bot) a.val
  have hz : map F (fam.P fam.bot) G (fam.p fam.bot) z = positiveMap F G fam.T fam.i T₀ j a := by
    dsimp only [z]
    rw [← map_comp_apply_of_hom, Category.assoc, Category.assoc, fam.torus_comp]
    rfl
  have he : y.val = z :=
    (isClosedEmbedding_map_of_isClosedSubgroup F (fam.p fam.bot)
      (fam.isCompatible fam.bot).parabolic.isClosedSubgroup).injective (hy.trans (hx.trans hz.symm))
  rw [← hcmp, he]
  exact fam.halfModulus_bot_eq_siegelSqrt hsetup a

end Langlands.Global.StandardParabolicFamily

namespace Langlands.Global

open GroupScheme AdelicGroupPoints AdelicSiegelFactors

/-- When a Siegel torus point represents a positive split point of a standard parabolic,
its Siegel modulus has square root equal to that parabolic's half modulus. -/
def AdelicSiegelHalfModulusStatement : Prop :=
  StandardNestedHalfModulusCompatibilityStatement →
  ∀ (F : Type) [Field F] [NumberField F] (G : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom],
    ∀ (fam : StandardParabolicFamily F G)
      (T₀ : CommGroupScheme (Spec (CommRingCat.of F))) (j : T₀ ⟶ fam.T),
      IsSiegelAlgebraicSetup F G fam.T fam.i fam.ν T₀ j →
    ∀ (J : StandardIndex F G fam.i fam.ν) (a : PositiveRealTorus.intrinsicSubgroup F T₀)
      (x : fam.positiveSplitComponent J),
      map F (fam.P J) G (fam.p J) x.val = positiveMap F G fam.T fam.i T₀ j a →
      fam.halfModulus J x.val = (Real.sqrt (siegelModulus F G fam.T fam.i fam.ν T₀ j a) : ℂ)

theorem adelicSiegelHalfModulus : AdelicSiegelHalfModulusStatement := by
  intro hδ F _ _ G _ _ _ fam T₀ j hsetup J a x hx
  exact fam.halfModulus_eq_siegelSqrt_of_positiveSplitComponent hδ hsetup J a x hx

end Langlands.Global
