import Langlands.Representation.Exponents.LeviCompletionComparison
import Langlands.Representation.Exponents.LeviCompletionOppositeJacquetStatement
import Langlands.Representation.Exponents.LeviJacquetContragredientStructure
import Langlands.GroupScheme.Dynamic.OppositeParabolicUniquenessProof

/-!
# The represented completion theorem from the two remaining global inputs

Parabolic dynamics and VI.9.1 uniform compression stabilization imply the exact
published VI.9.7 statement. Opposite dynamic uniqueness is a proved input.
-/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme
open Langlands.HarishChandraSchwartz (CompactOpenSubgroup)

/-- The two remaining global inputs suffice for the exact published VI.9.7
statement. This proposition records the internal reduction. -/
def LeviCompletionStructureStatement : Prop :=
  ParabolicDynamicStatement.{u} →
    RationalPointFamily.UniformCompressionStabilizationStatement.{u, v} →
      LeviCompletionOppositeJacquetStatement.{u, v}

/-- The exact completion statement follows from parabolic dynamics and uniform
compression stabilization. Neither retained input is asserted here. -/
theorem leviCompletionOppositeJacquet_of_structure
    (hPD : ParabolicDynamicStatement.{u})
    (hstab : RationalPointFamily.UniformCompressionStabilizationStatement.{u, v}) :
    LeviCompletionOppositeJacquetStatement.{u, v} := by
  intro k _ _ _ _ _ G hG
  have := hG.isAffineHom
  let : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
  intro _ _ P Pbar M N Nbar p m n hp hm hn hmul
    pbar mbar nbar hpbar hmbar hnbar hmulbar hLevi hPP
  have := hm.isConnectedReductive.isAffineHom
  let := leviPointTopology m hm
  have := leviPoints_locallyCompactSpace p m hp hm
  have := leviPoints_nonarchimedeanGroup p m hp hm
  obtain ⟨χ, hPχ, hMχ⟩ :=
    DynamicLeviConjugacy.exists_cocharacter_parabolic_levi hPD
      dynamicGeometricUnipotentRadical hG hpbar hmbar
  have hNbar : pointImage (nbar ≫ pbar) =
      (Dynamic.unipotent χ).carrier (Over.mk (𝟙 _)) :=
    pointImage_radical_eq_dynamic dynamicGeometricUnipotentRadical hG χ hpbar hPχ hnbar
  have hM : pointImage (mbar ≫ pbar) =
      (Dynamic.centralizer χ).carrier (Over.mk (𝟙 _)) := by
    rw [pointImage_eq_range_carrier, hMχ]
  have hN : pointImage (n ≫ p) =
      (Dynamic.unipotent (Dynamic.inverseCocharacter χ)).carrier (Over.mk (𝟙 _)) := by
    apply pointImage_opposite_radical_eq_dynamic hPD oppositeDynamicParabolicUniqueness
      hG χ mbar hPχ hMχ hp hm hn hLevi.symm
    calc
      pointImage pbar ⊓ pointImage p = pointImage p ⊓ pointImage pbar := inf_comm _ _
      _ = pointImage (m ≫ p) := hPP
      _ = pointImage (mbar ≫ pbar) := congrArg pointImage hLevi.symm
  obtain ⟨g, hc, hB⟩ :=
    RationalPointFamily.dynamic_exists_central_hasOppositeIwahoriContractionBasis hG χ
  have hcentral : ∀ z ∈ pointImage (mbar ≫ pbar), z * g = g * z := by
    simpa only [hM] using hc
  have hBasis : Jacquet.HasOppositeIwahoriContractionBasis
      (pointImage (nbar ≫ pbar)) (pointImage (mbar ≫ pbar)) (pointImage (n ≫ p)) g := by
    simpa only [hNbar, hM, hN] using hB
  have hdata (π : SmoothRep.{0, u, v} ℂ (rationalPoints G))
      (K : CompactOpenSubgroup (rationalPoints G))
      (hK : K ∈ Jacquet.oppositeCompressionIndices
        (pointImage (nbar ≫ pbar)) (pointImage (mbar ≫ pbar)) (pointImage (n ≫ p)) g) :
      (∃ b : ℕ, Jacquet.stableImage π.representation π.isSmooth K.1 K.2 g =
        LinearMap.range (Jacquet.compressedAction π.representation π.isSmooth K.1 K.2 g ^ b)) ∧
      Function.Bijective (Jacquet.stableImageJacquetMap π.representation π.isSmooth
        K.1 K.2 g (pointImage (nbar ≫ pbar)) (pointImage (mbar ≫ pbar))
        (pointImage_le_normalizer pbar mbar nbar hnbar)) := by
    have hI : Jacquet.IsIwahoriContraction K.1
        ((Dynamic.unipotent χ).carrier (Over.mk (𝟙 _)))
        ((Dynamic.centralizer χ).carrier (Over.mk (𝟙 _)))
        ((Dynamic.unipotent (Dynamic.inverseCocharacter χ)).carrier (Over.mk (𝟙 _))) g := by
      simpa only [hNbar, hM, hN] using hK.1
    obtain ⟨b, hb⟩ := hstab k G hG χ K.1 K.2 g hc hI
    have hπ := hb π π.representation π.isSmooth
    refine ⟨⟨b, (hπ.1 b le_rfl).1⟩, ?_⟩
    exact Jacquet.stableImageJacquetMap_bijective_of_splits π.representation π.isSmooth
      K.2 hK.1 (pointImage_le_normalizer pbar mbar nbar hnbar) hπ.2
  let φ := fun π : SmoothRep.{0, u, v} ℂ (rationalPoints G) =>
    leviCompletionComparisonEquiv p m n hp hn pbar mbar nbar hpbar hmbar hnbar hmulbar
      hLevi g hcentral hBasis π (fun K hK => (hdata π K hK).1)
      (fun K => (hdata π K.val K.property).2)
  refine ⟨φ, ?_, ?_⟩
  · intro π x K g' hg' hI KM hKM
    exact leviCompletionComparisonEquiv_apply_of_factor
      p m n hp hn pbar mbar nbar hpbar hmbar hnbar hmulbar hLevi g hcentral hBasis
      π (fun K hK => (hdata π K hK).1) (fun K => (hdata π K.val K.property).2)
      x K (by simpa only [hLevi] using hI.factor) KM hKM
  · intro π σ f x y hxy KM
    exact leviCompletionComparisonEquiv_natural
      p m n hp hn pbar mbar nbar hpbar hmbar hnbar hmulbar hLevi g hcentral hBasis
      π (fun K hK => (hdata π K hK).1) (fun K => (hdata π K.val K.property).2)
      σ (fun K hK => (hdata σ K hK).1) (fun K => (hdata σ K.val K.property).2)
      f x y hxy KM

end Langlands.Aubert.General.RepresentedParabolic
