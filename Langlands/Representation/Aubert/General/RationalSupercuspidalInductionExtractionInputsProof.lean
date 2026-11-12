import Langlands.Representation.Aubert.General.RationalSupercuspidalInductionExtractionInputsStatement
import Langlands.Representation.Aubert.General.RationalSupercuspidalInductionInputsProof
import Langlands.Representation.Aubert.General.RationalIrreducibleJacquetFactorDetection
import Langlands.Representation.Aubert.General.RationalCorrectedLeviCriterion

/-! # Actual supercuspidal induction finite length from the cuspidal extraction inputs -/

noncomputable section

set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency.types false

universe u v uG uV

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RationalPointFamily

open GroupScheme SmoothRep Group.RelativeWeylIndexing
open Langlands.AlgebraicGeometry.PointTopology

/-- A smooth representation with a finite zero-to-full filtration whose grades
have length at most one has finite length. -/
theorem smooth_hasFiniteLength_of_filtration_grades_le_one
    {H : Type uG} [Group H] [TopologicalSpace H]
    {A : SmoothRep.{0, uG, uV} ℂ H} {r : ℕ} (s : ObjectRepFiltration A.obj r)
    (hle : ∀ q : Fin r, repLength (s.gradedRepresentation q).ρ ≤ 1) :
    A.HasFiniteLength := by
  have hsum : repLength A.representation ≤ r := by
    have h := repLength_eq_sum_of_filtration s
    calc repLength A.representation
        = ∑ q : Fin r, repLength (s.gradedRepresentation q).ρ := h
      _ ≤ ∑ _q : Fin r, (1 : ℕ∞) := Finset.sum_le_sum fun q _ => hle q
      _ = r := by simp
  exact Module.length_ne_top_iff.mp (ne_top_of_le_ne_top (ENat.natCast_ne_top r) hsum)

/-- A smooth representation isomorphic to a conjugate of an irreducible
representation has length at most one. -/
theorem repLength_le_one_of_iso_conjugation
    {H : Type uG} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    {L M : Subgroup H} (g : H) (hg : ∀ x : H, x ∈ M ↔ g⁻¹ * x * g ∈ L)
    {σ : SmoothRep.{0, uG, uV} ℂ L} (hσ : σ.IsIrreducible)
    {X : SmoothRep.{0, uG, uV} ℂ M} (e : X ≅ (conjugationFunctor g hg).obj σ) :
    repLength X.representation ≤ 1 := by
  have hirr : ((conjugationFunctor g hg).obj σ).IsIrreducible :=
    (Langlands.isIrreducible_comp_continuousMulEquiv_iff
      σ.representation (conjugationEquiv g hg)).mpr hσ
  exact (repLength_congr (SmoothRep.equivOfIso e)).trans_le
    (repLength_eq_one_iff.mpr hirr).le

section Fixed

variable {k : Type u} [Field k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  (i : T.toGrp ⟶ G) [Mono i.hom.hom.left]
  (ν : cocharacterLattice T) [Fintype (SimpleRoot i ν)]
  (hN : HasPointNormalizerComparison i) (hZ : HasPointCentralizerComparison i)

/-- At a minimum for root-associated indices, a full source intersection forces
a full inverse intersection. -/
theorem intersectionSubset_inv_eq_of_rootAssociation
    {C : CoxeterMatrix (SimpleRoot i ν)} (cs : ActualCoxeterSystem (torusPoints i) C)
    {I J : Finset (SimpleRoot i ν)} {n : RationalPoint k G.X}
    (hIJ : rootAssociation i ν hN hZ I J n) {w : Weyl i} (hw : IsMinimal cs J I w)
    (hS : intersectionSubset cs J I w = I) :
    intersectionSubset cs I J w⁻¹ = J := by
  classical
  have hS' : simpleImage cs w⁻¹ J ∩ I = I := by
    ext a
    simpa only [Finset.mem_inter] using
      (Finset.ext_iff.mp ((intersectionSubset_eq_simpleImage_inter cs hw).symm.trans hS) a)
  have hc : (simpleImage cs w⁻¹ J ∩ I).card = (simpleImage cs w I ∩ J).card :=
    card_simpleImage_intersections cs w I J
  rw [hS', rootAssociation_card_eq i ν hN hZ hIJ] at hc
  have hT' : simpleImage cs w I ∩ J = J :=
    Finset.eq_of_subset_of_card_le Finset.inter_subset_right hc.le
  ext a
  have h1 := Finset.ext_iff.mp
    (intersectionSubset_eq_simpleImage_inter cs (isMinimal_inv cs hw)) a
  have h2 := Finset.ext_iff.mp hT' a
  simp only [Finset.mem_inter, inv_inv] at h1 h2
  rw [h1]
  exact h2

variable [TopologicalSpace k]

local instance rationalSupercuspidalExtractionInputsPointTopology :
    TopologicalSpace (RationalPoint k G.X) := pointTopology

variable [LocallyCompactSpace (RationalPoint k G.X)]
  [NonarchimedeanGroup (RationalPoint k G.X)]
  (hStandard : StandardCocharacterStatement.{u})
  (hInter : StandardLeviIntersectionStatement.{u})
  (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  (hν : IsGenericCocharacter i ν)
  (hM : ∀ A, IsClosed (levi i ν A : Set (RationalPoint k G.X)))
  (hU : ∀ A, IsClosed (unipotent i ν A : Set (RationalPoint k G.X)))

/-- Full source intersection: the actual geometric term is the irreducible
conjugate of `σ`, so it has length at most one. -/
theorem pointAssociatedCuspidalGeometricTerm_repLength_le_one_of_full
    {C : CoxeterMatrix (SimpleRoot i ν)} {cs : ActualCoxeterSystem (torusPoints i) C}
    (hGeom : PointCuspidalExtractionGeometry.{u, v}
      i ν hN hZ cs hG hi hν hInter hM hU)
    {I J : Finset (SimpleRoot i ν)} {n : RationalPoint k G.X}
    (hIJ : rootAssociation i ν hN hZ I J n)
    (σ : SmoothRep.{0, u, max (u + 1) v} ℂ (levi i ν I)) (hσ : σ.IsIrreducible)
    (w : Weyl i) (hw : IsMinimal cs J I w)
    (m : Group.RelativeWeyl.normalizer (torusPoints i)) (hm : QuotientGroup.mk m = w)
    (hs : GeometricSourceDecomposition (parabolic i ν) (levi i ν) (unipotent i ν) J I m)
    (ht : GeometricTargetDecomposition (parabolic i ν) (levi i ν) (unipotent i ν) J I m)
    (hS : intersectionSubset cs J I w = I) :
    repLength ((geometricTermFunctor.{u, u, max (u + 1) v}
      (parabolic i ν) (levi i ν) (unipotent i ν) hM hU J I m hs ht).obj σ).representation
      ≤ 1 := by
  have hT := intersectionSubset_inv_eq_of_rootAssociation i ν hN hZ cs hIJ hw hS
  obtain ⟨hConj, -, ⟨eConj⟩⟩ := hGeom.2.2.2 I J w hw m hm hs ht hS hT σ
  exact repLength_le_one_of_iso_conjugation _ hConj hσ eConj

/-- Proper source intersection: the actual geometric term of an inside-Levi
cuspidal `σ` vanishes, so it has length at most one. -/
theorem pointAssociatedCuspidalGeometricTerm_repLength_le_one_of_proper
    {C : CoxeterMatrix (SimpleRoot i ν)} {cs : ActualCoxeterSystem (torusPoints i) C}
    (hGeom : PointCuspidalExtractionGeometry.{u, v}
      i ν hN hZ cs hG hi hν hInter hM hU)
    {I J : Finset (SimpleRoot i ν)}
    (σ : SmoothRep.{0, u, max (u + 1) v} ℂ (levi i ν I))
    (hcσ : IsCorollaryLeviCuspidal.{u, u, max (u + 1) v}
      (parabolic i ν) (levi i ν) (unipotent i ν)
      I (hM I) (isSemidirectDecomposition_in_levi i ν hInter hG hi hν I) hU σ)
    (w : Weyl i) (hw : IsMinimal cs J I w)
    (m : Group.RelativeWeyl.normalizer (torusPoints i)) (hm : QuotientGroup.mk m = w)
    (hs : GeometricSourceDecomposition (parabolic i ν) (levi i ν) (unipotent i ν) J I m)
    (ht : GeometricTargetDecomposition (parabolic i ν) (levi i ν) (unipotent i ν) J I m)
    (hS : intersectionSubset cs J I w ≠ I) :
    repLength ((geometricTermFunctor.{u, u, max (u + 1) v}
      (parabolic i ν) (levi i ν) (unipotent i ν) hM hU J I m hs ht).obj σ).representation
      ≤ 1 :=
  (repLength_eq_zero_iff.mpr (hGeom.2.2.1 J I w hw m hm hs ht σ hcσ hS)).trans_le
    zero_le_one

/-- A filtration of an actual smooth representation of `levi i ν J` whose
grades are actual geometric terms of an irreducible inside-Levi cuspidal `σ`
along a root-associated pair proves that the representation has finite
length. -/
theorem pointAssociatedCuspidal_hasFiniteLength_of_geometricGrades
    {C : CoxeterMatrix (SimpleRoot i ν)} {cs : ActualCoxeterSystem (torusPoints i) C}
    (hGeom : PointCuspidalExtractionGeometry.{u, v}
      i ν hN hZ cs hG hi hν hInter hM hU)
    {I J : Finset (SimpleRoot i ν)} {n : RationalPoint k G.X}
    (hIJ : rootAssociation i ν hN hZ I J n)
    (σ : SmoothRep.{0, u, max (u + 1) v} ℂ (levi i ν I)) (hσ : σ.IsIrreducible)
    (hcσ : IsLeviCuspidal (parabolic i ν) (levi i ν) (unipotent i ν) hU I (hM I)
      (isSemidirectDecomposition_in_levi i ν hInter hG hi hν I) σ)
    {A : SmoothRep.{0, u, max (u + 1) v} ℂ (levi i ν J)}
    {r : ℕ} (s : ObjectRepFiltration A.obj r)
    (hgrades : ∀ q : Fin r,
      ∃ (w : Weyl i) (_hw : IsMinimal cs J I w)
        (m : Group.RelativeWeyl.normalizer (torusPoints i)) (_hm : QuotientGroup.mk m = w)
        (hs : GeometricSourceDecomposition
          (parabolic i ν) (levi i ν) (unipotent i ν) J I m)
        (ht : GeometricTargetDecomposition
          (parabolic i ν) (levi i ν) (unipotent i ν) J I m),
        Nonempty
          (s.smoothGradedObject q ≅
            (geometricTermFunctor.{u, u, max (u + 1) v}
              (parabolic i ν) (levi i ν) (unipotent i ν) hM hU J I m hs ht).obj σ)) :
    A.HasFiniteLength := by
  have hcσ' := (isCorollaryLeviCuspidal_iff_isLeviCuspidal.{u, u, max (u + 1) v}
    I (hM I) (isSemidirectDecomposition_in_levi i ν hInter hG hi hν I) σ).mpr hcσ
  refine smooth_hasFiniteLength_of_filtration_grades_le_one s fun q => ?_
  obtain ⟨w, hw, m, hm, hs, ht, ⟨e⟩⟩ := hgrades q
  have h : repLength ((geometricTermFunctor.{u, u, max (u + 1) v}
      (parabolic i ν) (levi i ν) (unipotent i ν) hM hU J I m hs ht).obj σ).representation
      ≤ 1 := by
    by_cases hS : intersectionSubset cs J I w = I
    · exact pointAssociatedCuspidalGeometricTerm_repLength_le_one_of_full
        i ν hN hZ hInter hG hi hν hM hU hGeom hIJ σ hσ w hw m hm hs ht hS
    · exact pointAssociatedCuspidalGeometricTerm_repLength_le_one_of_proper
        i ν hN hZ hInter hG hi hν hM hU hGeom σ hcσ' w hw m hm hs ht hS
  rw [← repLength_congr (SmoothRep.equivOfIso e)] at h
  exact h

end Fixed

/-- The published extraction inputs prove finite length of every actual
associated cuspidal Jacquet module `r_J i_I σ`. Only the geometric-filtration
conjunct is used. -/
theorem rationalAssociatedCuspidalJacquetFiniteLength_of_extractionInputs
    (hInputs : RationalCuspidalExtractionInputsStatement.{u, v}) :
    RationalAssociatedCuspidalJacquetFiniteLengthStatement.{u, v} := by
  intro k _ _ _ _ G hG T i hi
  have := hG.isAffineHom
  have := hi.isSplitSubtorus.mono
  let : TopologicalSpace (RationalPoint k G.X) := pointTopology
  intro _ _ _ ν hν hStandard hInter hRoots hN hZ hU hM
  let := simpleRelativeRootFintype i hRoots hi.isSplitSubtorus.1 ν
  intro h hL I J n hIJ σ hσ hcσ
  obtain ⟨⟨C, cs, hLength, hF⟩, -⟩ :=
    hInputs k G hG T i hi ν hν hStandard hInter hRoots hN hZ hU hM
  have hSimple := positiveSimpleReflectionComparison_of_rootLength
    i ν hN hZ cs hi.isSplitSubtorus.1 hRoots hν hLength
  have hGeom := pointCuspidalExtractionGeometry_of_rootComparisons.{u, v}
    i ν hN hZ cs hLength hSimple hG hi hν hStandard hInter hM hU
  obtain ⟨r, s, hgrades⟩ := hF I J σ
  exact pointAssociatedCuspidal_hasFiniteLength_of_geometricGrades
    i ν hN hZ hInter hG hi hν hM hU hGeom hIJ σ hσ hcσ s hgrades

/-- The two published extraction inputs imply the finite-length part of
Renard, Théorème VI.5.4, on the actual standard families: they give Jacquet
detection through factor extraction and associated Jacquet finite length
through the geometric filtration. -/
theorem rationalSupercuspidalInductionFiniteLengthFromExtractionInputs :
    RationalSupercuspidalInductionFiniteLengthFromExtractionInputsStatement.{u, v} :=
  fun hInputs => rationalSupercuspidalInductionFiniteLengthFromInputs
    (rationalSupportCategoryIrreducibleJacquetDetection_of_cuspidalFactors
      (rationalCuspidalJacquetFactorExtraction_of_inputs hInputs))
    (rationalAssociatedCuspidalJacquetFiniteLength_of_extractionInputs hInputs)

end Langlands.Aubert.General.RationalPointFamily
