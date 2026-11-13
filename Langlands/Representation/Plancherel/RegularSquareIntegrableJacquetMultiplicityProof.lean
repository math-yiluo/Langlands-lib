import Langlands.Representation.Plancherel.RegularSquareIntegrableJacquetMultiplicityReduction
import Langlands.Representation.Exponents.SelfUnitaryPieceMultiplicityUnconditional
import Langlands.Representation.Exponents.SquareIntegrableNormalizedTemperedProof
import Langlands.Representation.Exponents.ArbitraryParabolicJacquetAdmissibilityProof
import Langlands.Representation.Exponents.ArbitraryParabolicQuotientCompactProof
import Langlands.Representation.Geometric.RepresentedGeometricLemmaProof

/-! # Actual regular square-integrable Jacquet multiplicity

This module proves `RegularSquareIntegrableJacquetMultiplicityStatement`
(Waldspurger III.7.3 in its Jacquet multiplicity form) outright. The argument is
that of `jacquetInductionHom_rank_le_one_of_statements`, except that the
self-intersection pieces are bounded by the criterion-free lemmas of
`SelfUnitaryPieceMultiplicityUnconditional`; the remaining inputs are the
published geometric lemma, quotient compactness, temperedness of
square-integrable representations and Jacquet admissibility. -/

noncomputable section

open CategoryTheory AlgebraicGeometry MeasureTheory MeasureTheory.Measure
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.Plancherel

universe u uV

open Aubert.General

section Actual

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {A : CommGroupScheme (Spec (CommRingCat.of F))}
  {G M P U : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine M.X.left]
  {p : P ⟶ G} {l : M ⟶ P} {a : A.toGrp ⟶ M} {n : U ⟶ P}
  (pres : ParabolicRootPresentation p l a)

local instance regularMultiplicityProofAmbientAffine : IsAffine G.X.left :=
  isAffine_of_isAffineHom G.X.hom
local instance regularMultiplicityProofAmbientPointTopology :
    TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
local instance regularMultiplicityProofLeviPointTopology :
    TopologicalSpace (rationalPoints M) := rationalPointTopology F M.X
local instance regularMultiplicityProofFieldT2 : T2Space F := BruhatTits.localField_t2Space F

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]

variable (hn : LeviSubgroup.IsGeometricUnipotentRadical n)
  (h : IsSemidirectDecomposition
    ((SubgroupFunctor.range p).carrier (Over.mk (𝟙 _)))
    (parabolicLeviPointSubgroup p l)
    ((SubgroupFunctor.range (n ≫ p)).carrier (Over.mk (𝟙 _))))
  (hU : IsClosed (((SubgroupFunctor.range (n ≫ p)).carrier (Over.mk (𝟙 _))) :
    Set (rationalPoints G)))

variable [T2Space (rationalPoints G)]

include pres hn in
set_option maxHeartbeats 1600000 in
/-- The actual multiplicity bound for one regular square-integrable irreducible
representation of the literal Levi. Same argument as
`jacquetInductionHom_rank_le_one_of_statements`, with the self-intersection
pieces bounded by the criterion-free lemmas and the published inputs
discharged. -/
theorem jacquetInductionHom_rank_le_one_unconditional
    (hG : IsConnectedReductive G) (hr : Continuous h.projection)
    (π : SmoothRep.{0, u, uV} ℂ (parabolicLeviPointSubgroup p l)) (hirr : π.IsIrreducible) :
    let C := (parabolicSplitComponentPointHom pres).range
    let hC := parabolicSplitComponentPointHom_range_le_center pres
    letI : C.Normal := C.normal_of_le_center hC
    ∀ [MeasurableSpace (parabolicLeviPointSubgroup p l ⧸ C)]
      [BorelSpace (parabolicLeviPointSubgroup p l ⧸ C)]
      (qMeasure : Measure (parabolicLeviPointSubgroup p l ⧸ C)) [IsHaarMeasure qMeasure],
      IsSquareIntegrableModCentralSubgroup C hC π.representation qMeasure →
      IsNormalizerRegular π →
      Module.rank ℂ (((jacquetFunctor h hU).obj
        ((DynamicNormalization.leviTwistedInductionFunctor h hU).obj π)).representation.IntertwiningMap
          π.representation) ≤ 1 := by
  intro C hC _ _ qMeasure _ hsq hreg
  have : C.Normal := C.normal_of_le_center hC
  have := hG.smooth
  have hcompact := RepresentedParabolic.arbitraryParabolicQuotientCompact.{u}
  let hp := pres.isCompatible.parabolic
  let hl := pres.isCompatible.levi
  let ha := pres.isCompatible.splitComponent
  let hmul := parabolicRadical_isIso_subgroupMultiplication pres hG hn
  let e := parabolicLeviPointHomeomorph pres
  let σ := SmoothRep.pullback e π
  have hI := leviTwistedInduction_obj_isAdmissible pres hn h hU hcompact hG hr π hsq.1
  have hJI := representedJacquetInduction_isAdmissible pres hn h hU hG π hI
  have := RepresentedParabolic.leviPoints_locallyCompactSpace p l hp hl
  have := RepresentedParabolic.leviPoints_nonarchimedeanGroup p l hp hl
  have : IsTopologicalGroup (rationalPoints M) :=
    Topology.IsInducing.isTopologicalGroup e.toMulEquiv e.toHomeomorph.isInducing
  let : MeasurableSpace (rationalPoints M ⧸ Subgroup.center (rationalPoints M)) := borel _
  have : BorelSpace (rationalPoints M ⧸ Subgroup.center (rationalPoints M)) := ⟨rfl⟩
  let haarM : Measure (rationalPoints M ⧸ Subgroup.center (rationalPoints M)) := Measure.haar
  have hσsquare := isSquareIntegrableModCenter_pullback_of_modCentralSubgroup pres hG π
    qMeasure hsq haarM
  have hσtemp := RepresentedParabolic.squareIntegrableNormalizedTempered.{u, uV}
    F M hl.isConnectedReductive haarM σ hσsquare
  have hσirr : σ.IsIrreducible :=
    (isIrreducible_comp_continuousMulEquiv_iff π.representation e).mpr hirr
  have hσreg := isNormalizerRegular_leviPoints_pullback pres π hreg
  obtain ⟨m, c, z, hz, D, hglue⟩ :=
    RepresentedParabolic.representedGeometricLemma.{u, uV}
      F G hG P M U P M U p l n hp hl hn hmul p l n hp hl hn hmul
  have hJac := fun i => RepresentedParabolic.arbitraryParabolicJacquetAdmissibility.{u, uV}
    F M hl.isConnectedReductive (D i).P' (D i).M' (D i).N'
    (D i).p' (D i).l' (D i).r' (D i).hp' (D i).hl' (D i).hr' (D i).hmul' σ hσsquare.1
  refine (parabolicJacquetHom_rank_le_representedUnitary pres hG hn h hU π hI qMeasure
    hsq).trans ?_
  exact RepresentedParabolic.leviUnitaryJacquetInductionHomRank_le_one_of_doubleCosets
    p l n hp hl hn hmul p l n hp hl hn hmul ha c z hz D hglue σ hJI σ.representation
    (fun i => by
      obtain ⟨A', a', ha'⟩ :=
        (splitComponentStatement F (D i).M' (D i).hl'.isConnectedReductive).1
      exact (D i).selectedPieceHomLength_le_one_unconditional ha' σ hσtemp haarM hσsquare
        hcompact ha pres (hJac i) hσirr)
    (fun i hne => by
      obtain ⟨A', a', ha'⟩ :=
        (splitComponentStatement F (D i).M' (D i).hl'.isConnectedReductive).1
      exact (D i).mem_pointImage_parabolic_of_selectedPieceHomLength_ne_zero_unconditional ha' σ
        hσtemp haarM hσsquare hcompact ha pres (hJac i) hσirr hσreg hne)

end Actual

/-- **Waldspurger III.7.3**, Jacquet multiplicity form for the literal subgroup
model: `RegularSquareIntegrableJacquetMultiplicityStatement` holds. -/
theorem regularSquareIntegrableJacquetMultiplicity :
    RegularSquareIntegrableJacquetMultiplicityStatement.{u, uV} := by
  intro F _ _ _ _ G hG _ _ _ A M P U _ p l a n r hn Ppt Mpt Upt h hU _ hr C hC _ _ qMeasure _
    π hirr hsq hreg
  have := hG.isAffineHom
  exact jacquetInductionHom_rank_le_one_unconditional r hn h hU hG hr π hirr qMeasure hsq hreg

end Langlands.Plancherel
