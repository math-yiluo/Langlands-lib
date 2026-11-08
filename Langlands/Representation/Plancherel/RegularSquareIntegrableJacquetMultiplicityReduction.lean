import Langlands.Representation.Plancherel.RegularJacquetMultiplicityStatement
import Langlands.Representation.Plancherel.ParabolicRepresentedComparison
import Langlands.Representation.Plancherel.ParabolicSquareIntegrableModCenter
import Langlands.Representation.Exponents.SelfUnitaryPieceMultiplicity
import Langlands.Representation.Exponents.LeviUnitaryGluedHomBound
import Langlands.Representation.Exponents.SquareIntegrableNormalizedTemperedStatement
import Langlands.Representation.Exponents.ArbitraryParabolicJacquetAdmissibilityStatement
import Langlands.Representation.Aubert.General.RationalInductionDualityReduction
import Langlands.GroupScheme.Rational.SplitComponentProof

/-! # A reduction of actual regular square-integrable Jacquet multiplicity -/

noncomputable section

open CategoryTheory AlgebraicGeometry MeasureTheory MeasureTheory.Measure
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.Plancherel

universe u uV

open Aubert.General

section Regularity

variable {H : Type u} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]

/-- Normalizer regularity depends only on the isomorphism class. -/
theorem isNormalizerRegular_of_iso {M : Subgroup H} {σ σ' : SmoothRep.{0, u, uV} ℂ M}
    (E : σ ≅ σ') (hσ : IsNormalizerRegular σ) : IsNormalizerRegular σ' := by
  rintro g hg ⟨F'⟩
  apply hσ g hg
  exact ⟨SmoothRep.equivOfIso
    ((SmoothRep.pullbackFunctor (normalizerConjugation g)).mapIso E ≪≫ SmoothRep.mkIso F' ≪≫
      E.symm)⟩

/-- Normalizer regularity is unchanged by identifying equal subgroups. -/
theorem isNormalizerRegular_pullback_subgroupCongr {M M' : Subgroup H} (eM : M = M')
    (σ : SmoothRep.{0, u, uV} ℂ M) (hσ : IsNormalizerRegular σ) :
    IsNormalizerRegular
      (SmoothRep.pullback (RepresentedParabolic.subgroupCongrContinuous eM).symm σ) := by
  subst eM
  exact isNormalizerRegular_of_iso (pullbackSubgroupCongrReflIso σ).symm hσ

end Regularity

section Actual

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {A : CommGroupScheme (Spec (CommRingCat.of F))}
  {G M P U : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine M.X.left]
  {p : P ⟶ G} {l : M ⟶ P} {a : A.toGrp ⟶ M} {n : U ⟶ P}
  (pres : ParabolicRootPresentation p l a)

local instance regularReductionAmbientAffine : IsAffine G.X.left :=
  isAffine_of_isAffineHom G.X.hom
local instance regularReductionAmbientPointTopology :
    TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
local instance regularReductionLeviPointTopology :
    TopologicalSpace (rationalPoints M) := rationalPointTopology F M.X
local instance regularReductionFieldT2 : T2Space F := BruhatTits.localField_t2Space F

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]

include pres in
omit [ValuativeRel F] [IsNonarchimedeanLocalField F]
  [LocallyCompactSpace (rationalPoints G)] in
/-- Normalizer regularity of a representation of the literal Levi passes to its
pullback to the represented Levi point image. -/
theorem isNormalizerRegular_leviPoints_pullback
    (π : SmoothRep.{0, u, uV} ℂ (parabolicLeviPointSubgroup p l))
    (hπ : IsNormalizerRegular π) :
    IsNormalizerRegular (SmoothRep.pullback
      (RepresentedParabolic.leviPointsEquiv p l pres.isCompatible.parabolic
        pres.isCompatible.levi).symm
      (SmoothRep.pullback (parabolicLeviPointHomeomorph pres) π)) := by
  let e := parabolicLeviPointHomeomorph pres
  let e' := RepresentedParabolic.leviPointsEquiv p l pres.isCompatible.parabolic
    pres.isCompatible.levi
  have eM : parabolicLeviPointSubgroup p l = RepresentedParabolic.pointImage (l ≫ p) :=
    (RepresentedParabolic.pointImage_eq_range_carrier (l ≫ p)).symm
  let c := RepresentedParabolic.subgroupCongrContinuous eM
  have hce (x : RepresentedParabolic.pointImage (l ≫ p)) : e (e'.symm x) = c.symm x := by
    apply Subtype.ext
    change (rationalPoints.map (l ≫ p) (e'.symm x)) = (x : rationalPoints G)
    exact congrArg Subtype.val (e'.apply_symm_apply x)
  exact isNormalizerRegular_of_iso (pullbackPullbackIso e'.symm e c.symm hce π).symm
    (isNormalizerRegular_pullback_subgroupCongr eM π hπ)

variable (hn : LeviSubgroup.IsGeometricUnipotentRadical n)
  (h : IsSemidirectDecomposition
    ((SubgroupFunctor.range p).carrier (Over.mk (𝟙 _)))
    (parabolicLeviPointSubgroup p l)
    ((SubgroupFunctor.range (n ≫ p)).carrier (Over.mk (𝟙 _))))
  (hU : IsClosed (((SubgroupFunctor.range (n ≫ p)).carrier (Over.mk (𝟙 _))) :
    Set (rationalPoints G)))

include pres hn in
omit [IsAffine M.X.left] in
/-- With compact actual parabolic quotient, the literal Levi-twisted induction of
an admissible representation is admissible. -/
theorem leviTwistedInduction_obj_isAdmissible
    (hcompact : RepresentedParabolic.ArbitraryParabolicQuotientCompactStatement.{u})
    (hG : IsConnectedReductive G) (hr : Continuous h.projection)
    (π : SmoothRep.{0, u, uV} ℂ (parabolicLeviPointSubgroup p l)) (hπ : π.IsAdmissible) :
    ((DynamicNormalization.leviTwistedInductionFunctor h hU).obj π).IsAdmissible := by
  have hδ := parabolicRadical_isUnimodular F G hG A M P U p l a n pres hn hU
  have : CompactSpace (Induction.LeftQuotient
      ((SubgroupFunctor.range p).carrier (Over.mk (𝟙 (Spec (CommRingCat.of F)))))) := by
    rw [← RepresentedParabolic.pointImage_eq_range_carrier]
    exact hcompact F G hG P p pres.isCompatible.parabolic
  exact isAdmissible_of_equiv
    (SmoothRep.equivOfIso ((DynamicNormalization.normalizedInductionLeviTwistIso h hU hδ).app π))
    (normalizedInductionFunctor_obj_isAdmissible h hU hr π hπ)

include pres hn in
/-- Admissibility of the literal induction gives admissibility of the
represented Jacquet module of the represented induction of the pulled-back
inducing representation. -/
theorem representedJacquetInduction_isAdmissible (hG : IsConnectedReductive G)
    (π : SmoothRep.{0, u, uV} ℂ (parabolicLeviPointSubgroup p l))
    (hI : ((DynamicNormalization.leviTwistedInductionFunctor h hU).obj π).IsAdmissible) :
    IsAdmissible ((RepresentedParabolic.leviJacquetInductionFunctor p l n
      pres.isCompatible.parabolic hn pres.isCompatible.levi
      (parabolicRadical_isIso_subgroupMultiplication pres hG hn)
      p l n pres.isCompatible.parabolic hn pres.isCompatible.levi
      (parabolicRadical_isIso_subgroupMultiplication pres hG hn)).obj
        (SmoothRep.pullback (parabolicLeviPointHomeomorph pres) π)).ρ := by
  have hX := parabolicJacquet_obj_isAdmissible pres hn h hU hG _ hI
  exact isAdmissible_of_equiv
    (SmoothRep.equivOfIso (parabolicRepresentedJacquetInductionIso pres hG hn h hU π))
    (isAdmissible_comp_continuousMulEquiv _ (parabolicLeviPointHomeomorph pres) hX)

variable [T2Space (rationalPoints G)]

include pres hn in
set_option maxHeartbeats 1600000 in
/-- The actual multiplicity bound for one regular square-integrable irreducible
representation of the literal Levi, from the represented geometric lemma, the
Renard VII.2.4 criterion, quotient compactness, temperedness of
square-integrable representations and Jacquet admissibility. -/
theorem jacquetInductionHom_rank_le_one_of_statements
    (hgeom : RepresentedParabolic.RepresentedGeometricLemmaStatement.{u, uV})
    (hcrit : RepresentedParabolic.TemperedSquareIntegrableUnitaryPartStatement.{u, uV})
    (hcompact : RepresentedParabolic.ArbitraryParabolicQuotientCompactStatement.{u})
    (htemp : RepresentedParabolic.SquareIntegrableNormalizedTemperedStatement.{u, uV})
    (hjac : RepresentedParabolic.ArbitraryParabolicJacquetAdmissibilityStatement.{u, uV})
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
  have hσtemp := htemp F M hl.isConnectedReductive haarM σ hσsquare
  have hσirr : σ.IsIrreducible :=
    (isIrreducible_comp_continuousMulEquiv_iff π.representation e).mpr hirr
  have hσreg := isNormalizerRegular_leviPoints_pullback pres π hreg
  obtain ⟨m, c, z, hz, D, hglue⟩ :=
    hgeom F G hG P M U P M U p l n hp hl hn hmul p l n hp hl hn hmul
  have hJac := fun i => hjac F M hl.isConnectedReductive (D i).P' (D i).M' (D i).N'
    (D i).p' (D i).l' (D i).r' (D i).hp' (D i).hl' (D i).hr' (D i).hmul' σ hσsquare.1
  refine (parabolicJacquetHom_rank_le_representedUnitary pres hG hn h hU π hI qMeasure
    hsq).trans ?_
  exact RepresentedParabolic.leviUnitaryJacquetInductionHomRank_le_one_of_doubleCosets
    p l n hp hl hn hmul p l n hp hl hn hmul ha c z hz D hglue σ hJI σ.representation
    (fun i => by
      obtain ⟨A', a', ha'⟩ :=
        (splitComponentStatement F (D i).M' (D i).hl'.isConnectedReductive).1
      exact (D i).selectedPieceHomLength_le_one ha' σ hσtemp haarM hσsquare hcrit hcompact
        ha pres (hJac i) hσirr)
    (fun i hne => by
      obtain ⟨A', a', ha'⟩ :=
        (splitComponentStatement F (D i).M' (D i).hl'.isConnectedReductive).1
      exact (D i).mem_pointImage_parabolic_of_selectedPieceHomLength_ne_zero ha' σ hσtemp
        haarM hσsquare hcrit hcompact ha pres (hJac i) hσirr hσreg hne)

end Actual

/-- The reduction: Waldspurger III.7.3, in its Jacquet multiplicity form for the
literal subgroup model, follows from the represented geometric lemma, the
Renard VII.2.4 square-integrability criterion, compactness of the actual
parabolic quotients, temperedness of square-integrable representations and
Jacquet admissibility. -/
def RegularSquareIntegrableJacquetMultiplicityReductionStatement : Prop :=
  RepresentedParabolic.RepresentedGeometricLemmaStatement.{u, uV} →
    RepresentedParabolic.TemperedSquareIntegrableUnitaryPartStatement.{u, uV} →
      RepresentedParabolic.ArbitraryParabolicQuotientCompactStatement.{u} →
        RepresentedParabolic.SquareIntegrableNormalizedTemperedStatement.{u, uV} →
          RepresentedParabolic.ArbitraryParabolicJacquetAdmissibilityStatement.{u, uV} →
            RegularSquareIntegrableJacquetMultiplicityStatement.{u, uV}

/-- The reduction holds. -/
theorem regularSquareIntegrableJacquetMultiplicity_of_statements :
    RegularSquareIntegrableJacquetMultiplicityReductionStatement.{u, uV} := by
  intro hgeom hcrit hcompact htemp hjac F _ _ _ _ G hG _ _ _ A M P U _ p l a n r hn
    Ppt Mpt Upt h hU _ hr C hC _ _ qMeasure _ π hirr hsq hreg
  have := hG.isAffineHom
  exact jacquetInductionHom_rank_le_one_of_statements r hn h hU hgeom hcrit hcompact htemp
    hjac hG hr π hirr qMeasure hsq hreg

end Langlands.Plancherel
