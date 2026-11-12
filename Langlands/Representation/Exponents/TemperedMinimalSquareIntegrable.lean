import Langlands.Representation.Exponents.TemperedMinimalUnitaryJacquet
import Langlands.Representation.Exponents.TemperedUnitaryQuotientStructure
import Langlands.Representation.Exponents.TemperedJacquetInductionEmbedding
import Langlands.Representation.Exponents.NestedLeviJacquetExponents
import Langlands.Representation.Exponents.NormalizedTemperedQuotient
import Langlands.Representation.Exponents.UnitaryJacquetPartTemperedProof
import Langlands.Representation.Exponents.UnitaryJacquetExponents
import Langlands.Representation.Exponents.TemperedSquareIntegrableUnitaryPartStatement
import Langlands.Representation.Exponents.ArbitraryParabolicQuotientCompactStatement
import Langlands.Representation.Exponents.LeviCuspidalEmbeddingSteps
import Langlands.GroupScheme.Rational.ParabolicLeviIntersectionReduction

/-! # Square-integrability of the quotient chosen at a minimal unitary support

Renard VII.2.6, first proof paragraph (printed p.231 / PDF p.237): at an actual
parabolic minimal among those with nonzero unitary Jacquet part, every irreducible
quotient of the unitary Jacquet module has vanishing unitary Jacquet parts along all
proper parabolics of the Levi. With the VII.2.4 square-integrability criterion this
makes the quotient square-integrable modulo the center, and with compactness of the
parabolic quotient it gives the embedding of a tempered irreducible representation
into an induced discrete series.
-/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

variable {k : Type u} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k] [T2Space k]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

local instance minimalSquareIntegrableAmbientTopology : TopologicalSpace (rationalPoints G) :=
  RationalPointFamily.pointTopology

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
  {hG : IsConnectedReductive G} {π : SmoothRep.{0, u, v} ℂ (rationalPoints G)}

namespace UnitaryJacquetSupportData

/-- At a minimal unitary support of a tempered representation, an irreducible
quotient of the unitary Jacquet module has zero unitary Jacquet part along every
proper actual parabolic of the Levi. -/
theorem IsMinimal.unitaryJacquetPart_quotient_eq_bot
    (hπ : IsNormalizedExponentTempered hG π) {D : UnitaryJacquetSupportData π}
    (hD : D.IsMinimal)
    (Q : UnitaryJacquetIrreducibleQuotientData D.p D.l D.r D.hp D.hl D.hr D.hmul D.ha π)
    {PL N NL : GroupScheme (Spec (CommRingCat.of k))}
    (pL : PL ⟶ D.M) (mL : N ⟶ PL) (nL : NL ⟶ PL)
    (hpL : IsParabolicSubgroup pL) (hmL : IsRationalLeviSubgroup mL)
    (hnL : LeviSubgroup.IsGeometricUnipotentRadical nL)
    (hmulL : IsIso (subgroupMultiplication mL nL))
    {B : CommGroupScheme (Spec (CommRingCat.of k))} {b : B.toGrp ⟶ N}
    (hb : IsSplitComponent b) (hproper : ¬ IsIso pL) :
    haveI := D.hl.isConnectedReductive.isAffineHom
    letI : TopologicalSpace (rationalPoints D.M) := leviPointTopology D.l D.hl
    haveI : LocallyCompactSpace (rationalPoints D.M) :=
      leviPoints_locallyCompactSpace D.p D.l D.hp D.hl
    haveI : NonarchimedeanGroup (rationalPoints D.M) :=
      leviPoints_nonarchimedeanGroup D.p D.l D.hp D.hl
    unitaryJacquetPart pL mL nL hpL hmL hnL hmulL hb Q.quotient = ⊥ := by
  have hMred := D.hl.isConnectedReductive
  have := hMred.isAffineHom
  let : TopologicalSpace (rationalPoints D.M) := leviPointTopology D.l D.hl
  have : LocallyCompactSpace (rationalPoints D.M) :=
    leviPoints_locallyCompactSpace D.p D.l D.hp D.hl
  have : NonarchimedeanGroup (rationalPoints D.M) :=
    leviPoints_nonarchimedeanGroup D.p D.l D.hp D.hl
  have hσ₀ : IsNormalizedExponentTempered hMred
      (leviUnitaryJacquetModule D.p D.l D.r D.hp D.hl D.hr D.hmul D.ha π) :=
    (unitaryJacquetPartTempered k G hG D.P D.M D.U D.A D.p D.l D.r D.a
      D.hp D.hl D.hr D.hmul D.ha π hπ).2
  have hJ := hσ₀.isAdmissible_jacquetFunctor_obj pL mL nL hpL hmL hnL hmulL hb
  apply unitaryJacquetPart_eq_bot_of_surjective_intertwining nL hpL hmL hnL hmulL hb hJ
    (SmoothRep.hom Q.quotientMap) Q.surjective
  rw [unitaryJacquetPart_eq_bot_iff]
  intro χ hχ h0
  obtain ⟨R, W, pR, nR, rR, hpR, hnR, hrR, hmulR, hM, hPQ, hPL⟩ :=
    leviParabolicExtension k G hG D.P D.M D.U D.p D.l D.r D.hp D.hl D.hr D.hmul
      PL N NL pL mL nL hpL hmL hnL hmulL
  have hPQ' : pointImage pR ≤ pointImage D.p := hPQ _
  have hPL' : pointImage (pL ≫ D.l ≫ D.p) = pointImage (D.l ≫ D.p) ⊓ pointImage pR :=
    congrArg (fun F : SubgroupFunctor G =>
      F.carrier (Over.mk (𝟙 (Spec (CommRingCat.of k))))) hPL
  have hRχ := isNormalizedJacquetExponent_of_nestedUnitary hG pR nR rR hpR hnR hrR hmulR
    D.p D.l D.r D.hp D.hl D.hr D.hmul pL mL nL hpL hmL hnL hmulL hPQ' hM.symm hPL'
    D.ha π hb χ hχ
  have hU : unitaryJacquetPart pR nR rR hpR hnR hrR hmulR hb π ≠ ⊥ := fun h =>
    (unitaryJacquetPart_eq_bot_iff pR nR rR hpR hnR hrR hmulR hb π).mp h χ hRχ h0
  have hne : Nontrivial
      (SmoothRep.subrepresentation ((jacquetFunctor pR nR rR hpR hrR hnR hmulR).obj π)
        (unitaryJacquetPart pR nR rR hpR hnR hrR hmulR hb π)) := by
    by_contra hnt
    rw [not_nontrivial_iff_subsingleton] at hnt
    apply hU
    refine le_antisymm (fun x hx => ?_) bot_le
    have hx0 : (⟨x, hx⟩ : (unitaryJacquetPart pR nR rR hpR hnR hrR hmulR hb π).toSubmodule) =
        0 := @Subsingleton.elim _ hnt _ _
    exact (Submodule.mem_bot ℂ).mpr (congrArg Subtype.val hx0)
  let E : UnitaryJacquetSupportData π :=
    { P := R, M := N, U := W, p := pR, l := nR, r := rR
      hp := hpR, hl := hnR, hr := hrR, hmul := hmulR
      A := B, a := b, ha := hb, nontrivial_unitaryPart := hne }
  have heq : SubgroupFunctor.range pR = SubgroupFunctor.range D.p := hD E hPQ
  apply hproper
  apply IsClosedSubgroup.isIso_of_range_le_range_comp hpL.isClosedSubgroup
    (D.hl.isClosedSubgroup.comp D.hp.isClosedSubgroup)
  rw [hPL, heq, SubgroupFunctor.le_def]
  intro T x hx
  exact ⟨hx, (RepresentedParabolicLeviIntersection.range_comp_le D.l D.p) T hx⟩

/-- Conditionally on the VII.2.4 square-integrability criterion, an irreducible
quotient of the unitary Jacquet module at a minimal unitary support is
square-integrable modulo the center for every Haar measure. -/
theorem IsMinimal.isSquareIntegrableModCenter_quotient
    (hSI : TemperedSquareIntegrableUnitaryPartStatement.{u, v})
    (hπ : IsNormalizedExponentTempered hG π) {D : UnitaryJacquetSupportData π}
    (hD : D.IsMinimal)
    (Q : UnitaryJacquetIrreducibleQuotientData D.p D.l D.r D.hp D.hl D.hr D.hmul D.ha π) :
    haveI := D.hl.isConnectedReductive.isAffineHom
    letI : TopologicalSpace (rationalPoints D.M) := leviPointTopology D.l D.hl
    haveI : LocallyCompactSpace (rationalPoints D.M) :=
      leviPoints_locallyCompactSpace D.p D.l D.hp D.hl
    haveI : NonarchimedeanGroup (rationalPoints D.M) :=
      leviPoints_nonarchimedeanGroup D.p D.l D.hp D.hl
    ∀ [MeasurableSpace (rationalPoints D.M ⧸ Subgroup.center (rationalPoints D.M))]
      [BorelSpace (rationalPoints D.M ⧸ Subgroup.center (rationalPoints D.M))]
      (haar : MeasureTheory.Measure
        (rationalPoints D.M ⧸ Subgroup.center (rationalPoints D.M)))
      [haar.IsHaarMeasure],
      IsSquareIntegrableModCenter Q.quotient.representation haar := by
  have hMred := D.hl.isConnectedReductive
  have := hMred.isAffineHom
  let : TopologicalSpace (rationalPoints D.M) := leviPointTopology D.l D.hl
  have : LocallyCompactSpace (rationalPoints D.M) :=
    leviPoints_locallyCompactSpace D.p D.l D.hp D.hl
  have : NonarchimedeanGroup (rationalPoints D.M) :=
    leviPoints_nonarchimedeanGroup D.p D.l D.hp D.hl
  intro _ _ haar _
  have hσ₀ : IsNormalizedExponentTempered hMred
      (leviUnitaryJacquetModule D.p D.l D.r D.hp D.hl D.hr D.hmul D.ha π) :=
    (unitaryJacquetPartTempered k G hG D.P D.M D.U D.A D.p D.l D.r D.a
      D.hp D.hl D.hr D.hmul D.ha π hπ).2
  have hσ : IsNormalizedExponentTempered hMred Q.quotient :=
    hσ₀.of_surjective_intertwining (SmoothRep.hom Q.quotientMap) Q.surjective
  have hω := (Q.centralCharacter_spec D.p D.l D.r D.hp D.hl D.hr D.hmul D.ha hπ).2
  refine (hSI k D.M hMred haar Q.quotient
    (Q.centralCharacter D.p D.l D.r D.hp D.hl D.hr D.hmul D.ha hπ) hσ hω).mpr ?_
  intro PL N NL B pL mL nL b hpL hmL hnL hmulL hb hproper
  exact hD.unitaryJacquetPart_quotient_eq_bot hπ Q pL mL nL hpL hmL hnL hmulL hb hproper

end UnitaryJacquetSupportData

/-- Renard VII.2.6, necessity, conditionally on compactness of every actual
parabolic quotient and on the VII.2.4 square-integrability criterion: an
irreducible tempered representation embeds into the normalized induction of an
irreducible representation of a Levi that is square-integrable modulo the center
for every Haar measure. -/
theorem IsNormalizedExponentTempered.exists_squareIntegrable_induction_embedding
    (hCompact : ArbitraryParabolicQuotientCompactStatement.{u})
    (hSI : TemperedSquareIntegrableUnitaryPartStatement.{u, v})
    (hπ : IsNormalizedExponentTempered hG π) (hirr : π.IsIrreducible) :
    ∃ (P M U : GroupScheme (Spec (CommRingCat.of k)))
      (p : P ⟶ G) (l : M ⟶ P) (r : U ⟶ P)
      (hp : IsParabolicSubgroup p) (hl : IsRationalLeviSubgroup l)
      (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
      (hmul : IsIso (subgroupMultiplication l r)),
      haveI := hl.isConnectedReductive.isAffineHom
      letI : TopologicalSpace (rationalPoints M) := leviPointTopology l hl
      haveI : LocallyCompactSpace (rationalPoints M) :=
        leviPoints_locallyCompactSpace p l hp hl
      haveI : NonarchimedeanGroup (rationalPoints M) :=
        leviPoints_nonarchimedeanGroup p l hp hl
      ∃ σ : SmoothRep.{0, u, v} ℂ (rationalPoints M),
        σ.IsIrreducible ∧
          (∀ [MeasurableSpace (rationalPoints M ⧸ Subgroup.center (rationalPoints M))]
            [BorelSpace (rationalPoints M ⧸ Subgroup.center (rationalPoints M))]
            (haar : MeasureTheory.Measure
              (rationalPoints M ⧸ Subgroup.center (rationalPoints M)))
            [haar.IsHaarMeasure],
            IsSquareIntegrableModCenter σ.representation haar) ∧
          ∃ f : π.representation.IntertwiningMap
              ((leviInductionFunctor p l r hp hr hl hmul).obj σ).representation,
            Function.Injective f := by
  have : π.representation.IsIrreducible := hirr
  have : Nontrivial π :=
    IsSimpleModule.nontrivial (MonoidAlgebra ℂ (rationalPoints G)) π.representation.asModule
  let D := minimalUnitaryJacquetSupport hπ
  have hD : D.IsMinimal := minimalUnitaryJacquetSupport_isMinimal hπ
  have : CompactSpace (Induction.LeftQuotient (pointImage D.p)) :=
    hCompact k G hG D.P D.p D.hp
  let Q := unitaryJacquetIrreducibleQuotient D.p D.l D.r D.hp D.hl D.hr D.hmul D.ha π hirr
    (hπ.unitaryJacquetPart_isCompl D.p D.l D.r D.hp D.hl D.hr D.hmul D.ha)
    D.nontrivial_unitaryPart
  have := D.hl.isConnectedReductive.isAffineHom
  let : TopologicalSpace (rationalPoints D.M) := leviPointTopology D.l D.hl
  have : LocallyCompactSpace (rationalPoints D.M) :=
    leviPoints_locallyCompactSpace D.p D.l D.hp D.hl
  have : NonarchimedeanGroup (rationalPoints D.M) :=
    leviPoints_nonarchimedeanGroup D.p D.l D.hp D.hl
  exact ⟨D.P, D.M, D.U, D.p, D.l, D.r, D.hp, D.hl, D.hr, D.hmul, Q.quotient, Q.irreducible,
    hD.isSquareIntegrableModCenter_quotient hSI hπ Q,
    temperedUnitaryJacquetQuotientInductionMap D.p D.l D.r D.hp D.hl D.hr D.hmul D.ha hπ Q,
    temperedUnitaryJacquetQuotientInductionMap_injective D.p D.l D.r D.hp D.hl D.hr D.hmul
      D.ha hπ hirr Q⟩

end Langlands.Aubert.General.RepresentedParabolic
