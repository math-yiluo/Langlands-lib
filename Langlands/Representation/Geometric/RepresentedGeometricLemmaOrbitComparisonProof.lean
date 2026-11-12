import Langlands.Representation.Geometric.RepresentedGeometricLemmaOrbitComparisonStatement
import Langlands.Representation.Geometric.RepresentedGeometricLemmaCompactNaturality
import Langlands.Representation.Geometric.RepresentedGeometricLemmaTargetInduction
import Langlands.Representation.Geometric.RepresentedParabolicKernelCoinvariants
import Langlands.Representation.Geometric.RepresentedGeometricLemmaDynamicRealization
import Langlands.Representation.Exponents.ArbitraryParabolicQuotientCompactProof
import Langlands.GroupScheme.Absolute.ParabolicDynamicProof
import Langlands.GroupScheme.Rational.RelativeRootSystemProof
import Langlands.GroupScheme.Rational.CentralSplitTorusCharacterProof
import Langlands.GroupScheme.Rational.SplitTorusFactorization

/-! # The local normalized orbit comparison for represented parabolics -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

namespace GeometricLemmaIntersectionDatum

variable {k : Type u} [Field k] [TopologicalSpace k]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  {P M N Q L U : GroupScheme (Spec (CommRingCat.of k))}
  {p : P ⟶ G} {l : M ⟶ P} {r : N ⟶ P}
  {hp : IsParabolicSubgroup p} {hr : LeviSubgroup.IsGeometricUnipotentRadical r}
  {hl : IsRationalLeviSubgroup l} {hmul : IsIso (subgroupMultiplication l r)}
  {q : Q ⟶ G} {lQ : L ⟶ Q} {rQ : U ⟶ Q}
  {hq : IsParabolicSubgroup q} {hrQ : LeviSubgroup.IsGeometricUnipotentRadical rQ}
  {hlQ : IsRationalLeviSubgroup lQ} {hmulQ : IsIso (subgroupMultiplication lQ rQ)}
  {z : rationalPoints G}

omit [IsAffineHom G.X.hom] in
/-- Restriction of rational characters from the target common Levi of an intersection datum
to its common maximal split torus is injective. -/
theorem characterRestrict_targetCommonTorusHom_injective
    (D : GeometricLemmaIntersectionDatum p l r hp hr hl hmul q lQ rQ hq hrQ hlQ hmulQ z) :
    Function.Injective (characterRestrict D.targetCommonTorusHom) := by
  have hM : IsConnectedReductive D.L' := D.hlQ'.isConnectedReductive
  have : IsAffineHom D.L'.X.hom := hM.isAffineHom
  have hj : IsClosedSubgroup (D.lQ' ≫ D.q' ≫ lQ ≫ q) :=
    D.hlQ'.isClosedSubgroup.comp (D.hq'.isClosedSubgroup.comp
      (hlQ.isClosedSubgroup.comp hq.isClosedSubgroup))
  have ht : IsMaximalSplitTorus (D.targetCommonTorusHom ≫ D.lQ' ≫ D.q' ≫ lQ ≫ q) :=
    D.targetCommonTorus_isMaximalSplitTorus_ambient
  rw [injective_iff_map_eq_zero]
  intro χ hχ
  by_contra hne
  obtain ⟨A, a, ha, hχa⟩ := centralSplitTorusCharacter k D.L' hM χ hne
  obtain ⟨g, hg⟩ := ha.exists_factor_of_isMaximalSplitTorus hj ht
  apply hχa
  rw [← hg, characterRestrict_comp, AddMonoidHom.comp_apply, hχ, map_zero]

end GeometricLemmaIntersectionDatum

/-- **Local normalized orbit comparison** (Renard VI.5.1, local step). For every represented
intersection datum at `z`, compact stabilizer induction of the normalized inducing
representation followed by normalized target-radical coinvariants is the datum's
Jacquet–conjugation–induction piece. -/
theorem representedGeometricLemmaOrbitComparison :
    RepresentedGeometricLemmaOrbitComparisonStatement.{u, v} := by
  intro k _ _ _ _ _ G hG
  have := hG.isAffineHom
  have := hG.smooth
  let : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
  intro _ _ P M N Q L U p l r hp hl hr hmul q lQ rQ hq hlQ hrQ hmulQ z D
  let := leviPointTopology l hl
  let := leviPointTopology lQ hlQ
  have := hlQ.isConnectedReductive.isAffineHom
  have : LocallyCompactSpace (rationalPoints L) := leviPoints_locallyCompactSpace q lQ hq hlQ
  have : NonarchimedeanGroup (rationalPoints L) := leviPoints_nonarchimedeanGroup q lQ hq hlQ
  have hcompact : CompactSpace (Induction.LeftQuotient (pointImage D.q')) :=
    arbitraryParabolicQuotientCompact k L hlQ.isConnectedReductive D.Q' D.q' D.hq'
  let R := D.dynamicRealizationOfParabolicDynamic parabolicDynamic hG
  have hroot := relativeRootSystem k G hG D.torus _
    D.targetCommonTorus_isMaximalSplitTorus_ambient
  exact ⟨orbitParabolicProjectionKernelIso p l r hp hr hl hmul q lQ rQ hq hrQ hlQ hmulQ z ≪≫
    R.orbitProjectionKernelCompactIso ≪≫
    GeometricLemmaIntersectionDatum.DynamicRealization.targetNormalizedCompactIso D R hcompact
      hroot D.characterRestrict_targetCommonTorusHom_injective⟩

end Langlands.Aubert.General.RepresentedParabolic
