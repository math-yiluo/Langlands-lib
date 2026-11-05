import Langlands.GroupScheme.Absolute.MaximalTorusCentralizerReduction
import Langlands.GroupScheme.Reductive.RootGenerationStatement
import Langlands.GroupScheme.Reductive.RootGenerationTorusContainment
import Langlands.GroupScheme.Reductive.RootTorusGeneration
import Langlands.GroupScheme.Torus.MaximalSplitComparison

/-! # Semisimple root generation from rank-one pairs and torus centralization -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

section Pointwise

variable {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    {T : CommGroupScheme (Spec (CommRingCat.of k))}
    (i : T.toGrp ⟶ G) [Mono i.hom.hom.left]
    (hG : IsSemisimple G) (hT : IsSplitTorus T.toGrp)
    (hi : IsClosedSubgroup i) (hE : RelativeRoot.HasOppositeFactorPairs i)
    (hself : torusCentralizer i = SubgroupFunctor.range i)
    {D : GroupScheme (Spec (CommRingCat.of k))} (d : D ⟶ G)
    (hd : IsClosedSubgroup d)
    (hroots : ∀ α ∈ relativeRoots i,
      RelativeRoot.subgroup i α ≤ SubgroupFunctor.range d)

include hG hT hi hE hself hd hroots in
/-- A root-containing closed subgroup is full, given actual opposite pairs
and all-test self-centralization for the split closed torus. -/
theorem IsSemisimple.range_eq_top_of_oppositeFactorPairs_of_selfCentralizing :
    SubgroupFunctor.range d = ⊤ := by
  let : Smooth G.X.hom := hG.isConnectedReductive.smooth
  let : ConnectedSpace G.X.left := hG.isConnectedReductive.connectedSpace
  exact range_eq_top_of_selfCentralizing_torus_and_rootSubgroups i hT hself d hd
    (hG.range_torus_le_of_oppositeFactorPairs i hT hi hE hd hroots) hroots

/-- The actual isomorphism from closed root generation under the two
explicit structural premises. -/
def semisimpleRootGenerationIso : D ≅ G := by
  let : IsClosedImmersion d.hom.hom.left := hd
  have hfull : (⊤ : SubgroupFunctor G).IsRepresentedBy d :=
    ⟨Over.mono_of_mono_left _,
      hG.range_eq_top_of_oppositeFactorPairs_of_selfCentralizing i hT hi hE hself d hd hroots⟩
  exact hfull.topIso

/-- The isomorphism retains the original closed inclusion as its forward map. -/
theorem semisimpleRootGenerationIso_hom :
    (semisimpleRootGenerationIso i hG hT hi hE hself d hd hroots).hom = d := by
  apply SubgroupFunctor.IsRepresentedBy.topIso_hom

end Pointwise

/-- The existing full rank-one factorization statement and algebraically
closed maximal-torus self-centralization imply the exact published
semisimple root-generation target. Both inputs remain premises. -/
def SemisimpleRootGenerationReductionStatement : Prop :=
  RootRankOneFactorizationStatement.{u} →
    AlgClosedMaximalTorusCentralizerStatement.{u} →
      SemisimpleRootGenerationStatement.{u}

/-- Apply the pointwise bridge to the chosen split maximal torus, extracting
opposite-pair existence from the supplied rank-one statement. -/
theorem semisimpleRootGenerationReduction :
    SemisimpleRootGenerationReductionStatement.{u} := by
  intro hfactor hcentral k _ _ G hG T i hi hmax D d hd hroots
  let : IsAffineHom G.X.hom := hG.isConnectedReductive.isAffineHom
  let : Mono i.hom.hom.left := hi.mono
  have hE : RelativeRoot.HasOppositeFactorPairs i := by
    intro α hα x hx hx1
    exact (hfactor k G hG.isConnectedReductive T i
      (hmax.isMaximalSplitTorus hi.1) α hα x hx hx1).1.exists
  exact hG.range_eq_top_of_oppositeFactorPairs_of_selfCentralizing i hi.1 hi.2 hE
    (hcentral k G hG.isConnectedReductive T i hmax) d hd hroots

end Langlands.GroupScheme
