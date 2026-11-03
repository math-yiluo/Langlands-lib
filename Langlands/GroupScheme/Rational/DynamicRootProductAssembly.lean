import Langlands.GroupScheme.Rational.ActionWeightSupport
import Langlands.GroupScheme.Rational.SemigroupTransport
import Langlands.GroupScheme.Rational.RootRayBlocks
import Langlands.GroupScheme.Rational.SplitUnipotentSolvable
import Langlands.GroupScheme.Dynamic.CentralizerReductiveTransport

/-! # Conditional assembly of the actual Dynamic ordered root product -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.RelativeRoot

/-- Conditional reduction to the structural source statements and the cyclic
comparison for actual reductive roots. -/
def DynamicRootOrderedProductFromSemigroups : Prop :=
  SemigroupRealizationStatement.{u} →
  SemigroupOrderedProductStatement.{u} →
  RelativeRootRayDecompositionStatement.{u} →
  DynamicSemigroupComparisonStatement.{u} →
  (∀ (k : Type u) [Field k]
      (G : GroupScheme (Spec (CommRingCat.of k))) (hG : IsConnectedReductive G)
      (S : CommGroupScheme (Spec (CommRingCat.of k))) (i : S.toGrp ⟶ G),
      IsMaximalSplitTorus i →
      letI := hG.isAffineHom
      ∀ a ∈ relativeRoots i,
        semigroupSubgroup (AutomorphicAction.conjugation i) (cyclicTail a 1) =
          subgroup i a) →
  DynamicRootOrderedProductStatement.{u}

/-- The conditional assembly retains the complete published conclusion.
All structural premises remain explicit. -/
theorem dynamicRootOrderedProduct_of_semigroupStatements :
    DynamicRootOrderedProductFromSemigroups.{u} := by
  intro hReal hProduct hRays hDynamic hCyclic k _ G hG S i hi
  let := hG.isAffineHom
  intro ν n a hinj ha
  let b := AutomorphicAction.conjugation i
  let A := positiveSemigroup ν
  obtain ⟨⟨U, jU, hjU, hjUc, hUs, hUc⟩, hStable, _, hUnip, _, _⟩ :=
    hReal k G hG.smooth inferInstance S hi.1.1 b A
  have hzero : (0 : characterLattice S) ∉ A := by
    change ¬ 0 < latticePairing S 0 ν
    simp
  obtain ⟨hUu, hUsp⟩ := hUnip U jU hjU hzero
  let : IsAffineHom U.X.hom := hjUc.isAffineHom
  let c := b.onRepresentedSubgroup jU hjU hStable
  have hequiv : ∀ (T : Over (Spec (CommRingCat.of k))) (s : T ⟶ S.X)
      (x : T ⟶ U.X), c.act s x ≫ jU.hom.hom = b.act s (x ≫ jU.hom.hom) :=
    fun _ s x => b.onRepresentedSubgroup_act_comp jU hjU hStable s x
  have htop : (⊤ : SubgroupFunctor U).map jU = semigroupSubgroup b A := by
    rw [SubgroupFunctor.map_top, hjU.2]
  have hsupport : actionWeightSupport c ⊤ = positiveRelativeRoots i ν := by
    rw [← actionWeightSupport_map jU hjU.1 c b hequiv, htop]
    exact actionWeightSupport_positiveSemigroup hReal hG.smooth hi.1.1 i ν
  obtain ⟨_, hdisj, hcover⟩ := hRays k G hG S i hi ν
  have hblocks := rootRayBlock_pairwise i ν a hinj ha hdisj
  have hcover' : (⋃ r, rootRayBlock i (a r)) = actionWeightSupport c ⊤ :=
    (iUnion_rootRayBlock i ν a ha hcover).trans hsupport.symm
  obtain ⟨H, jH, hH, hIso⟩ := hProduct k U hUs inferInstance hUc
    hUsp.isSolvableScheme S hi.1.1 c n (fun r => rootRayBlock i (a r))
      hcover' hblocks.1 hblocks.2
  have hroot (r : Fin n) : a r ∈ indivisiblePositiveRoots i ν :=
    ha ▸ Set.mem_range_self r
  have hsemigroup (r : Fin n) :
      ((semigroupSubgroup c (AddSubsemigroup.closure (rootRayBlock i (a r)))).map jU) =
        semigroupSubgroup b (cyclicTail (a r) 1) := by
    rw [closure_rootRayBlock i (hroot r).1.1]
    apply semigroupSubgroup_map_eq jU hjUc c b hequiv
    rw [hjU.2]
    exact semigroupSubgroup_mono b (cyclicTail_one_le_positiveSemigroup (hroot r).2)
  have hambient (r : Fin n) :
      (semigroupSubgroup b (cyclicTail (a r) 1)).IsRepresentedBy (jH r ≫ jU) := by
    rw [← hsemigroup r]
    exact (hH r).1.comp hjU
  have hfactor (r : Fin n) :
      (subgroup i (a r)).IsRepresentedBy (jH r ≫ jU) ∧
        IsClosedSubgroup (jH r ≫ jU) ∧ Smooth (H r).X.hom ∧
        ConnectedSpace (H r).X.left ∧ IsUnipotent (H r) ∧ IsSplitUnipotent (H r) := by
    have hcyclic := hCyclic k G hG S i hi (a r) (hroot r).1.1
    have hrep := hambient r
    obtain ⟨hHu, hHsp⟩ := (hReal k G hG.smooth inferInstance S hi.1.1 b
      (cyclicTail (a r) 1)).2.2.2.1 (H r) (jH r ≫ jU) hrep (by
        intro hz
        have hp := cyclicTail_one_le_positiveSemigroup (hroot r).2 hz
        exact hzero hp)
    exact ⟨hcyclic ▸ hrep, (hH r).2.1.comp hjUc, (hH r).2.2.1,
      (hH r).2.2.2, hHu, hHsp⟩
  let := hIso
  refine ⟨U, jU, H, (fun r => jH r ≫ jU), asIso (orderedMultiplication jH),
    ?_, hjUc, hUs, hUc, hUu, hUsp, hfactor, ?_⟩
  · rw [(hDynamic k G hG.smooth inferInstance hG.connectedSpace S hi.1.1 i ν).2.2]
    exact hjU
  · exact orderedMultiplication_comp jH jU

end Langlands.GroupScheme.RelativeRoot
