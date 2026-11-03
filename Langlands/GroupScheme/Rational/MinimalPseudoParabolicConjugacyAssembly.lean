import Langlands.GroupScheme.PseudoParabolicStructureStatement
import Langlands.GroupScheme.Reductive.SplitUnipotentRadicalExistenceStatement
import Langlands.GroupScheme.SplitSolvableIntoPseudoParabolicStatement
import Langlands.GroupScheme.Rational.PseudoParabolicSplitSolvableEnvelopeStatement
import Langlands.GroupScheme.Rational.PseudoParabolicMaximalSplitTorusStructureStatement
import Langlands.GroupScheme.Rational.MinimalPseudoParabolicConjugacyStatement
import Langlands.GroupScheme.Rational.MinimalPseudoParabolicRangeReduction
import Langlands.GroupScheme.Rational.PseudoParabolicAmbientTransport
import Langlands.GroupScheme.Rational.MaximalSplitTorusExtension
import Langlands.GroupScheme.Rational.MaximalSplitTorusSubgroup
import Langlands.GroupScheme.Torus.ExistenceProof

/-! # Assembly of minimal pseudo-parabolic conjugacy from structural inputs -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

set_option maxHeartbeats 800000

/-- Extend the trivial split torus to obtain an actual maximal split torus. -/
theorem exists_maximalSplitTorus {k : Type u} [Field k]
    (G : GroupScheme (Spec (CommRingCat.of k)))
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom] :
    ∃ (T : CommGroupScheme (Spec (CommRingCat.of k))) (s : T.toGrp ⟶ G),
      IsMaximalSplitTorus s := by
  obtain ⟨T, s, hs, _⟩ := exists_maximalSplitTorus_extension G
    (TorusExistence.trivialTorusHom G)
    ⟨isSplitTorus_splitTorus PEmpty, TorusExistence.isClosedSubgroup_trivialTorusHom G⟩
  exact ⟨T, s, hs⟩

/-- The C.2.5 containment argument, with all five structural inputs explicit.
This theorem does not discharge any of those inputs. -/
theorem minimalPseudoParabolicConjugacy_of_structure
    (hgeometry : PseudoParabolicSubgroupStructureStatement.{u})
    (hradical : SplitUnipotentRadicalExistenceStatement.{u})
    (henvelope : PseudoParabolicSplitSolvableEnvelopeStatement.{u})
    (hcontainment : SplitSolvableIntoPseudoParabolicStatement.{u})
    (hstructure : PseudoParabolicMaximalSplitTorusStructureStatement.{u}) :
    MinimalPseudoParabolicConjugacyStatement.{u} := by
  intro k _ G hGsm hGconn hGaff P Q i j hi hj
  let : Smooth G.X.hom := hGsm
  let : ConnectedSpace G.X.left := hGconn
  let : IsAffineHom G.X.hom := hGaff
  obtain ⟨hPsm, hPconn, hPaff⟩ := hgeometry k G P i hi.1
  let : Smooth P.X.hom := hPsm
  let : ConnectedSpace P.X.left := hPconn
  let : IsAffineHom P.X.hom := hPaff
  obtain ⟨T, s, hs⟩ := exists_maximalSplitTorus P
  obtain ⟨U, z, hz⟩ := hradical k P
  obtain ⟨H, h, hsplit, hprod⟩ := henvelope k G P i hi.1 T s hs U z hz
  obtain ⟨g, f, hf⟩ :=
    hcontainment k G Q j hj.1 H (h ≫ i)
      (hprod.isClosedSubgroup.comp hi.isClosedSubgroup) hsplit
  let e := G.innerIso g
  let j' := j ≫ e.inv
  have hj' : IsMinimalPseudoParabolicSubgroup j' := hj.comp_iso e.symm
  have hf' : f ≫ j' = h ≫ i := by
    simpa only [j', e, Category.assoc, Iso.hom_inv_id, Category.comp_id] using
      congrArg (fun a => a ≫ e.inv) hf
  have hH : SubgroupFunctor.range (h ≫ i) ≤ SubgroupFunctor.range j' :=
    SubgroupFunctor.range_le_of_factor f hf'
  have hT : SubgroupFunctor.range (s ≫ i) ≤ SubgroupFunctor.range j' :=
    (SubgroupFunctor.range_comp_mono hprod.left_le i).trans hH
  have hU : SubgroupFunctor.range (z ≫ i) ≤ SubgroupFunctor.range j' :=
    (SubgroupFunctor.range_comp_mono hprod.right_le i).trans hH
  obtain ⟨hsG, _, hminimal⟩ := hstructure k G P i hi.1 T s hs
  have hPprod := (hminimal U z hz).mp hi
  let : IsClosedImmersion j'.hom.hom.left := hj'.isClosedSubgroup
  let : Mono j'.hom.hom := Over.mono_of_mono_left _
  have hjrep : (SubgroupFunctor.range j').IsRepresentedBy j' := ⟨inferInstance, rfl⟩
  obtain ⟨sQ, hsQ, hsQcomp⟩ := hsG.exists_lift hjrep hj'.isClosedSubgroup hT
  have hcentralizer : torusCentralizer (s ≫ i) ≤ SubgroupFunctor.range j' := by
    have hc := (hstructure k G Q j' hj'.1 T sQ hsQ).2.1
    rwa [hsQcomp] at hc
  have hle : SubgroupFunctor.range i ≤ SubgroupFunctor.range j' :=
    hPprod.range_le hcentralizer hU
  have hconj : SubgroupConjugate i j' :=
    hj'.subgroupConjugate_of_range_le hi.1 hle
  have hback : SubgroupConjugate j' j := by
    simpa only [j', e, Category.assoc, Iso.inv_hom_id, Category.comp_id] using
      SubgroupConjugate.conjugate j' g
  exact hconj.trans hback

/-- Choose the actual rational conjugator and source isomorphism produced by
the structural assembly. Every unproved structural assertion is an argument. -/
def minimalPseudoParabolicConjugatorOfStructure
    (hgeometry : PseudoParabolicSubgroupStructureStatement.{u})
    (hradical : SplitUnipotentRadicalExistenceStatement.{u})
    (henvelope : PseudoParabolicSplitSolvableEnvelopeStatement.{u})
    (hcontainment : SplitSolvableIntoPseudoParabolicStatement.{u})
    (hstructure : PseudoParabolicMaximalSplitTorusStructureStatement.{u})
    {k : Type u} [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth G.X.hom] [ConnectedSpace G.X.left] [IsAffineHom G.X.hom]
    {P Q : GroupScheme (Spec (CommRingCat.of k))} (i : P ⟶ G) (j : Q ⟶ G)
    (hi : IsMinimalPseudoParabolicSubgroup i) (hj : IsMinimalPseudoParabolicSubgroup j) :
    Σ g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X,
      {e : P ≅ Q // i ≫ (G.innerIso g).hom = e.hom ≫ j} := by
  let hc := minimalPseudoParabolicConjugacy_of_structure
    hgeometry hradical henvelope hcontainment hstructure k G
    inferInstance inferInstance inferInstance P Q i j hi hj
  exact ⟨hc.choose, hc.choose_spec.choose, hc.choose_spec.choose_spec⟩

end Langlands.GroupScheme
