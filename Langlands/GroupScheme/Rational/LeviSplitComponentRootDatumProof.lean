import Langlands.GroupScheme.Rational.LeviSplitComponentRootDatumStatement
import Langlands.GroupScheme.Rational.LeviSplitComponentCentralizerProof
import Langlands.GroupScheme.Rational.MaximalSplitTorusExtension
import Langlands.GroupScheme.Rational.MaximalSplitTorusCentralizer
import Langlands.GroupScheme.Rational.SplitCentralDirectionsConstruction
import Langlands.GroupScheme.Rational.RootAnnihilatorCentralityProof
import Langlands.GroupScheme.Rational.RootReflectionExistenceProof
import Langlands.GroupScheme.Rational.CentralRootRestriction
import Langlands.GroupScheme.Dynamic.LeviAdjointDeterminantReciprocityReduction
import Langlands.GroupScheme.Lie.Functoriality
import Langlands.GroupScheme.ClosedSubgroupMonomorphism
import Langlands.Geometry.Building.RealTorusDuality

/-! # The weights of a split component inside a relative root datum -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

open RealTorusSpace

/-- Centralizing a torus centralizes every torus mapping to it. -/
theorem torusCentralizer_le_torusCentralizer_comp {S : Scheme.{u}} {A T : CommGroupScheme S}
    {G : GroupScheme S} (f : A.toGrp ⟶ T.toGrp) (i : T.toGrp ⟶ G) :
    torusCentralizer i ≤ torusCentralizer (f ≫ i) := by
  intro U g hg V a t
  have h := hg V a (t ≫ f.hom.hom)
  have e : (f ≫ i).hom.hom = f.hom.hom ≫ i.hom.hom := rfl
  rw [e]
  simpa only [Category.assoc] using h

/-- Evaluation of a character on the image of a real cocharacter is evaluation of the
restricted character. -/
theorem eval_cocharacterMapReal_apply {k : Type u} [Field k]
    {S T : CommGroupScheme (Spec (CommRingCat.of k))} (t : S ⟶ T) (a : characterLattice T)
    (v : V S) : eval T a (cocharacterMapReal t v) = eval S (t ≫ a) v := by
  rw [eval_eq_pair, eval_eq_pair, pair_cocharacterMapReal]
  rfl

/-- The split component of a rational Levi lies in a maximal split torus of the ambient group
whose roots and integral coroots form a root datum, and the real cocharacters of the split
component are the common kernel of the roots vanishing on it. -/
theorem leviSplitComponentRootDatum : LeviSplitComponentRootDatumStatement.{u} := by
  intro F _ G _ _ hG P M p l hp hl A a hA
  have hM := hl.isConnectedReductive
  have : IsAffineHom M.X.hom := hM.isAffineHom
  have : Smooth M.X.hom := hM.smooth
  have : ConnectedSpace M.X.left := hM.connectedSpace
  have hj : IsClosedSubgroup (l ≫ p) := hl.isClosedSubgroup.comp hp.isClosedSubgroup
  obtain ⟨T, s, hs, f, hf⟩ :=
    exists_maximalSplitTorus_extension M a hA.isCentralSplitTorus.isSplitSubtorus
  have hT : IsSplitTorus T.toGrp := hs.1.1
  have hZA : torusCentralizer (a ≫ l ≫ p) = SubgroupFunctor.range (l ≫ p) :=
    leviSplitComponentCentralizer F G hG P M p l hp hl A a hA
  have hZ : torusCentralizer (s ≫ l ≫ p) ≤ SubgroupFunctor.range (l ≫ p) := by
    rw [← hZA, ← hf, Category.assoc]
    exact torusCentralizer_le_torusCentralizer_comp f (s ≫ l ≫ p)
  have ht : IsMaximalSplitTorus (s ≫ l ≫ p) := hs.comp_of_torusCentralizer_le_range hj hZ
  let g : A ⟶ T := Additive.ofMul f
  have hg : CommGroupScheme.groupHom g = f := rfl
  have : Mono s.hom.hom.left := hs.isSplitSubtorus.mono
  have : Mono (s ≫ l ≫ p).hom.hom.left := ht.isSplitSubtorus.mono
  have : Mono a.hom.hom.left := hA.isCentralSplitTorus.isSplitSubtorus.mono
  have : Mono (CommGroupScheme.groupHom g).hom.hom.left := by
    rw [hg]
    have h : f.hom.hom.left ≫ s.hom.hom.left = a.hom.hom.left := by
      rw [← hf]
      rfl
    exact mono_of_mono_fac h
  have hrange := hA.range_cocharacterMapReal_eq_relativeCentralDirections rootAnnihilatorCentrality
    hT g (i := s) hf
  refine ⟨T, s ≫ l ≫ p, g, hT, ?_, cocharacterMapReal_injective g, ?_, ?_⟩
  · rw [hg, ← Category.assoc, hf]
  · rw [hrange]
    apply le_antisymm
    · intro v hv
      rw [mem_rootAnnihilator]
      rintro c ⟨-, hc⟩
      rw [← hrange] at hv
      obtain ⟨x, rfl⟩ := hv
      exact hc x
    · intro v hv
      rw [mem_rootAnnihilator] at hv
      rw [mem_relativeCentralDirections]
      intro c hc
      apply hv
      refine ⟨?_, ?_⟩
      · have : Mono (l ≫ p).hom.hom := hj.mono_overHom
        exact roots_subset_comp (l ≫ p) s hc
      · intro x
        have h0 := root_restrict_eq_zero_of_isCentral s g hA.isCentralSplitTorus.isSplitSubtorus.1
          (by rw [hg, hf]; exact hA.isCentralSplitTorus.isCentral) hc
        rw [eval_cocharacterMapReal_apply, h0, eval_eq_pair, TensorProduct.tmul_zero, map_zero]
        rfl
  · obtain ⟨D, -⟩ := relativeRootReflectionExistence F G hG T (s ≫ l ≫ p) ht
    intro c hc
    refine ⟨D.coroot ⟨c, hc⟩, D.pair_self ⟨c, hc⟩, fun δ hδ => ?_⟩
    rw [← D.action ⟨c, hc⟩ δ]
    exact ⟨weylAction_mapsTo_relativeRoots _ _ hδ, finrank_weightSpace_weylAction _ δ⟩

end Langlands.GroupScheme
