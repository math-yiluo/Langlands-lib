import Langlands.GroupScheme.Torus.RelativeCocharacterCentralizers
import Langlands.GroupScheme.Reductive.RankOneCentralizerDetection

/-! # Fixed relative root centralizers from an actual geometric fibre -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.splitTorus

variable {r : Type u} [CommRing r] (I : Type u) [Fintype I]
  (G : GroupScheme (Spec (CommRingCat.of r))) [Smooth G.X.hom] [IsAffineHom G.X.hom]
  (i : splitTorus (Spec (CommRingCat.of r)) I ⟶ G)

local instance rootCentralizerProfile_smooth_geometricFiber
    (s : Spec (CommRingCat.of r)) : Smooth (geometricFiber G s).X.hom :=
  inferInstanceAs (Smooth (CategoryTheory.Limits.pullback.snd G.X.hom (geometricPoint _ s)))

local instance rootCentralizerProfile_affine_geometricFiber
    (s : Spec (CommRingCat.of r)) : IsAffineHom (geometricFiber G s).X.hom :=
  inferInstanceAs (IsAffineHom (CategoryTheory.Limits.pullback.snd G.X.hom (geometricPoint _ s)))

/-- Every actual relative cocharacter centralizer inherits selfcentralization
of the given torus in each geometric identity component. -/
theorem mem_geometricSelfCentralizingTorusLocus_centralizer [DecidableEq I]
    (hi : IsClosedSubgroup i) (n : I → ℤ) (s : Spec (CommRingCat.of r))
    (hs : s ∈ geometricSelfCentralizingTorusLocus I G i) :
    s ∈ geometricSelfCentralizingTorusLocus I
      (RelativeCocharacterCentralizer.groupScheme I G i n)
      (RelativeCocharacterCentralizer.torusHom I G i n) := by
  have hrank : exponentWeightRank I
      (RelativeCocharacterCentralizer.groupScheme I G i n)
      (RelativeCocharacterCentralizer.torusHom I G i n) 0 s =
        exponentWeightRank I G i 0 s := by
    rw [← finrank_weight_geometricIdentityComponentHom,
      ← finrank_weight_geometricIdentityComponentHom]
    exact RelativeCocharacterCentralizer.finrank_geometricCentralizerWeight
      I G i n s 0 (by simp)
  apply (mem_geometricSelfCentralizingTorusLocus_iff I _ _
    (RelativeCocharacterCentralizer.isClosedSubgroup_torusHom I G i n hi) s).mpr
  exact hrank.trans ((mem_geometricSelfCentralizingTorusLocus_iff I G i hi s).mp hs)

/-- The integer coordinate vector of an actual generic cocharacter at the
specified geometric identity-component fibre. -/
def rootCentralizerVector (s : Spec (CommRingCat.of r))
    (m : I → ℤ) (hm : m ∈ geometricExponentRoots I G i s) : I → ℤ :=
  cocharacterLatticeEquiv
    (AlgebraicClosure ((Spec (CommRingCat.of r)).residueField s)) I
      (RankOneCentralizerDetection.cocharacter
        (T := commGroupScheme _ I) (geometricIdentityComponentHom I G i s)
        (isSplitTorus_splitTorus I) (exponentCharacter _ I m) hm.1)

/-- Extending the chosen vector over the original base recovers the exact
original generic cocharacter on the specified geometric fibre. -/
theorem exponentCocharacter_rootCentralizerVector (s : Spec (CommRingCat.of r))
    (m : I → ℤ) (hm : m ∈ geometricExponentRoots I G i s) :
    exponentCocharacter
      (Spec (CommRingCat.of (AlgebraicClosure ((Spec (CommRingCat.of r)).residueField s))))
      I (rootCentralizerVector I G i s m hm) =
        RankOneCentralizerDetection.cocharacter
          (T := commGroupScheme _ I) (geometricIdentityComponentHom I G i s)
          (isSplitTorus_splitTorus I) (exponentCharacter _ I m) hm.1 := by
  rw [exponentCocharacter_eq_cocharacterLatticeEquiv_symm]
  exact (cocharacterLatticeEquiv _ I).symm_apply_apply _

/-- The chosen fixed integer vector annihilates the specified actual root. -/
theorem dot_rootCentralizerVector (s : Spec (CommRingCat.of r))
    (m : I → ℤ) (hm : m ∈ geometricExponentRoots I G i s) :
    ∑ j, m j * rootCentralizerVector I G i s m hm j = 0 := by
  rw [← latticePairing_exponentCharacter_exponentCocharacter
    I (AlgebraicClosure ((Spec (CommRingCat.of r)).residueField s)),
    exponentCocharacter_rootCentralizerVector]
  exact RankOneCentralizerDetection.pairing_cocharacter
    (T := commGroupScheme _ I) (geometricIdentityComponentHom I G i s)
    (isSplitTorus_splitTorus I) (exponentCharacter _ I m) hm.1

/-- Every root surviving in this actual relative centralizer at the original
fibre is linearly dependent with the specified original root. -/
theorem dependent_of_mem_geometricRootCentralizerExponentRoots
    (s : Spec (CommRingCat.of r)) (m : I → ℤ)
    (hm : m ∈ geometricExponentRoots I G i s) (a : I → ℤ)
    (ha : a ∈ geometricExponentRoots I
      (RelativeCocharacterCentralizer.groupScheme I G i (rootCentralizerVector I G i s m hm))
      (RelativeCocharacterCentralizer.torusHom I G i (rootCentralizerVector I G i s m hm)) s) :
    ¬ LinearIndependent ℤ ![
      exponentCharacter
        (Spec (CommRingCat.of (AlgebraicClosure ((Spec (CommRingCat.of r)).residueField s)))) I m,
      exponentCharacter
        (Spec (CommRingCat.of (AlgebraicClosure ((Spec (CommRingCat.of r)).residueField s)))) I a] := by
  obtain ⟨haroot, hadot⟩ :=
    (RelativeCocharacterCentralizer.mem_geometricCentralizerExponentRoots_iff
      I G i (rootCentralizerVector I G i s m hm) s a).mp ha
  have hapair := hadot
  rw [← latticePairing_exponentCharacter_exponentCocharacter
    I (AlgebraicClosure ((Spec (CommRingCat.of r)).residueField s)),
    exponentCocharacter_rootCentralizerVector] at hapair
  exact RootReducedness.not_linearIndependent_of_latticePairing_kernelCocharacter
    (T := commGroupScheme _ I) (isSplitTorus_splitTorus I) hm.1
    ((isSplitTorus_splitTorus I).finite_relativeRoots
      (T := commGroupScheme _ I) (geometricIdentityComponentHom I G i s)) haroot hapair

/-- Supplied forward negation and reducedness at the original actual fibre
identify the centralizer's complete actual root support as the two roots. -/
theorem mem_geometricRootCentralizerExponentRoots_iff_pair
    (s : Spec (CommRingCat.of r)) (m : I → ℤ)
    (hm : m ∈ geometricExponentRoots I G i s)
    (hneg : -m ∈ geometricExponentRoots I G i s)
    (hred : ∀ a ∈ geometricExponentRoots I G i s,
      ¬ LinearIndependent ℤ ![
        exponentCharacter
          (Spec (CommRingCat.of (AlgebraicClosure ((Spec (CommRingCat.of r)).residueField s)))) I m,
        exponentCharacter
          (Spec (CommRingCat.of (AlgebraicClosure ((Spec (CommRingCat.of r)).residueField s)))) I a] →
        a = m ∨ a = -m)
    (a : I → ℤ) :
    a ∈ geometricExponentRoots I
      (RelativeCocharacterCentralizer.groupScheme I G i (rootCentralizerVector I G i s m hm))
      (RelativeCocharacterCentralizer.torusHom I G i (rootCentralizerVector I G i s m hm)) s ↔
        a = m ∨ a = -m := by
  constructor
  · intro ha
    exact hred a
      ((RelativeCocharacterCentralizer.mem_geometricCentralizerExponentRoots_iff
        I G i (rootCentralizerVector I G i s m hm) s a).mp ha).1
      (dependent_of_mem_geometricRootCentralizerExponentRoots I G i s m hm a ha)
  · intro ha
    rcases ha with ha | ha
    · subst a
      exact (RelativeCocharacterCentralizer.mem_geometricCentralizerExponentRoots_iff
        I G i (rootCentralizerVector I G i s m hm) s m).mpr
        ⟨hm, dot_rootCentralizerVector I G i s m hm⟩
    · subst a
      apply (RelativeCocharacterCentralizer.mem_geometricCentralizerExponentRoots_iff
        I G i (rootCentralizerVector I G i s m hm) s (-m)).mpr
      refine ⟨hneg, ?_⟩
      simpa only [Pi.neg_apply, neg_mul, Finset.sum_neg_distrib, neg_eq_zero] using
        dot_rootCentralizerVector I G i s m hm

end Langlands.GroupScheme.splitTorus
