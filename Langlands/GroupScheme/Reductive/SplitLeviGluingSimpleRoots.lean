import Langlands.GroupScheme.Reductive.SplitLeviGluingLocal
import Mathlib.LinearAlgebra.RootSystem.BaseExists

/-! # Actual simple roots and rank-one directions for Levi gluing -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme.LeviGluing

variable {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))}
    {T : CommGroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
    (i : T.toGrp ⟶ G)

/-- A generic chamber and one actual rank-one centralizer direction for each
of its intrinsic simple roots. -/
structure SimpleRootDirections where
  chamber : cocharacterLattice T
  generic : IsGenericCocharacter i chamber
  direction : simpleRelativeRoots i chamber → cocharacterLattice T
  annihilates : ∀ a : simpleRelativeRoots i chamber,
    latticePairing T (a : characterLattice T) (direction a) = 0
  rankOne : ∀ a, IsRankOneDirection i (direction a)

/-- Construct the simple-root family and its local directions from the split
torus and actual finite root set, without a supplied chamber or root group. -/
def simpleRootDirections (hT : IsSplitTorus T.toGrp) : SimpleRootDirections i := by
  let ν := genericCocharacterOfIsSplitTorus hT i
  refine
    { chamber := ν
      generic := genericCocharacterOfIsSplitTorus_spec hT i
      direction := fun a => RootReducedness.kernelCocharacter hT a.2.1.1.1
        (hT.finite_relativeRoots i)
      annihilates := ?_
      rankOne := ?_ }
  · intro a
    exact RootReducedness.latticePairing_kernelCocharacter hT a.2.1.1.1
      (hT.finite_relativeRoots i)
  · intro a
    exact kernelCocharacter_isRankOneDirection i hT a.2.1.1.1

section RootDatum

variable {J : Type v}
    (P : RootDatum J (characterLattice T) (cocharacterLattice T))
    (hP : IsRootDatumOf i P) (ν : cocharacterLattice T)

include hP in
/-- A root datum realizing the actual roots has finite index type. -/
theorem finite_rootIndex (hT : IsSplitTorus T.toGrp) : Finite J := by
  have hfin : (Set.range P.root).Finite := by
    rw [hP.2.1]
    exact hT.finite_relativeRoots i
  let : Fintype (Set.range P.root) := hfin.fintype
  exact Finite.of_injective
    (fun j : J => (⟨P.root j, ⟨j, rfl⟩⟩ : Set.range P.root))
    (fun _ _ h => P.root.injective (congrArg Subtype.val h))

omit [LocallyOfFiniteType G.X.hom] in
include hP in
/-- Positive indecomposable indices of a realizing root datum are exactly the
intrinsic simple roots. No reducedness condition is required. -/
theorem mem_baseOf_iff_simple (j : J) :
    j ∈ IsAddIndecomposable.baseOf P.root
      ((latticePairing T).flip ν).toAddMonoidHom ↔
        P.root j ∈ simpleRelativeRoots i ν := by
  constructor
  · intro hj
    refine ⟨⟨?_, hj.1⟩, ?_⟩
    · rw [← (show Set.range P.root = relativeRoots i from hP.2.1)]
      exact ⟨j, rfl⟩
    · rintro ⟨a, ha, b, hb, hab⟩
      have ha' := ha.1
      have hb' := hb.1
      rw [← (show Set.range P.root = relativeRoots i from hP.2.1)] at ha' hb'
      obtain ⟨a, rfl⟩ := ha'
      obtain ⟨b, rfl⟩ := hb'
      rcases hj.2 a ha.2 b hb.2 hab with hzero | hzero
      · exact P.ne_zero a hzero
      · exact P.ne_zero b hzero
  · intro hj
    refine ⟨hj.1.2, ?_⟩
    intro a ha b hb hab
    exfalso
    apply hj.2
    refine ⟨P.root a, ⟨?_, ha⟩, P.root b, ⟨?_, hb⟩, hab⟩
    · rw [← (show Set.range P.root = relativeRoots i from hP.2.1)]
      exact ⟨a, rfl⟩
    · rw [← (show Set.range P.root = relativeRoots i from hP.2.1)]
      exact ⟨b, rfl⟩

/-- The actual index equivalence between the positive indecomposable root-datum
indices and the intrinsic simple-root characters. -/
def simpleRootIndexEquiv :
    IsAddIndecomposable.baseOf P.root
      ((latticePairing T).flip ν).toAddMonoidHom ≃
        simpleRelativeRoots i ν :=
  Equiv.ofBijective
    (fun j => ⟨P.root j, (mem_baseOf_iff_simple i P hP ν j).mp j.2⟩)
    ⟨by
      intro a b hab
      apply Subtype.ext
      exact P.root.injective (congrArg Subtype.val hab), by
      intro a
      have ha := a.2.1.1
      rw [← (show Set.range P.root = relativeRoots i from hP.2.1)] at ha
      obtain ⟨j, hj⟩ := ha
      refine ⟨⟨j, (mem_baseOf_iff_simple i P hP ν j).mpr ?_⟩, Subtype.ext hj⟩
      simpa only [hj] using a.2⟩

omit [LocallyOfFiniteType G.X.hom] in
theorem root_simpleRootIndexEquiv_symm (a : simpleRelativeRoots i ν) :
    P.root ((simpleRootIndexEquiv i P hP ν).symm a) = a :=
  congrArg Subtype.val ((simpleRootIndexEquiv i P hP ν).apply_symm_apply a)

include hP in
/-- Simple intrinsic roots of an actual realizing root datum are integrally
linearly independent. Root and coroot bases are not assumed. -/
theorem linearIndependent_simpleRoots (hT : IsSplitTorus T.toGrp)
    (hν : IsGenericCocharacter i ν) :
    LinearIndependent ℤ
      (fun a : simpleRelativeRoots i ν => (a : characterLattice T)) := by
  let : Finite J := finite_rootIndex i P hP hT
  let f := (latticePairing T).flip ν
  have hf (j : J) : f (P.root j) ≠ 0 := by
    apply hν
    rw [← (show Set.range P.root = relativeRoots i from hP.2.1)]
    exact ⟨j, rfl⟩
  have hli := P.linearIndepOn_root_baseOf' (S := ℤ) f hf
  let e := simpleRootIndexEquiv i P hP ν
  have h := hli.comp e.symm e.symm.injective
  convert h using 1
  funext a
  exact (root_simpleRootIndexEquiv_symm i P hP ν a).symm

include hP in
/-- The additive monoid of positive actual roots is generated by the intrinsic
simple roots. This remains valid for a nonreduced root datum. -/
theorem closure_simpleRoots_eq_positive (hT : IsSplitTorus T.toGrp) :
    AddSubmonoid.closure (simpleRelativeRoots i ν) =
      AddSubmonoid.closure (positiveRelativeRoots i ν) := by
  let : Finite J := finite_rootIndex i P hP hT
  let f := (latticePairing T).flip ν
  have hs : P.root '' IsAddIndecomposable.baseOf P.root f.toAddMonoidHom =
      simpleRelativeRoots i ν := by
    ext a
    constructor
    · rintro ⟨j, hj, rfl⟩
      exact (mem_baseOf_iff_simple i P hP ν j).mp hj
    · intro ha
      have ha' := ha.1.1
      rw [← (show Set.range P.root = relativeRoots i from hP.2.1)] at ha'
      obtain ⟨j, rfl⟩ := ha'
      exact ⟨j, (mem_baseOf_iff_simple i P hP ν j).mpr ha, rfl⟩
  have hp : P.root '' {j | 0 < f (P.root j)} = positiveRelativeRoots i ν := by
    ext a
    constructor
    · rintro ⟨j, hj, rfl⟩
      refine ⟨?_, hj⟩
      rw [← (show Set.range P.root = relativeRoots i from hP.2.1)]
      exact ⟨j, rfl⟩
    · rintro ⟨ha, hpos⟩
      rw [← (show Set.range P.root = relativeRoots i from hP.2.1)] at ha
      obtain ⟨j, rfl⟩ := ha
      exact ⟨j, hpos, rfl⟩
  rw [← hs, ← hp]
  exact AddSubmonoid.closure_image_isAddIndecomposable_baseOf P.root f.toAddMonoidHom

omit [LocallyOfFiniteType G.X.hom] in
include hP in
/-- Differences of distinct intrinsic simple roots are not actual roots. -/
theorem simple_sub_not_root (hν : IsGenericCocharacter i ν)
    (a b : simpleRelativeRoots i ν) (hab : a ≠ b) :
    (a : characterLattice T) - b ∉ roots i := by
  let _ := P.indexNeg
  let f := (latticePairing T).flip ν
  have hf (j : J) : f (P.root j) ≠ 0 := by
    apply hν
    rw [← (show Set.range P.root = relativeRoots i from hP.2.1)]
    exact ⟨j, rfl⟩
  let e := simpleRootIndexEquiv i P hP ν
  have h := IsAddIndecomposable.pairwise_baseOf_sub_notMem P.root
    (by simp) f.toAddMonoidHom hf (e.symm a).2 (e.symm b).2
    (fun h => hab (e.symm.injective (Subtype.ext h)))
  dsimp only [e] at h
  simpa only [root_simpleRootIndexEquiv_symm, hP.2.1] using h

end RootDatum

end Langlands.GroupScheme.LeviGluing
