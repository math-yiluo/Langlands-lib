import Langlands.AlgebraicGeometry.Picard.FieldPicardIdentityComponent
import Langlands.AlgebraicGeometry.Picard.OpenLocus
import Langlands.AlgebraicGeometry.Picard.PicardZeroUniversalUniquenessProof
import Mathlib.AlgebraicGeometry.ResidueField
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-! # Actual parameter isomorphisms and smoothness transport for a chosen dual scheme -/

universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard Langlands.SchemeModule

variable {S : Scheme.{u}} (A : AbelianScheme S) (hA : HasDualScheme A)

/-- The chosen dual is isomorphic over the base to any actual universal Picard-zero
parameter, using the published rigidified pullback coherence proof. -/
def dualSchemeIsoOfUniversal {P : Over S} (L : RigidifiedFamily A P)
    (hL : IsUniversalPicardZero A L) : dualScheme A hA ≅ P :=
  Classical.choose (picardZeroUniversalUniqueness
    RigidifiedModule.pullbackCoherence S A (dualScheme A hA) P
    (poincareFamily A hA) L (poincareFamily_universal A hA) hL)

/-- The parameter isomorphism compares the actual rigidified families by pullback. -/
lemma dualSchemeIsoOfUniversal_family {P : Over S} (L : RigidifiedFamily A P)
    (hL : IsUniversalPicardZero A L) :
    Nonempty ((RigidifiedLineBundle.relativePullback A.X.hom
      (unitSection A) (unitSection_comp A) (dualSchemeIsoOfUniversal A hA L hL).hom).obj L ≅
        poincareFamily A hA) :=
  (Classical.choose_spec (picardZeroUniversalUniqueness
    RigidifiedModule.pullbackCoherence S A (dualScheme A hA) P
    (poincareFamily A hA) L (poincareFamily_universal A hA) hL)).1

/-- Two actual universal Picard-zero families have equally smooth structure maps. -/
lemma smooth_dualScheme_iff_of_universal {P : Over S} (L : RigidifiedFamily A P)
    (hL : IsUniversalPicardZero A L) :
    Smooth (dualScheme A hA).hom ↔ Smooth P.hom := by
  let e := dualSchemeIsoOfUniversal A hA L hL
  have : IsIso e.hom.left :=
    inferInstanceAs (IsIso ((Over.forget S).map e.hom))
  have : IsIso e.inv.left :=
    inferInstanceAs (IsIso ((Over.forget S).map e.inv))
  constructor
  · intro h
    let := h
    rw [← e.inv.w]
    infer_instance
  · intro h
    let := h
    rw [← e.hom.w]
    infer_instance

/-- The chosen dual is isomorphic to the actual open restriction of a full universal
parameter when that open classifies geometric Picard-zero families on all tests. -/
def dualSchemeIsoOfOpenLocus {P : Over S} (L : RigidifiedFamily A P)
    (U : P.left.Opens)
    (hL : RigidifiedLineBundle.IsUniversal A.X.hom (unitSection A) (unitSection_comp A) L)
    (hU : IsPicardZeroOpenLocus A L U) :
    dualScheme A hA ≅ openLocusParameter P U :=
  dualSchemeIsoOfUniversal A hA (restrictedRigidifiedFamily A L U)
    (restrictedRigidifiedFamily_universal A L U hL hU)

/-- Smoothness of the chosen dual is equivalent to smoothness of a supplied all-test
Picard-zero open locus in a full universal parameter. -/
lemma smooth_dualScheme_iff_of_openLocus {P : Over S} (L : RigidifiedFamily A P)
    (U : P.left.Opens)
    (hL : RigidifiedLineBundle.IsUniversal A.X.hom (unitSection A) (unitSection_comp A) L)
    (hU : IsPicardZeroOpenLocus A L U) :
    Smooth (dualScheme A hA).hom ↔ Smooth (openLocusParameter P U).hom :=
  smooth_dualScheme_iff_of_universal A hA (restrictedRigidifiedFamily A L U)
    (restrictedRigidifiedFamily_universal A L U hL hU)

/-- Smoothness of an actual all-test Picard-zero open locus transports to the chosen dual. -/
lemma smooth_dualScheme_of_smooth_openLocus {P : Over S} (L : RigidifiedFamily A P)
    (U : P.left.Opens)
    (hL : RigidifiedLineBundle.IsUniversal A.X.hom (unitSection A) (unitSection_comp A) L)
    (hU : IsPicardZeroOpenLocus A L U)
    (hSmooth : Smooth (openLocusParameter P U).hom) :
    Smooth (dualScheme A hA).hom :=
  (smooth_dualScheme_iff_of_openLocus A hA L U hL hU).mpr hSmooth

/-- Range tests from algebraically closed fields in the same universe determine subsets
of any scheme. This asserts equality only of underlying sets. -/
lemma geometricPointRanges_determine_set (X : Scheme.{u}) (V W : Set X)
    (h : ∀ (K : Type u) [Field K] [IsAlgClosed K]
      (s : Spec (CommRingCat.of K) ⟶ X),
      Set.range s ⊆ V ↔ Set.range s ⊆ W) :
    V = W := by
  ext x
  let K : Type u := AlgebraicClosure (X.residueField x)
  let s : Spec (CommRingCat.of K) ⟶ X :=
    Spec.map (CommRingCat.ofHom (algebraMap (X.residueField x) K)) ≫
      X.fromSpecResidueField x
  have hs (y : Spec (CommRingCat.of K)) : s y = x := by
    exact X.fromSpecResidueField_apply x _
  have hr : Set.range s = {x} := by
    ext y
    simp only [Set.mem_range, Set.mem_singleton_iff]
    constructor
    · rintro ⟨a, rfl⟩
      exact hs a
    · rintro rfl
      exact ⟨IsLocalRing.closedPoint K, hs _⟩
  simpa only [hr, Set.singleton_subset_iff] using h K s

/-- A supplied all-test open locus is the identity-component open if a separately
supplied geometric-family/component comparison holds. This downstream adapter
does not prove that comparison or construct an open locus. -/
lemma isFullPicardIdentityComponentOpen_of_geometric_comparison
    (k : Type u) [Field k]
    (B : AbelianScheme (Scheme.Spec.obj (Opposite.op (CommRingCat.of k))))
    {P : Over (Scheme.Spec.obj (Opposite.op (CommRingCat.of k)))}
    (L : RigidifiedFamily B P)
    (hL : RigidifiedLineBundle.IsUniversal B.X.hom (unitSection B) (unitSection_comp B) L)
    (U : P.left.Opens) (hU : IsPicardZeroOpenLocus B L U)
    (hComparison : ∀ (K : Type u) [Field K] [IsAlgClosed K]
      (s : Spec (CommRingCat.of K) ⟶ P.left),
      IsPicardZeroFamily B
        ((RigidifiedLineBundle.relativePullback B.X.hom
          (unitSection B) (unitSection_comp B)
          (Over.homMk s rfl : Over.mk (s ≫ P.hom) ⟶ P)).obj L) ↔
        Set.range s ⊆ connectedComponent (fullPicardOriginPoint k B L hL)) :
    IsFullPicardIdentityComponentOpen k B L hL U := by
  change (U : Set P.left) = connectedComponent (fullPicardOriginPoint k B L hL)
  refine geometricPointRanges_determine_set P.left (U : Set P.left)
    (connectedComponent (fullPicardOriginPoint k B L hL)) ?_
  intro K _ _ s
  let g : Over.mk (s ≫ P.hom) ⟶ P := Over.homMk s rfl
  have hClass := hU (Over.mk (s ≫ P.hom)) g
  have hFamily := isPicardZeroClass_classifyingMap_iff B L g
  exact hClass.symm.trans (hFamily.trans (hComparison K s))

end Langlands.AbelianScheme
