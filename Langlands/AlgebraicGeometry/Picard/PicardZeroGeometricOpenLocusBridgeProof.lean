import Langlands.AlgebraicGeometry.Picard.PicardZeroGeometricOpenLocusBridgeStatement
import Mathlib.AlgebraicGeometry.ResidueField
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-! # The all-test Picard-zero criterion from a geometric-point locus -/

universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard Langlands.SchemeModule

/-- Every point of a scheme is the image of a geometric point in the same universe. -/
private lemma exists_geometricPoint_over (X : Scheme.{u}) (x : X) :
    ∃ (K : Type u) (_ : Field K) (_ : IsAlgClosed K)
      (s : Spec (CommRingCat.of K) ⟶ X) (z : Spec (CommRingCat.of K)), s z = x := by
  let K := AlgebraicClosure (X.residueField x)
  let s : Spec (CommRingCat.of K) ⟶ X :=
    Spec.map (CommRingCat.ofHom (algebraMap (X.residueField x) K)) ≫
      X.fromSpecResidueField x
  refine ⟨K, inferInstance, inferInstance, s, IsLocalRing.closedPoint K, ?_⟩
  change X.fromSpecResidueField x _ = x
  exact X.fromSpecResidueField_apply x _

/-- Range containment is detected after all geometric-point maps into the source. -/
private lemma range_subset_iff_geometricPoints {X Y : Scheme.{u}} (f : X ⟶ Y)
    (Z : Set Y) :
    Set.range f ⊆ Z ↔
      ∀ (K : Type u) [Field K] [IsAlgClosed K]
        (s : Spec (CommRingCat.of K) ⟶ X), Set.range (s ≫ f) ⊆ Z := by
  constructor
  · intro hf K _ _ s y hy
    obtain ⟨z, rfl⟩ := hy
    exact hf ⟨s z, Scheme.Hom.comp_apply s f z⟩
  · intro hf y hy
    obtain ⟨x, rfl⟩ := hy
    obtain ⟨K, hK, hclosed, s, z, hz⟩ := exists_geometricPoint_over X x
    let : Field K := hK
    let : IsAlgClosed K := hclosed
    have h := hf K s (Set.mem_range_self z)
    simpa only [Scheme.Hom.comp_apply, hz] using h

/-- The class predicate on a twice-pulled-back family agrees with direct composition. -/
private lemma picardZeroFamily_relativePullback_comp {S : Scheme.{u}}
    (A : AbelianScheme S) {P T V : Over S} (L : RigidifiedFamily A P)
    (h : T ⟶ P) (g : V ⟶ T) :
    IsPicardZeroFamily A
      ((RigidifiedLineBundle.relativePullback A.X.hom (unitSection A)
        (unitSection_comp A) g).obj
        ((RigidifiedLineBundle.relativePullback A.X.hom (unitSection A)
          (unitSection_comp A) h).obj L)) ↔
      IsPicardZeroFamily A
        ((RigidifiedLineBundle.relativePullback A.X.hom (unitSection A)
          (unitSection_comp A) (g ≫ h)).obj L) := by
  have hc := RigidifiedLineBundle.classifyingMap_comp A.X.hom (unitSection A)
    (unitSection_comp A) RigidifiedModule.pullbackCoherence L g h
  exact (congrArg (IsPicardZeroClass A) hc).symm.to_iff

/-- A chosen structure map can be replaced by the equal composite structure map. -/
private lemma picardZeroFamily_overHomMk_iff {S : Scheme.{u}}
    (A : AbelianScheme S) {P : Over S} (L : RigidifiedFamily A P)
    {X : Scheme.{u}} (p : X ⟶ S) (s : X ⟶ P.left) (hs : s ≫ P.hom = p) :
    IsPicardZeroFamily A
      ((RigidifiedLineBundle.relativePullback A.X.hom (unitSection A)
        (unitSection_comp A) (Over.homMk s hs : Over.mk p ⟶ P)).obj L) ↔
      IsPicardZeroFamily A
        ((RigidifiedLineBundle.relativePullback A.X.hom (unitSection A)
          (unitSection_comp A)
          (Over.homMk s rfl : Over.mk (s ≫ P.hom) ⟶ P)).obj L) := by
  subst p
  rfl

/-- Geometric detection and a geometric-point locus give the criterion on all test schemes. -/
lemma isPicardZeroOpenLocus_of_geometricPoints
    (detection : PicardZeroGeometricDetectionStatement.{u})
    {S : Scheme.{u}} (A : AbelianScheme S) {P : Over S}
    (L : RigidifiedFamily A P) (U : P.left.Opens)
    (hU : ∀ (K : Type u) [Field K] [IsAlgClosed K]
      (s : Spec (CommRingCat.of K) ⟶ P.left),
      IsPicardZeroFamily A
        ((RigidifiedLineBundle.relativePullback A.X.hom (unitSection A)
          (unitSection_comp A)
          (Over.homMk s rfl : Over.mk (s ≫ P.hom) ⟶ P)).obj L) ↔
        Set.range s ⊆ (U : Set P.left)) :
    IsPicardZeroOpenLocus A L U := by
  intro T h
  rw [isPicardZeroClass_classifyingMap_iff]
  rw [detection S A T]
  rw [range_subset_iff_geometricPoints h.left (U : Set P.left)]
  apply forall_congr'
  intro K
  apply forall_congr'
  intro hK
  apply forall_congr'
  intro hclosed
  let : Field K := hK
  let : IsAlgClosed K := hclosed
  apply forall_congr'
  intro s
  let g : Over.mk (s ≫ T.hom) ⟶ T := Over.homMk s rfl
  exact (picardZeroFamily_relativePullback_comp A L h g).trans
    ((picardZeroFamily_overHomMk_iff A L (s ≫ T.hom) (s ≫ h.left)
      (by rw [Category.assoc, h.w])).trans (hU K (s ≫ h.left)))

/-- The exact generic bridge proposition, with its original reusable lemma above. -/
lemma picardZeroGeometricOpenLocusBridge :
    PicardZeroGeometricOpenLocusBridgeStatement.{u} :=
  isPicardZeroOpenLocus_of_geometricPoints

end Langlands.AbelianScheme
