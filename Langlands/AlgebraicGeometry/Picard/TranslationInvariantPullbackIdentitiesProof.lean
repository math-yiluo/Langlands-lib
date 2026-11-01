import Langlands.AlgebraicGeometry.Picard.TranslationInvariantPullbackIdentitiesStatement
import Langlands.AlgebraicGeometry.Picard.RigidifiedClassesEqualizerClosedProof
import Langlands.AlgebraicGeometry.Picard.LineBundleNormalization
import Langlands.AlgebraicGeometry.Picard.LineBundleIsoClassGroup
import Langlands.AlgebraicGeometry.Picard.RigidifiedPullbackProofs
import Langlands.AlgebraicGeometry.Picard.MumfordBundle
import Langlands.AlgebraicGeometry.Modules.PullbackTensorProof
import Langlands.AlgebraicGeometry.SmoothReducedProof
import Mathlib.AlgebraicGeometry.AlgClosed.Basic

noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.AbelianScheme.TranslationInvariantIdentities

open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules
open Langlands.SchemeModule

variable {K : Type u} [Field K] [IsAlgClosed K]
  (A : AbelianScheme (Spec (CommRingCat.of K)))

/-- Rational points detect equality of rigidified classes over a reduced parameter. -/
lemma classes_eq_of_rational {T : Over (Spec (CommRingCat.of K))}
    [LocallyOfFiniteType T.hom] [IsReduced T.left]
    (q r : RigidifiedClasses A T)
    (H : ∀ x : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ T,
      RigidifiedLineBundle.classesPullback A.X.hom (unitSection A) (unitSection_comp A) x q =
        RigidifiedLineBundle.classesPullback A.X.hom (unitSection A) (unitSection_comp A) x r) :
    q = r := by
  obtain ⟨Z, incl, hincl, hZ⟩ := rigidifiedClassesEqualizerClosed _ A T q r
  let := hincl
  have : JacobsonSpace T.left := LocallyOfFiniteType.jacobsonSpace T.hom
  have hall : closedPoints T.left ⊆ Set.range incl := by
    intro t ht
    let x : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ T :=
      Over.homMk (pointOfClosedPoint T.hom t ht) (pointOfClosedPoint_comp T.hom t ht)
    obtain ⟨g, hg⟩ := (hZ _ x).mpr (H x)
    refine ⟨g (IsLocalRing.closedPoint K), ?_⟩
    change (g ≫ incl) (IsLocalRing.closedPoint K) = t
    rw [hg]
    exact pointOfClosedPoint_apply T.hom t ht _
  have hclosed : IsClosed (Set.range incl) := incl.isClosedEmbedding.isClosed_range
  have hsurj : Set.univ ⊆ Set.range incl := by
    rw [← closure_closedPoints]
    exact hclosed.closure_subset_iff.mpr hall
  let : Surjective incl := ⟨fun t ↦ hsurj (Set.mem_univ t)⟩
  let : IsIso incl := isIso_of_isClosedImmersion_of_surjective incl
  have heq := (hZ T (𝟙 T)).mp ⟨inv incl, IsIso.inv_hom_id incl⟩
  have hid (s : RigidifiedClasses A T) :
      RigidifiedLineBundle.classesPullback A.X.hom (unitSection A) (unitSection_comp A)
        (𝟙 T) s = s := by
    induction s using Quotient.inductionOn with | h L =>
      exact Quotient.sound ⟨(RigidifiedLineBundle.relativePullbackId
        RigidifiedModule.pullbackCoherence A.X.hom (unitSection A)
          (unitSection_comp A) T).app L⟩
  simpa only [hid] using heq

/-- Fibrewise isomorphisms and the same restriction along the identity give a
global isomorphism of the underlying line bundles. -/
lemma iso_of_rational {T : Over (Spec (CommRingCat.of K))}
    [LocallyOfFiniteType T.hom] [IsReduced T.left]
    (M N : LineBundle ((relativeSpace A.X.hom).obj T))
    (e : (LineBundle.pullback
        ((relativeSection A.X.hom (unitSection A) (unitSection_comp A)).app T)).obj M ≅
      (LineBundle.pullback
        ((relativeSection A.X.hom (unitSection A) (unitSection_comp A)).app T)).obj N)
    (H : ∀ x : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ T,
      Nonempty ((LineBundle.pullback ((relativeSpace A.X.hom).map x)).obj M ≅
        (LineBundle.pullback ((relativeSpace A.X.hom).map x)).obj N)) :
    Nonempty (M ≅ N) := by
  let f := (relativeProjection A.X.hom).app T
  let ε := (relativeSection A.X.hom (unitSection A) (unitSection_comp A)).app T
  have hε : ε ≫ f = 𝟙 T.left :=
    relativeSection_projection A.X.hom (unitSection A) (unitSection_comp A) T
  obtain ⟨B, ⟨evaluation⟩⟩ :=
    LineBundle.exists_tensorObj_iso_structureSheaf ((LineBundle.pullback ε).obj M)
  let evaluationN :
      tensorObj ((Scheme.Modules.pullback ε).obj N.obj) B.obj ≅ structureSheaf T.left :=
    (tensorFunctor T.left).mapIso
      (((LineBundle.forget T.left).mapIso e.symm).prod (Iso.refl B.obj)) ≪≫ evaluation
  let U : RigidifiedFamily A T :=
    LineBundle.normalize pullbackTensorComparisonIsIso f ε hε M B evaluation
  let V : RigidifiedFamily A T :=
    LineBundle.normalize pullbackTensorComparisonIsIso f ε hε N B evaluationN
  have hUV : (⟦U⟧ : RigidifiedClasses A T) = ⟦V⟧ := by
    apply classes_eq_of_rational A
    intro x
    obtain ⟨ex⟩ := H x
    let g := (relativeSpace A.X.hom).map x
    let D := (LineBundle.pullback f).obj B
    let E : (LineBundle.pullback g).obj (LineBundle.tensor pullbackTensorComparisonIsIso M D) ≅
        (LineBundle.pullback g).obj (LineBundle.tensor pullbackTensorComparisonIsIso N D) :=
      LineBundle.pullbackTensorObjIso pullbackTensorComparisonIsIso g M D ≪≫
        LineBundle.tensorIso pullbackTensorComparisonIsIso ex (Iso.refl _) ≪≫
        (LineBundle.pullbackTensorObjIso pullbackTensorComparisonIsIso g N D).symm
    exact Quotient.sound (RigidifiedLineBundle.nonempty_iso_of_forget_iso
      pullbackTensorComparisonIsIso ((relativeProjection A.X.hom).app _)
      (relativeSection_projection A.X.hom (unitSection A) (unitSection_comp A) _) E)
  obtain ⟨E⟩ := Quotient.exact hUV
  have he : LineBundle.isoClass pullbackTensorComparisonIsIso
      (LineBundle.tensor pullbackTensorComparisonIsIso M ((LineBundle.pullback f).obj B)) =
    LineBundle.isoClass pullbackTensorComparisonIsIso
      (LineBundle.tensor pullbackTensorComparisonIsIso N ((LineBundle.pullback f).obj B)) :=
    LineBundle.isoClass_eq_of_iso
      ((RigidifiedLineBundle.forget ε).mapIso E)
  rw [LineBundle.isoClass_tensor, LineBundle.isoClass_tensor] at he
  exact LineBundle.isoClass_eq_iff.mp (mul_right_cancel he)

omit [IsAlgClosed K] in
set_option backward.isDefEq.respectTransparency false in
/-- Restricting the addition family at a rational parameter gives translation. -/
lemma rational_addition (x : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ A.X) :
    (relativeSpace A.X.hom).map x ≫ mumfordAddition A =
      pullback.snd (𝟙 (Spec (CommRingCat.of K))) A.X.hom ≫
        (GroupScheme.translation A.toGrp x).left := by
  let W : Over (Spec (CommRingCat.of K)) :=
    Over.mk (pullback.fst (𝟙 (Spec (CommRingCat.of K))) A.X.hom)
  let d : W ⟶ A.X := Over.homMk (pullback.snd _ _) (by
    simpa [W] using
      (pullback.condition (f := 𝟙 (Spec (CommRingCat.of K))) (g := A.X.hom)).symm)
  let φ : W ⟶ mumfordProduct A := Over.homMk ((relativeSpace A.X.hom).map x) (by
    simp [relativeSpace, mumfordProduct, Category.assoc, Over.w x, W])
  have h₁ : φ ≫ mumfordFirst A = Over.mkIdTerminal.from W ≫ x := by
    apply Over.OverMorphism.ext
    simp [φ, mumfordFirst, relativeSpace, W]
  have h₂ : φ ≫ mumfordSecond A = d := by
    apply Over.OverMorphism.ext
    simp [φ, mumfordSecond, relativeSpace, d]
  have key : φ ≫ (mumfordFirst A * mumfordSecond A) =
      d ≫ GroupScheme.translation A.toGrp x := by
    rw [MonObj.comp_mul, h₁, h₂, GroupScheme.points_translation]
  exact congrArg CommaMorphism.left key

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option maxHeartbeats 800000 in
/-- Multiplication distributes a translation-invariant class on the explicit fibre product. -/
lemma multiplication_class (L : LineBundle A.X.left)
    (hL : GroupScheme.IsTranslationInvariant A.toGrp L) :
    LineBundle.pullbackHom pullbackTensorComparisonIsIso (mumfordAddition A)
        (LineBundle.isoClass pullbackTensorComparisonIsIso L) =
      LineBundle.pullbackHom pullbackTensorComparisonIsIso
          (pullback.fst A.X.hom A.X.hom) (LineBundle.isoClass pullbackTensorComparisonIsIso L) *
        LineBundle.pullbackHom pullbackTensorComparisonIsIso
          (pullback.snd A.X.hom A.X.hom) (LineBundle.isoClass pullbackTensorComparisonIsIso L) := by
  let l := LineBundle.isoClass pullbackTensorComparisonIsIso L
  let M := (LineBundle.pullback (mumfordAddition A)).obj L
  let N := LineBundle.tensor pullbackTensorComparisonIsIso
    ((LineBundle.pullback (pullback.fst A.X.hom A.X.hom)).obj L)
    ((LineBundle.pullback (pullback.snd A.X.hom A.X.hom)).obj L)
  have : IsReduced A.X.left :=
    Langlands.AlgebraicGeometry.SmoothReducedProof.isReduced_of_smooth_over_field K _ A.X.hom
  have hsection_fst : mumfordSection A ≫ pullback.fst A.X.hom A.X.hom = 𝟙 A.X.left :=
    relativeSection_projection A.X.hom (unitSection A) (unitSection_comp A) A.X
  have hsection_snd : mumfordSection A ≫ pullback.snd A.X.hom A.X.hom =
      A.X.hom ≫ unitSection A :=
    relativeSection_snd A.X.hom (unitSection A) (unitSection_comp A) A.X
  have section_iso :
      Nonempty ((LineBundle.pullback (mumfordSection A)).obj M ≅
        (LineBundle.pullback (mumfordSection A)).obj N) := by
    apply LineBundle.isoClass_eq_iff.mp
    change LineBundle.pullbackHom pullbackTensorComparisonIsIso (mumfordSection A)
        (LineBundle.pullbackHom pullbackTensorComparisonIsIso (mumfordAddition A) l) =
      LineBundle.pullbackHom pullbackTensorComparisonIsIso (mumfordSection A)
        (LineBundle.pullbackHom pullbackTensorComparisonIsIso
            (pullback.fst A.X.hom A.X.hom) l *
          LineBundle.pullbackHom pullbackTensorComparisonIsIso
            (pullback.snd A.X.hom A.X.hom) l)
    have em := (LineBundle.pullbackHom_comp_eq pullbackTensorComparisonIsIso _ _
      (mumfordSection_addition A) l).trans (LineBundle.pullbackHom_id _ l)
    have e1 := (LineBundle.pullbackHom_comp_eq pullbackTensorComparisonIsIso _ _
      hsection_fst l).trans (LineBundle.pullbackHom_id _ l)
    have e2 := (LineBundle.pullbackHom_comp_eq pullbackTensorComparisonIsIso _ _
      hsection_snd l).trans (LineBundle.pullbackHom_eq_one_of_factor
        pullbackTensorComparisonIsIso A.X.hom (unitSection A) rfl l)
    have en := (map_mul (LineBundle.pullbackHom pullbackTensorComparisonIsIso
      (mumfordSection A)) _ _).trans (congrArg₂ (· * ·) e1 e2)
    exact em.trans (en.trans (mul_one l)).symm
  obtain ⟨es⟩ := section_iso
  obtain ⟨E⟩ := iso_of_rational A M N es (fun x ↦ by
    apply LineBundle.isoClass_eq_iff.mp
    let g := (relativeSpace A.X.hom).map x
    have hfst : g ≫ pullback.fst A.X.hom A.X.hom =
        pullback.fst (𝟙 (Spec (CommRingCat.of K))) A.X.hom ≫ x.left := by
      simp [g, relativeSpace]
    have hsnd : g ≫ pullback.snd A.X.hom A.X.hom =
        pullback.snd (𝟙 (Spec (CommRingCat.of K))) A.X.hom := by
      simp [g, relativeSpace]
    have ht : LineBundle.pullbackHom pullbackTensorComparisonIsIso
        (GroupScheme.translation A.toGrp x).left l = l :=
      LineBundle.isoClass_eq_of_iso (hL x).some
    let : Unique (Over.mk (𝟙 (Spec (CommRingCat.of K)))).left :=
      inferInstanceAs (Unique (Spec (CommRingCat.of K)))
    change LineBundle.pullbackHom pullbackTensorComparisonIsIso g
        (LineBundle.pullbackHom pullbackTensorComparisonIsIso (mumfordAddition A) l) =
      LineBundle.pullbackHom pullbackTensorComparisonIsIso g
        (LineBundle.pullbackHom pullbackTensorComparisonIsIso
            (pullback.fst A.X.hom A.X.hom) l *
          LineBundle.pullbackHom pullbackTensorComparisonIsIso
            (pullback.snd A.X.hom A.X.hom) l)
    have em := (LineBundle.pullbackHom_comp_eq pullbackTensorComparisonIsIso _ _
      (rational_addition A x) l).trans
        ((LineBundle.pullbackHom_comp pullbackTensorComparisonIsIso _ _ l).symm.trans
          (congrArg (LineBundle.pullbackHom pullbackTensorComparisonIsIso
            (pullback.snd (𝟙 (Spec (CommRingCat.of K))) A.X.hom)) ht))
    have e1 := (LineBundle.pullbackHom_comp_eq pullbackTensorComparisonIsIso _ _
      hfst l).trans (LineBundle.pullbackHom_eq_one_of_factor
        pullbackTensorComparisonIsIso _ x.left rfl l)
    have e2 := LineBundle.pullbackHom_comp_eq pullbackTensorComparisonIsIso _ _ hsnd l
    have en := (map_mul (LineBundle.pullbackHom pullbackTensorComparisonIsIso g) _ _).trans
      (congrArg₂ (· * ·) e1 e2)
    exact em.trans (en.trans (one_mul _)).symm)
  exact LineBundle.isoClass_eq_of_iso E

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The multiplication class identity on the categorical product. -/
lemma categorical_multiplication_class (L : LineBundle A.X.left)
    (hL : GroupScheme.IsTranslationInvariant A.toGrp L) :
    let p1 : A.X ⨯ A.X ⟶ A.X := Limits.prod.fst
    let p2 : A.X ⨯ A.X ⟶ A.X := Limits.prod.snd
    LineBundle.pullbackHom pullbackTensorComparisonIsIso (p1 * p2).left
        (LineBundle.isoClass pullbackTensorComparisonIsIso L) =
      LineBundle.pullbackHom pullbackTensorComparisonIsIso p1.left
          (LineBundle.isoClass pullbackTensorComparisonIsIso L) *
        LineBundle.pullbackHom pullbackTensorComparisonIsIso p2.left
          (LineBundle.isoClass pullbackTensorComparisonIsIso L) := by
  let P := A.X ⨯ A.X
  let p1 : P ⟶ A.X := Limits.prod.fst
  let p2 : P ⟶ A.X := Limits.prod.snd
  let l := LineBundle.isoClass pullbackTensorComparisonIsIso L
  let φ : P ⟶ mumfordProduct A := Over.homMk
    (pullback.lift p1.left p2.left ((Over.w p1).trans (Over.w p2).symm)) (by
      change pullback.lift _ _ _ ≫ (pullback.fst _ _ ≫ A.X.hom) = P.hom
      rw [pullback.lift_fst_assoc]
      exact Over.w p1)
  have h1 : φ ≫ mumfordFirst A = p1 := by
    apply Over.OverMorphism.ext
    simp [φ, mumfordFirst]
  have h2 : φ ≫ mumfordSecond A = p2 := by
    apply Over.OverMorphism.ext
    simp [φ, mumfordSecond]
  have hm : φ.left ≫ mumfordAddition A = (p1 * p2).left :=
    congrArg CommaMorphism.left
      ((MonObj.comp_mul φ _ _).trans (congrArg₂ (· * ·) h1 h2))
  have h1' : φ.left ≫ pullback.fst A.X.hom A.X.hom = p1.left :=
    congrArg CommaMorphism.left h1
  have h2' : φ.left ≫ pullback.snd A.X.hom A.X.hom = p2.left :=
    congrArg CommaMorphism.left h2
  have H := congrArg (LineBundle.pullbackHom pullbackTensorComparisonIsIso φ.left)
    (multiplication_class A L hL)
  have em := LineBundle.pullbackHom_comp_eq pullbackTensorComparisonIsIso _ _ hm l
  have e1 := LineBundle.pullbackHom_comp_eq pullbackTensorComparisonIsIso _ _ h1' l
  have e2 := LineBundle.pullbackHom_comp_eq pullbackTensorComparisonIsIso _ _ h2' l
  have en := (map_mul (LineBundle.pullbackHom pullbackTensorComparisonIsIso φ.left) _ _).trans
    (congrArg₂ (· * ·) e1 e2)
  exact em.symm.trans (H.trans en)

end Langlands.AbelianScheme.TranslationInvariantIdentities

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Ordinary rational-point translation invariance gives both actual pullback identities. -/
theorem algClosedFieldTranslationInvariantPullbackIdentities :
    AlgClosedFieldTranslationInvariantPullbackIdentitiesStatement.{u} := by
  intro K _ _ A L hL
  let P := A.X ⨯ A.X
  let p1 : P ⟶ A.X := Limits.prod.fst
  let p2 : P ⟶ A.X := Limits.prod.snd
  let m : P ⟶ A.X := p1 * p2
  let i : A.X ⟶ A.X := (𝟙 A.X)⁻¹
  let l := LineBundle.isoClass pullbackTensorComparisonIsIso L
  have hm : LineBundle.pullbackHom pullbackTensorComparisonIsIso m.left l =
      LineBundle.pullbackHom pullbackTensorComparisonIsIso p1.left l *
        LineBundle.pullbackHom pullbackTensorComparisonIsIso p2.left l :=
    TranslationInvariantIdentities.categorical_multiplication_class A L hL
  constructor
  · obtain ⟨e⟩ := LineBundle.isoClass_eq_iff.mp hm
    exact ⟨(LineBundle.forget P.left).mapIso e⟩
  · let j : A.X ⟶ P := Limits.prod.lift (𝟙 A.X) i
    have hj1 : j ≫ p1 = 𝟙 A.X := Limits.prod.lift_fst _ _
    have hj2 : j ≫ p2 = i := Limits.prod.lift_snd _ _
    have hjm : j ≫ m = 1 := by
      change j ≫ (p1 * p2) = _
      rw [MonObj.comp_mul, hj1, hj2]
      exact mul_inv_cancel (𝟙 A.X)
    have hunit : A.X.hom ≫ unitSection A = (1 : A.X ⟶ A.X).left := by
      have e : Over.mkIdTerminal.from A.X ≫
          (1 : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ A.X) = (1 : A.X ⟶ A.X) := by
        simp
      simpa only [Over.comp_left, Over.mkIdTerminal_from_left, unitSection] using
        congrArg CommaMorphism.left e
    have em := (LineBundle.pullbackHom_comp_eq pullbackTensorComparisonIsIso _ _
      (congrArg CommaMorphism.left hjm) l).trans
        (LineBundle.pullbackHom_eq_one_of_factor pullbackTensorComparisonIsIso
          A.X.hom (unitSection A) hunit l)
    have e1 := (LineBundle.pullbackHom_comp_eq pullbackTensorComparisonIsIso _ _
      (congrArg CommaMorphism.left hj1) l).trans
        (LineBundle.pullbackHom_id pullbackTensorComparisonIsIso l)
    have e2 := LineBundle.pullbackHom_comp_eq pullbackTensorComparisonIsIso _ _
      (congrArg CommaMorphism.left hj2) l
    have en := (map_mul (LineBundle.pullbackHom pullbackTensorComparisonIsIso j.left) _ _).trans
      (congrArg₂ (· * ·) e1 e2)
    have H := congrArg (LineBundle.pullbackHom pullbackTensorComparisonIsIso j.left) hm
    have hi : l * LineBundle.pullbackHom pullbackTensorComparisonIsIso i.left l = 1 :=
      en.symm.trans (H.symm.trans em)
    obtain ⟨e⟩ := LineBundle.isoClass_eq_iff.mp hi
    exact ⟨(LineBundle.forget A.X.left).mapIso e⟩

end Langlands.AbelianScheme
