import Langlands.AbelianScheme.AlgClosedFieldAmpleCubeSeparationReduction
import Langlands.AbelianScheme.CompleteLinearSystemIsogeny
import Langlands.AbelianScheme.FieldAbelianSchemeGeometry
import Langlands.AbelianScheme.FiniteTranslationPeriods
import Langlands.AbelianScheme.FiniteTranslationQuotientFactorization

/-! # Point and tangent separation by the cube of an ample bundle -/

noncomputable section

universe u v

open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
  AlgebraicGeometry
open Langlands.SchemeModule Langlands.AlgebraicGeometry Langlands.AlgebraicGeometry.Picard
  Langlands.AlgebraicGeometry.LinearSystem Langlands.AlgebraicGeometry.Modules.DerivedSections
  Langlands.AlgebraicGeometry.PointTopology Langlands.GroupScheme.SeparatingLineBundle
open scoped CategoryTheory.MonObj

namespace Langlands.AbelianScheme

variable {K : Type u} [Field K] [IsAlgClosed K]

private lemma dense_rational_family_in_open (A : AbelianScheme (Spec (CommRingCat.of K)))
    (U : A.X.left.Opens) (hU : (U : Set A.X.left).Nonempty) :
    HasDenseRationalPointFamily (I := {y : RationalPoint K A.X //
      y.left (IsLocalRing.closedPoint K) ∈ U}) Subtype.val := by
  have : IsIntegral A.X.left := field_isIntegral A
  apply dense_iff_inter_open.mpr
  intro V hV hne
  have hVU : (V ∩ (U : Set A.X.left)).Nonempty :=
    (U.isOpen.dense hU).inter_open_nonempty V hV hne
  let W : A.X.left.Opens := ⟨V ∩ (U : Set A.X.left), hV.inter U.isOpen⟩
  obtain ⟨y, hy⟩ := ClosedRationalPoints.exists_rationalPoint_mem (X := A.X) W hVU
  exact ⟨y.left (IsLocalRing.closedPoint K), hy.1,
    Set.mem_iUnion.mpr ⟨⟨y, hy.2⟩, Set.mem_range_self _⟩⟩

private lemma exists_completeSystem_of_no_rational_basePoints
    (A : AbelianScheme (Spec (CommRingCat.of K))) (N : LineBundle A.X.left)
    (hN : ∀ y : RationalPoint K A.X, ∃ s : GlobalSections N.obj, ¬ VanishesAlong N y.left s) :
    Nonempty (CompleteGeneratingSystem A.X.hom N) := by
  have : IsIntegral A.X.left := field_isIntegral A
  have : Module.Finite K ((relativeCohomology A.X.hom 0).obj N.obj) :=
    (lineBundle_hasFiniteCohomology A N).1 0
  have : Module.Finite K ((relativeGlobalSections A.X.hom).obj N.obj) :=
    Module.Finite.equiv ((relativeCohomologyZeroIso A.X.hom).app N.obj).toLinearEquiv
  exact exists_completeGeneratingSystem A.X.hom N fun y hy ↦ hN (Over.homMk y hy)

private lemma eq_one_of_completeSystem_period
    (A : AbelianScheme (Spec (CommRingCat.of K))) {N : LineBundle A.X.left}
    (C : CompleteGeneratingSystem A.X.hom N) (hN : N.IsAmple)
    {J : Type v} (p : J → RationalPoint K A.X) (hp : HasDenseRationalPointFamily p)
    {T : Over (Spec (CommRingCat.of K))} (x : T ⟶ A.X)
    (h : ∀ k, x.left ≫ (GroupScheme.translation A.toGrp (p k)).left ≫ C.map =
      T.hom ≫ (p k).left ≫ C.map) : x = 1 := by
  have : IsIntegral A.X.left := field_isIntegral A
  let W := Over.mk (projectiveSpaceToSpec K C.n)
  let F : A.X ⟶ W := Over.homMk C.map C.map_toSpec
  have : IsSeparated W.hom := inferInstanceAs (IsSeparated (projectiveSpaceToSpec K C.n))
  have : IsFinite F.left := C.isFinite_map_of_isAmple hN
  obtain ⟨H, i, hi, hH, hinv, hrep⟩ := exists_finiteTranslationPeriods A F p hp
  obtain ⟨a, ha⟩ := (hrep T x).1 (fun k ↦ Over.OverMorphism.ext (h k))
  obtain ⟨B, q, b, hqF, hqFl, hqS, hfac, hkill⟩ := finiteTranslationQuotientFactorization A i F hinv
  have hcomp : q.left ≫ b.left = C.map := congrArg (fun m ↦ m.left) hfac
  have : IsIso q.left := isIso_of_completeLinearSystem_factors C hN q b.left (Over.w b) hcomp
  have hi1 : i.hom.hom = (1 : H.X ⟶ A.X) := by
    apply Over.OverMorphism.ext
    apply (cancel_mono q.left).mp
    exact congrArg (fun m ↦ m.left) hkill
  rw [← ha, hi1, MonObj.comp_one]

/-- A generic simultaneous vanishing implication for the complete ample system
forces the rational translation to be the unit. -/
theorem ampleGenericTranslationVanishing : AmpleGenericTranslationVanishingStatement.{u} := by
  intro K _ _ A N hN hgen x U hU h
  obtain ⟨C⟩ := exists_completeSystem_of_no_rational_basePoints A N hgen
  let p : {y : RationalPoint K A.X // y.left (IsLocalRing.closedPoint K) ∈ U} →
      RationalPoint K A.X := Subtype.val
  apply eq_one_of_completeSystem_period A C hN p (dense_rational_family_in_open A U hU) x
  intro k
  let y := p k
  have hxy := C.comp_map_eq_of_rational_vanishing (Over.w y) (Over.w (x * y)) (h y k.2)
  change x.left ≫ (GroupScheme.translation A.toGrp y).left ≫ C.map = (𝟙 _) ≫ y.left ≫ C.map
  rw [← Category.assoc, left_comp_translation, Category.id_comp, mul_comm y x]
  exact hxy.symm

/-- The same period argument on the dual numbers detects a nonconstant
infinitesimal translation. -/
theorem ampleGenericTangentVanishing : AmpleGenericTangentVanishingStatement.{u} := by
  intro K _ _ A N hN hgen t ht U hU h
  obtain ⟨C⟩ := exists_completeSystem_of_no_rational_basePoints A N hgen
  let p : {y : RationalPoint K A.X // y.left (IsLocalRing.closedPoint K) ∈ U} →
      RationalPoint K A.X := Subtype.val
  let T := Over.mk (dualNumberProjection K)
  let τ : T ⟶ A.X := Over.homMk t ht.1.1
  have hτ : τ = 1 := by
    apply eq_one_of_completeSystem_period A C hN p (dense_rational_family_in_open A U hU) τ
    intro k
    let y := p k
    let a := (GroupScheme.translation A.toGrp y).left
    have ht' : IsTangentVectorAt A.X.hom y.left (t ≫ a) := by
      constructor
      · rw [Category.assoc, show a ≫ A.X.hom = A.X.hom from Over.w (GroupScheme.translation A.toGrp y)]
        exact ht.1.1
      · change dualNumberAugmentation K ≫ t ≫ a = y.left
        rw [← Category.assoc, ht.1.2]
        change (1 : RationalPoint K A.X).left ≫ (GroupScheme.translation A.toGrp y).left = y.left
        rw [left_comp_translation, mul_one]
    calc
      τ.left ≫ a ≫ C.map = (t ≫ a) ≫ C.map := (Category.assoc _ _ _).symm
      _ = (dualNumberProjection K ≫ y.left) ≫ C.map :=
        C.comp_map_eq_of_dualNumber_vanishing (Over.w y) ht' (h y k.2)
      _ = T.hom ≫ y.left ≫ C.map := Category.assoc _ _ _
  have hconst : τ = toUnit T ≫ (1 : RationalPoint K A.X) :=
    hτ.trans (MonObj.comp_one (toUnit T)).symm
  exact ht.2 (congrArg (fun m ↦ m.left) hconst)

/-- Lefschetz separation by the complete tensor cube of any ample line bundle
on an abelian variety over an algebraically closed field. -/
theorem algClosedFieldAmpleCubeSeparation : AlgClosedFieldAmpleCubeSeparationStatement.{u} :=
  algClosedFieldAmpleCubeSeparation_of_generic ampleGenericTranslationVanishing ampleGenericTangentVanishing

end Langlands.AbelianScheme
