import Langlands.AlgebraicGeometry.Picard.MumfordProductEulerCharacteristic
import Langlands.AlgebraicGeometry.Picard.SquareSecondProjectionSupport
import Langlands.AlgebraicGeometry.Picard.TranslationInvariantCohomologyVanishingProof
import Langlands.AlgebraicGeometry.Picard.AlgClosedFieldAmpleTranslationStabilizerFiniteProof
import Langlands.AlgebraicGeometry.Picard.LineBundleIsoClassGroup
import Langlands.AbelianScheme.FieldTheoremOfTheSquareStatement
import Langlands.AlgebraicGeometry.Modules.PullbackTensorProof

/-! # Finite support of the second-projection direct images of `m^* H ⊗ p₁^* N` -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules
open Langlands.AlgebraicGeometry.Modules Langlands.GroupScheme LineBundle

/-- The isomorphism class of a line bundle, for the proved tensor preservation. -/
local notation "cls" => LineBundle.isoClass pullbackTensorComparisonIsIso

/-- Pullback of isomorphism classes, for the proved tensor preservation. -/
local notation "pb" => LineBundle.pullbackHom pullbackTensorComparisonIsIso

section Translation

variable {S : Scheme.{u}} (G : GroupScheme S)

/-- Translation by `y` followed by translation by `x` is translation by `x * y`. -/
lemma translation_comp_translation (x y : Over.mk (𝟙 S) ⟶ G.X) :
    translation G y ≫ translation G x = translation G (x * y) := by
  rw [points_translation]
  simp only [translation, MonObj.comp_mul, mul_assoc]

end Translation

section Inclusion

variable {S : Scheme.{u}} (A : AbelianScheme S)

/-- The inclusion `z ↦ (z, x)` of `A` into its self-product, as a morphism over the base. -/
def mumfordSecondInclusionOver (x : Over.mk (𝟙 S) ⟶ A.X) : A.X ⟶ mumfordProduct A :=
  mumfordProductLift A (𝟙 A.X) (Over.mkIdTerminal.from A.X ≫ x)

lemma mumfordSecondInclusionOver_left (x : Over.mk (𝟙 S) ⟶ A.X) :
    (mumfordSecondInclusionOver A x).left = squareSecondInclusion A.X.hom x.left x.w := by
  apply pullback.hom_ext
  · simp [mumfordSecondInclusionOver, mumfordProductLift]
    exact pullback.lift_fst _ _ _
  · simp [mumfordSecondInclusionOver, mumfordProductLift]
    exact pullback.lift_snd _ _ _

/-- The inclusion `z ↦ (z, x)` followed by the addition map is translation by `x`. -/
lemma squareSecondInclusion_mumfordAddition (x : Over.mk (𝟙 S) ⟶ A.X) :
    squareSecondInclusion A.X.hom x.left x.w ≫ mumfordAddition A =
      (translation A.toGrp x).left := by
  rw [← mumfordSecondInclusionOver_left, mumfordAddition, ← Over.comp_left, MonObj.comp_mul,
    mumfordSecondInclusionOver, mumfordProductLift_first, mumfordProductLift_second,
    translation, mul_comm]

end Inclusion

section Support

variable {K : Type u} [Field K] [IsAlgClosed K] (A : AbelianScheme (Spec (CommRingCat.of K)))

omit [IsAlgClosed K] in
/-- A tensor inverse `N` of `H` has the inverse isomorphism class. -/
lemma isoClass_eq_inv_of_tensor (H N : LineBundle A.X.left)
    (evaluation : tensorObj H.obj N.obj ≅ structureSheaf A.X.left) :
    cls N = (cls H)⁻¹ := by
  let e : LineBundle.tensor pullbackTensorComparisonIsIso H N ≅ LineBundle.trivial A.X.left :=
    ObjectProperty.isoMk _ evaluation
  exact eq_inv_of_mul_eq_one_right (isoClass_eq_of_iso e)

omit [IsAlgClosed K] in
/-- By the theorem of the square, `t_x^* H ⊗ N` is translation invariant when `N` is a
tensor inverse of `H`. -/
lemma isTranslationInvariant_translation_tensor (square : FieldTheoremOfTheSquareStatement.{u})
    (H N : LineBundle A.X.left) (evaluation : tensorObj H.obj N.obj ≅ structureSheaf A.X.left)
    (x : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ A.X) :
    IsTranslationInvariant A.toGrp (LineBundle.tensor pullbackTensorComparisonIsIso
      ((LineBundle.pullback (translation A.toGrp x).left).obj H) N) := by
  intro y
  obtain ⟨e⟩ := square K A.toGrp A.smooth A.proper A.geometricallyConnected H x y
  let e' : LineBundle.tensor pullbackTensorComparisonIsIso
        ((LineBundle.pullback (translation A.toGrp (x * y)).left).obj H) H ≅
      LineBundle.tensor pullbackTensorComparisonIsIso
        ((LineBundle.pullback (translation A.toGrp x).left).obj H)
        ((LineBundle.pullback (translation A.toGrp y).left).obj H) :=
    ObjectProperty.isoMk _ e
  have hsq : pb (translation A.toGrp (x * y)).left (cls H) * cls H =
      pb (translation A.toGrp x).left (cls H) * pb (translation A.toGrp y).left (cls H) :=
    isoClass_eq_of_iso e'
  have hyx : (translation A.toGrp y).left ≫ (translation A.toGrp x).left =
      (translation A.toGrp (x * y)).left := by
    rw [← Over.comp_left, translation_comp_translation]
  refine (isoClass_eq_iff (preservation := pullbackTensorComparisonIsIso)).mp ?_
  change pb (translation A.toGrp y).left (pb (translation A.toGrp x).left (cls H) * cls N) =
    pb (translation A.toGrp x).left (cls H) * cls N
  rw [map_mul, pullbackHom_comp_eq _ _ _ hyx, isoClass_eq_inv_of_tensor A H N evaluation,
    map_inv, ← div_eq_mul_inv, ← div_eq_mul_inv, div_eq_div_iff_mul_eq_mul]
  exact hsq

/-- For `H` ample and `N` a tensor inverse of `H`, every higher direct image of
`m^* H ⊗ p₁^* N` along the second projection of the self-product has finite closed support,
given the theorem of the square. -/
theorem hasFiniteClosedSupport_higherDirectImage_mumfordAddition_tensor_fst
    (square : FieldTheoremOfTheSquareStatement.{u})
    (H N : LineBundle A.X.left) (hH : H.IsAmple)
    (evaluation : tensorObj H.obj N.obj ≅ structureSheaf A.X.left) (n : ℕ) :
    HasFiniteClosedSupport
      ((DerivedSections.higherDirectImage (pullback.snd A.X.hom A.X.hom) n).obj
        (tensorObj ((Scheme.Modules.pullback (mumfordAddition A)).obj H.obj)
          ((Scheme.Modules.pullback (pullback.fst A.X.hom A.X.hom)).obj N.obj))) := by
  -- the translations fixing `H`
  let F : Set (Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ A.X) :=
    {x | Nonempty ((LineBundle.pullback (translation A.toGrp x).left).obj H ≅ H)}
  have hF : F.Finite :=
    Set.finite_coe_iff.mp (algClosedFieldAmpleTranslationStabilizerFinite K A H hH)
  refine squareSecondProjectionSupport K A
    (LineBundle.tensor pullbackTensorComparisonIsIso
      ((LineBundle.pullback (mumfordAddition A)).obj H)
      ((LineBundle.pullback (pullback.fst A.X.hom A.X.hom)).obj N)) F hF ?_ n
  intro x hx m
  -- the restriction to `A × {x}` is `t_x^* H ⊗ N`
  have he : Nonempty ((LineBundle.pullback (squareSecondInclusion A.X.hom x.left x.w)).obj
      (LineBundle.tensor pullbackTensorComparisonIsIso
        ((LineBundle.pullback (mumfordAddition A)).obj H)
        ((LineBundle.pullback (pullback.fst A.X.hom A.X.hom)).obj N)) ≅
      LineBundle.tensor pullbackTensorComparisonIsIso
        ((LineBundle.pullback (translation A.toGrp x).left).obj H) N) := by
    refine (isoClass_eq_iff (preservation := pullbackTensorComparisonIsIso)).mp ?_
    change pb (squareSecondInclusion A.X.hom x.left x.w)
        (HMul.hMul (α := IsoClasses pullbackTensorComparisonIsIso (pullback A.X.hom A.X.hom))
          (β := IsoClasses pullbackTensorComparisonIsIso (pullback A.X.hom A.X.hom))
          (pb (mumfordAddition A) (cls H)) (pb (pullback.fst A.X.hom A.X.hom) (cls N))) =
      pb (translation A.toGrp x).left (cls H) * cls N
    rw [map_mul, pullbackHom_comp_eq _ _ _ (squareSecondInclusion_mumfordAddition A x),
      pullbackHom_comp_eq _ _ _ (squareSecondInclusion_fst A.X.hom x.left x.w), pullbackHom_id]
  obtain ⟨e⟩ := he
  refine (algClosedFieldTranslationInvariantCohomologyVanishing K A _
    (isTranslationInvariant_translation_tensor A square H N evaluation x) ?_ m).of_iso
    ((DerivedSections.relativeCohomology A.X.hom m).mapIso ((LineBundle.forget _).mapIso e))
  -- outside `F` the restriction is not trivial
  rintro ⟨d⟩
  apply hx
  show Nonempty ((LineBundle.pullback (translation A.toGrp x).left).obj H ≅ H)
  refine (isoClass_eq_iff (preservation := pullbackTensorComparisonIsIso)).mp ?_
  have h₁ : pb (translation A.toGrp x).left (cls H) * cls N = 1 := isoClass_eq_of_iso d
  rw [isoClass_eq_inv_of_tensor A H N evaluation, mul_inv_eq_one] at h₁
  exact h₁

end Support

end Langlands.AbelianScheme
