import Langlands.GroupScheme.Descent.FiniteCoefficientFlatAffineHom
import Langlands.GroupScheme.Descent.FiniteCoefficientHomProperties
import Langlands.GroupScheme.FppfQuotientComparison

/-! # Finite coefficient models of affine fppf group quotients -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000

namespace Langlands.GroupScheme.Descent.FiniteCoefficient

open Langlands.AlgebraicGeometry
open AffineLimit SchemeLimitModel.Geometry
open Langlands.AlgebraicGeometry.AlgebraicSpace

private theorem quotientFlat_structural_descent :
    SchemeStructuralPropertyDescent.{u} @Flat := by
  intro I _ _ D S X Y _ _ t a b f w _ _ _ _ _ _ c hc p hp
  have : LocallyOfFinitePresentation (f ≫ b) := by rw [w]; infer_instance
  have : QuasiCompact (f ≫ b) := by rw [w]; infer_instance
  have : QuasiSeparated (f ≫ b) := by rw [w]; infer_instance
  have : LocallyOfFinitePresentation f := locallyOfFinitePresentation_of_comp f b
  have : QuasiCompact f := QuasiCompact.of_comp f b
  have : QuasiSeparated f := QuasiSeparated.of_comp f b
  exact relativeFlatDescent D t a b f w c hc p hp

/-- Flatness and surjectivity of a finite-presentation diagram descend
together to one finite coefficient stage. -/
theorem flatSurjective_structural_descent :
    SchemeStructuralPropertyDescent.{u} (@Flat ⊓ @Surjective) := by
  intro I _ _ D S X Y _ _ t a b f w _ _ _ _ _ _ c hc p hp
  constructor
  · intro h
    obtain ⟨i, hi⟩ := (quotientFlat_structural_descent D t a b f w c hc p hp).mp h.1
    obtain ⟨j, hj⟩ :=
      (surjective_schemeStructuralPropertyDescent D t a b f w c hc p hp).mp h.2
    obtain ⟨k, ki, kj, -⟩ := IsCofilteredOrEmpty.cone_objs i j
    exact ⟨k,
      MorphismProperty.of_isPullback
        (morphismDiagram_cartesian a b f w D t ki).flip hi,
      MorphismProperty.of_isPullback
        (morphismDiagram_cartesian a b f w D t kj).flip hj⟩
  · rintro ⟨i, hi⟩
    exact MorphismProperty.of_isPullback
      (coneMorphism_cartesian a b f w D t c p hp i).flip hi

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    {G H : GroupScheme (Spec (CommRingCat.of A))}

/-- Every isomorphism-invariant property of the original map holds for
the recovered model map over the original algebra. -/
theorem FlatAffineHomModel.property_over_algebra
    (P : MorphismProperty Scheme.{u}) [P.RespectsIso]
    {f : G ⟶ H} (D : FlatAffineHomModel R A f) (hf : P f.hom.hom.left) :
    P ((baseChange (Spec.algebraMap D.coefficients A)).map D.hom).hom.hom.left := by
  have he : (baseChange (Spec.algebraMap D.coefficients A)).map D.hom =
      D.sourceIso.inv ≫ f ≫ D.targetIso.hom := by
    rw [← D.comm, Iso.inv_hom_id_assoc]
  rw [he]
  change P (D.sourceIso.inv.hom.hom.left ≫ f.hom.hom.left ≫
    D.targetIso.hom.hom.hom.left)
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in
  rw [P.cancel_left_of_respectsIso, P.cancel_right_of_respectsIso]
  exact hf

variable (R A)

/-- An affine flat finite-presentation group diagram with a flat surjective
quotient map over the common finite coefficient subalgebra. -/
structure FlatAffineQuotientModel (f : G ⟶ H) extends FlatAffineHomModel R A f where
  homFlat : Flat hom.hom.hom.left
  homSurjective : Surjective hom.hom.hom.left

variable {R A}

/-- A simultaneous model can be enlarged until its quotient map is flat
and surjective, retaining its group models and recovery square. -/
theorem FlatAffineHomModel.exists_flatSurjective
    {f : G ⟶ H} [Flat f.hom.hom.left] [Surjective f.hom.hom.left]
    (D : FlatAffineHomModel R A f) :
    ∃ E : FlatAffineQuotientModel R A f, D.coefficients ≤ E.coefficients := by
  let := D.sourceAffine
  let := D.sourceFinitePresentation
  let := D.targetAffine
  let := D.targetFinitePresentation
  obtain ⟨T, hT, hp⟩ := exists_fg_hom_property
    (@Flat ⊓ @Surjective) flatSurjective_structural_descent
    D.coefficients A D.hom
      (D.property_over_algebra _ ⟨inferInstance, inferInstance⟩)
  refine ⟨{ toFlatAffineHomModel := D.enlarge T hT
            homFlat := hp.1
            homSurjective := hp.2 }, ?_⟩
  intro x hx
  exact T.algebraMap_mem ⟨x, hx⟩

variable (R A)

/-- An affine fppf group quotient descends with flatness and surjectivity
to finitely generated coefficients containing any specified finite set. -/
theorem exists_flatAffineQuotientModel
    (f : G ⟶ H) [IsAffine G.X.left] [Flat G.X.hom]
    [LocallyOfFinitePresentation G.X.hom] [IsAffine H.X.left] [Flat H.X.hom]
    [LocallyOfFinitePresentation H.X.hom]
    [Flat f.hom.hom.left] [Surjective f.hom.hom.left] (s : Finset A) :
    ∃ D : FlatAffineQuotientModel R A f, (s : Set A) ⊆ D.coefficients := by
  obtain ⟨D, hs⟩ := exists_flatAffineHomModel R A f s
  obtain ⟨E, hDE⟩ := D.exists_flatSurjective
  exact ⟨E, hs.trans hDE⟩

/-- Choose a finite coefficient model of an affine fppf group quotient. -/
def flatAffineQuotientModel
    (f : G ⟶ H) [IsAffine G.X.left] [Flat G.X.hom]
    [LocallyOfFinitePresentation G.X.hom] [IsAffine H.X.left] [Flat H.X.hom]
    [LocallyOfFinitePresentation H.X.hom]
    [Flat f.hom.hom.left] [Surjective f.hom.hom.left] :
    FlatAffineQuotientModel R A f :=
  Classical.choose (exists_flatAffineQuotientModel R A f ∅)

variable {R A}

/-- The model quotient is locally of finite presentation. -/
theorem FlatAffineQuotientModel.homFinitePresentation
    {f : G ⟶ H} (D : FlatAffineQuotientModel R A f) :
    LocallyOfFinitePresentation D.hom.hom.hom.left := by
  let := D.sourceFinitePresentation
  let := D.targetAffine
  let := D.targetFinitePresentation
  have : LocallyOfFinitePresentation (D.hom.hom.hom.left ≫ D.target.X.hom) := by
    rw [Over.w]
    infer_instance
  exact locallyOfFinitePresentation_of_comp D.hom.hom.hom.left D.target.X.hom

/-- The exact sequence over the coefficient ring uses the actual kernel,
so no separate all-test exactness assertion must be descended. -/
theorem FlatAffineQuotientModel.isFppfQuotient_kernel
    {f : G ⟶ H} (D : FlatAffineQuotientModel R A f) :
    RelativeRoot.IsFppfQuotient (SubgroupFunctor.range (kernelι D.hom)) D.hom :=
  ⟨D.homFlat, D.homSurjective, D.homFinitePresentation, rfl⟩

/-- The model kernel is flat over its coefficient ring. -/
theorem FlatAffineQuotientModel.kernelFlat
    {f : G ⟶ H} (D : FlatAffineQuotientModel R A f) :
    Flat (kernel D.hom).X.hom :=
  MorphismProperty.of_isPullback (kernel_isPullback_scheme D.hom) D.homFlat

/-- The model kernel is locally of finite presentation over the coefficient ring. -/
theorem FlatAffineQuotientModel.kernelFinitePresentation
    {f : G ⟶ H} (D : FlatAffineQuotientModel R A f) :
    LocallyOfFinitePresentation (kernel D.hom).X.hom :=
  MorphismProperty.of_isPullback (kernel_isPullback_scheme D.hom) D.homFinitePresentation

/-- The model kernel is affine over its coefficient ring. -/
theorem FlatAffineQuotientModel.kernelAffine
    {f : G ⟶ H} (D : FlatAffineQuotientModel R A f) :
    IsAffineHom (kernel D.hom).X.hom := by
  let := D.sourceAffine
  let := D.targetAffine
  rw [← Over.w (kernelι D.hom).hom.hom]
  infer_instance

end Langlands.GroupScheme.Descent.FiniteCoefficient
