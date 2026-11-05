import Langlands.Algebra.RenardEndomorphismLocalizationInitialityStatements

/-! # Proof of initiality of the explicit and chosen endomorphism-localization arrows -/

set_option autoImplicit false

universe u v w

open CategoryTheory Limits Langlands.Algebra.PolynomialEndomorphism

noncomputable section

namespace Langlands.Renard.EndomorphismLocalization.ChosenComparison

variable {R : Type u} [CommRing R]

/-- The original linear map underlying a morphism out of the raised pair. -/
def baseMap {A : EndomorphismCat.{u, v} R} {B : InvertibleEndomorphismCat.{u, max u v w} R}
    (g : (raisedFunctor.{u, v, w} R).obj A ⟶
      (invertibleEndomorphismInclusion.{u, max u v w} R).obj B) :
    A.a →ₗ[R] B.obj.a :=
  g.f.hom.comp (ULift.moduleEquiv (R := R) (M := A.a)).symm.toLinearMap

theorem baseMap_intertwines {A : EndomorphismCat.{u, v} R}
    {B : InvertibleEndomorphismCat.{u, max u v w} R}
    (g : (raisedFunctor.{u, v, w} R).obj A ⟶
      (invertibleEndomorphismInclusion.{u, max u v w} R).obj B) (x : A.a) :
    baseMap g (endomorphism R A x) = endomorphism R B.obj (baseMap g x) :=
  (intertwining_iff R _ _ g.f).mp g.h (ULift.up x)

/-- The published linear factor, bundled as a morphism of invertible pairs. -/
def explicitFactor (A : EndomorphismCat.{u, v} R)
    (B : InvertibleEndomorphismCat.{u, max u v w} R)
    (g : (raisedFunctor.{u, v, w} R).obj A ⟶
      (invertibleEndomorphismInclusion.{u, max u v w} R).obj B) :
    (explicitFunctor.{u, v, w} R).obj A ⟶ B :=
  ObjectProperty.homMk
    { f := ModuleCat.ofHom ((factor (endomorphism R A) (endomorphism R B.obj) B.property
          (baseMap g) (baseMap_intertwines g)).comp
          (ULift.moduleEquiv (R := R) (M := Localized (endomorphism R A))).toLinearMap)
      h := (intertwining_iff R _ _ _).mpr (fun z =>
        factor_intertwines (endomorphism R A) (endomorphism R B.obj) B.property
          (baseMap g) (baseMap_intertwines g) z.down) }

theorem explicitFactor_fac (A : EndomorphismCat.{u, v} R)
    (B : InvertibleEndomorphismCat.{u, max u v w} R)
    (g : (raisedFunctor.{u, v, w} R).obj A ⟶
      (invertibleEndomorphismInclusion.{u, max u v w} R).obj B) :
    (explicitArrow.{u, v, w} R).app A ≫
      (invertibleEndomorphismInclusion.{u, max u v w} R).map (explicitFactor A B g) = g := by
  apply Endofunctor.Algebra.Hom.ext
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  exact LinearMap.congr_fun (factor_comp_iota (endomorphism R A) (endomorphism R B.obj)
    B.property (baseMap g) (baseMap_intertwines g)) x.down

theorem explicitFactor_unique (A : EndomorphismCat.{u, v} R)
    (B : InvertibleEndomorphismCat.{u, max u v w} R)
    (g : (raisedFunctor.{u, v, w} R).obj A ⟶
      (invertibleEndomorphismInclusion.{u, max u v w} R).obj B)
    (h : (explicitFunctor.{u, v, w} R).obj A ⟶ B)
    (hh : (explicitArrow.{u, v, w} R).app A ≫
      (invertibleEndomorphismInclusion.{u, max u v w} R).map h = g) :
    h = explicitFactor A B g := by
  have key : h.hom.f.hom.comp
      (ULift.moduleEquiv (R := R) (M := Localized (endomorphism R A))).symm.toLinearMap =
      factor (endomorphism R A) (endomorphism R B.obj) B.property
        (baseMap g) (baseMap_intertwines g) :=
    factor_unique (endomorphism R A) (endomorphism R B.obj) B.property
      (baseMap g) (baseMap_intertwines g) _
      (fun z => (intertwining_iff R _ _ _).mp h.hom.h (ULift.up z))
      (LinearMap.ext fun x => congrArg (fun k => k.f (ULift.up x)) hh)
  apply ObjectProperty.hom_ext
  apply Endofunctor.Algebra.Hom.ext
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  exact LinearMap.congr_fun key z.down

/-- Initiality data for the explicit structured arrow. -/
def explicitIsUniversal (A : EndomorphismCat.{u, v} R) :
    StructuredArrow.IsUniversal (explicitStructuredArrow.{u, v, w} R A) :=
  IsInitial.ofUniqueHom
    (fun g => StructuredArrow.homMk (explicitFactor A g.right g.hom)
      (explicitFactor_fac A g.right g.hom))
    (fun g m => StructuredArrow.ext _ _
      (explicitFactor_unique A g.right g.hom m.right (StructuredArrow.w m)))

/-- Initiality data for the chosen structured arrow, transported along the comparison. -/
def chosenIsUniversal (A : EndomorphismCat.{u, v} R) :
    StructuredArrow.IsUniversal (chosenStructuredArrow.{u, v, w} R A) :=
  IsInitial.ofIso (explicitIsUniversal A) (structuredArrowComparison R A).symm

theorem explicitFactorization : ExplicitFactorizationStatement.{u, v, w} :=
  fun _ _ A _ g => (explicitIsUniversal A).existsUnique (StructuredArrow.mk g)

theorem chosenFactorization : ChosenFactorizationStatement.{u, v, w} :=
  fun _ _ A _ g => (chosenIsUniversal A).existsUnique (StructuredArrow.mk g)

theorem explicitInitiality : ExplicitInitialityStatement.{u, v, w} :=
  fun _ _ A => ⟨explicitIsUniversal A⟩

theorem chosenInitiality : ChosenInitialityStatement.{u, v, w} :=
  fun _ _ A => ⟨chosenIsUniversal A⟩

theorem comparisonUniqueness : ComparisonUniquenessStatement.{u, v, w} := by
  intro R _ A
  refine ⟨fun h hh => ?_, fun h hh => ?_⟩
  · exact ((chosenIsUniversal A).existsUnique (explicitStructuredArrow R A)).unique hh
      (chosenArrow_comparison R A)
  · exact ((explicitIsUniversal A).existsUnique (chosenStructuredArrow R A)).unique hh
      (StructuredArrow.w (structuredArrowComparison R A).inv)

theorem fieldExplicitFactorization : FieldExplicitFactorizationStatement.{u, v, w} :=
  fun k _ A B g => explicitFactorization k A B g

theorem initialityStatements : InitialityStatements.{u, v, w} :=
  ⟨explicitFactorization, chosenFactorization, explicitInitiality, chosenInitiality,
    comparisonUniqueness, fieldExplicitFactorization⟩

end Langlands.Renard.EndomorphismLocalization.ChosenComparison
