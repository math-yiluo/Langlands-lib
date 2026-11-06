import Langlands.Algebra.RenardAlgebraActionLocalizationInitialityStatements
import Langlands.Algebra.RenardAlgebraLocalizationUniversalProof

/-! # Initiality of the canonical arrow of the localized algebra action: proof -/

set_option autoImplicit false

universe u v w x

noncomputable section

namespace Langlands.Renard.AlgebraActionLocalization

open CategoryTheory Limits Langlands.Algebra EndomorphismLocalization

variable {k : Type u} [CommRing k] {B : Type v} [NonUnitalRing B] [Module k B]

/-- The original intertwiner underlying a morphism out of the raised pair. -/
def baseIntertwiner {A : ActionEndomorphismCat.{u, v, w} k B}
    {T : InvertibleActionEndomorphismCat.{u, v, max u w x} k B}
    (g : (raisedFunctor.{u, v, w, x} k B).obj A ⟶
      (invertibleActionInclusion.{u, v, max u w x} k B).obj T) :
    LinearIntertwiner A.a.action T.obj.a.action where
  toLinearMap := g.f.hom.toLinearMap ∘ₗ
    (ULift.moduleEquiv (R := k) (M := A.a)).symm.toLinearMap
  map_action' b z := g.f.hom.map_action b (ULift.up z)

theorem baseIntertwiner_intertwines {A : ActionEndomorphismCat.{u, v, w} k B}
    {T : InvertibleActionEndomorphismCat.{u, v, max u w x} k B}
    (g : (raisedFunctor.{u, v, w, x} k B).obj A ⟶
      (invertibleActionInclusion.{u, v, max u w x} k B).obj T) (z : A.a) :
    baseIntertwiner g (endomorphism A z) = T.obj.str.hom (baseIntertwiner g z) :=
  (intertwining_iff _ _ g.f).mp g.h (ULift.up z)

/-- The published factor of the base intertwiner, as an actual intertwiner of the
localized action. -/
def factorIntertwiner (A : ActionEndomorphismCat.{u, v, w} k B)
    (T : InvertibleActionEndomorphismCat.{u, v, max u w x} k B)
    (g : (raisedFunctor.{u, v, w, x} k B).obj A ⟶
      (invertibleActionInclusion.{u, v, max u w x} k B).obj T) :
    LinearIntertwiner (objectLocalizedAction A) T.obj.a.action where
  toLinearMap := factor (endomorphism A) T.obj.str.hom.toLinearMap T.property
    (baseIntertwiner g).toLinearMap (baseIntertwiner_intertwines g)
  map_action' := factor_map_localizedAction (endomorphism A) A.a.action
    (endomorphism_action A) T.obj.a.action T.obj.str.hom T.property (baseIntertwiner g)
    (baseIntertwiner_intertwines g)

/-- The factor as a morphism of pairs with invertible endomorphism. -/
def canonicalFactor (A : ActionEndomorphismCat.{u, v, w} k B)
    (T : InvertibleActionEndomorphismCat.{u, v, max u w x} k B)
    (g : (raisedFunctor.{u, v, w, x} k B).obj A ⟶
      (invertibleActionInclusion.{u, v, max u w x} k B).obj T) :
    localizedObject.{u, v, w, x} A ⟶ T :=
  ObjectProperty.homMk
    { f := ActionModuleCat.ofHom
        { toLinearMap := (factorIntertwiner A T g).toLinearMap ∘ₗ
            (ULift.moduleEquiv (R := k) (M := Localized (endomorphism A))).toLinearMap
          map_action' := fun b z => (factorIntertwiner A T g).map_action b z.down }
      h := (intertwining_iff _ _ _).mpr fun z =>
        factor_intertwines (endomorphism A) T.obj.str.hom.toLinearMap T.property
          (baseIntertwiner g).toLinearMap (baseIntertwiner_intertwines g) z.down }

theorem canonicalFactor_fac (A : ActionEndomorphismCat.{u, v, w} k B)
    (T : InvertibleActionEndomorphismCat.{u, v, max u w x} k B)
    (g : (raisedFunctor.{u, v, w, x} k B).obj A ⟶
      (invertibleActionInclusion.{u, v, max u w x} k B).obj T) :
    canonicalArrow.{u, v, w, x} A ≫
      (invertibleActionInclusion.{u, v, max u w x} k B).map (canonicalFactor A T g) = g := by
  apply Endofunctor.Algebra.Hom.ext
  apply ActionModuleCat.hom_ext
  intro z
  exact LinearMap.congr_fun (factor_comp_iota (endomorphism A) T.obj.str.hom.toLinearMap
    T.property (baseIntertwiner g).toLinearMap (baseIntertwiner_intertwines g)) z.down

theorem canonicalFactor_unique (A : ActionEndomorphismCat.{u, v, w} k B)
    (T : InvertibleActionEndomorphismCat.{u, v, max u w x} k B)
    (g : (raisedFunctor.{u, v, w, x} k B).obj A ⟶
      (invertibleActionInclusion.{u, v, max u w x} k B).obj T)
    (h : localizedObject.{u, v, w, x} A ⟶ T)
    (hh : canonicalArrow.{u, v, w, x} A ≫
      (invertibleActionInclusion.{u, v, max u w x} k B).map h = g) :
    h = canonicalFactor A T g := by
  have key : h.hom.f.hom.toLinearMap ∘ₗ
      (ULift.moduleEquiv (R := k) (M := Localized (endomorphism A))).symm.toLinearMap =
      factor (endomorphism A) T.obj.str.hom.toLinearMap T.property
        (baseIntertwiner g).toLinearMap (baseIntertwiner_intertwines g) :=
    factor_unique (endomorphism A) T.obj.str.hom.toLinearMap T.property
      (baseIntertwiner g).toLinearMap (baseIntertwiner_intertwines g) _
      (fun z => (intertwining_iff _ _ _).mp h.hom.h (ULift.up z))
      (LinearMap.ext fun z => congrArg (fun m => m.f.hom (ULift.up z)) hh)
  apply ObjectProperty.hom_ext
  apply Endofunctor.Algebra.Hom.ext
  apply ActionModuleCat.hom_ext
  intro z
  exact LinearMap.congr_fun key z.down

/-- Initiality data for the canonical structured arrow. -/
def canonicalIsUniversal (A : ActionEndomorphismCat.{u, v, w} k B) :
    StructuredArrow.IsUniversal (canonicalStructuredArrow.{u, v, w, x} A) :=
  IsInitial.ofUniqueHom
    (fun g => StructuredArrow.homMk (canonicalFactor A g.right g.hom)
      (canonicalFactor_fac A g.right g.hom))
    (fun g m => StructuredArrow.ext _ _
      (canonicalFactor_unique A g.right g.hom m.right (StructuredArrow.w m)))

theorem factorization : FactorizationStatement.{u, v, w, x} :=
  fun _ _ _ _ _ A _ g => (canonicalIsUniversal A).existsUnique (StructuredArrow.mk g)

theorem initiality : InitialityStatement.{u, v, w, x} :=
  fun _ _ _ _ _ A => ⟨canonicalIsUniversal A⟩

theorem fieldFactorization : FieldFactorizationStatement.{u, v, w, x} :=
  fun k _ B _ _ _ _ A T g => factorization k B A T g

theorem initialityStatements : InitialityStatements.{u, v, w, x} :=
  ⟨factorization, initiality, fieldFactorization⟩

end Langlands.Renard.AlgebraActionLocalization
