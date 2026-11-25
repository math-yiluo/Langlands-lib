import Langlands.Algebra.FiniteFreeRingHomFunctor
import Langlands.AbelianScheme.IntegralOrderActions
import Langlands.AbelianScheme.RelativeEndomorphismRepresentabilityStatement
import Mathlib.CategoryTheory.Whiskering

/-! # Finite integral actions on the canonical relative endomorphism presheaf -/

noncomputable section

open CategoryTheory AlgebraicGeometry Module Opposite

universe u uI uO

namespace Langlands.AbelianScheme

open Langlands.GroupScheme.Cartier

variable {S : Scheme.{u}} (B : Langlands.AbelianScheme S)

private theorem restrict_identity {T T' : Over S} (a : T' ⟶ T) :
    restrict B.toCommGroupScheme B.toCommGroupScheme a
      (𝟙 (testBaseChange T B.toCommGroupScheme)) =
      𝟙 (testBaseChange T' B.toCommGroupScheme) := by
  change Additive.ofMul
    ((baseChangeCompIso B.toCommGroupScheme a).hom ≫
      (GroupScheme.baseChange a.left).map (𝟙 _) ≫
      (baseChangeCompIso B.toCommGroupScheme a).inv) = Additive.ofMul (𝟙 _)
  simp

private theorem restrict_composition {T T' : Over S} (a : T' ⟶ T)
    (f g : testBaseChange T B.toCommGroupScheme ⟶ testBaseChange T B.toCommGroupScheme) :
    restrict B.toCommGroupScheme B.toCommGroupScheme a (f ≫ g) =
      restrict B.toCommGroupScheme B.toCommGroupScheme a f ≫
        restrict B.toCommGroupScheme B.toCommGroupScheme a g := by
  change Additive.ofMul
    ((baseChangeCompIso B.toCommGroupScheme a).hom ≫
      (GroupScheme.baseChange a.left).map (f.toMul ≫ g.toMul) ≫
      (baseChangeCompIso B.toCommGroupScheme a).inv) =
    Additive.ofMul
      (((baseChangeCompIso B.toCommGroupScheme a).hom ≫
        (GroupScheme.baseChange a.left).map f.toMul ≫
        (baseChangeCompIso B.toCommGroupScheme a).inv) ≫
       ((baseChangeCompIso B.toCommGroupScheme a).hom ≫
        (GroupScheme.baseChange a.left).map g.toMul ≫
        (baseChangeCompIso B.toCommGroupScheme a).inv))
  rw [(GroupScheme.baseChange a.left).map_comp]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]

/-- The existing canonical relative-Hom restriction, with its actual End-ring laws. -/
def relativeEndRestrict {T T' : Over S} (a : T' ⟶ T) :
    CategoryTheory.End ((baseChange T.hom).obj B) →+*
      CategoryTheory.End ((baseChange T'.hom).obj B) where
  toFun f := CategoryTheory.End.of
    (restrict B.toCommGroupScheme B.toCommGroupScheme a f.asHom)
  map_zero' := congrArg CategoryTheory.End.of
    (map_zero (restrict B.toCommGroupScheme B.toCommGroupScheme a))
  map_add' f g := congrArg CategoryTheory.End.of
    (map_add (restrict B.toCommGroupScheme B.toCommGroupScheme a) f.asHom g.asHom)
  map_one' := congrArg CategoryTheory.End.of (restrict_identity B a)
  map_mul' f g := congrArg CategoryTheory.End.of (restrict_composition B a g.asHom f.asHom)

/-- The canonical relative integral endomorphism presheaf, retaining its ring structure. -/
def relativeEndRingFunctor : (Over S)ᵒᵖ ⥤ RingCat.{u} where
  obj T := RingCat.of (CategoryTheory.End ((baseChange T.unop.hom).obj B))
  map a := RingCat.ofHom (relativeEndRestrict B a.unop)
  map_id T := by
    ext f : 2
    exact congrArg CategoryTheory.End.of
      (restrict_id B.toCommGroupScheme B.toCommGroupScheme T.unop f.asHom)
  map_comp a b := by
    ext f : 2
    exact congrArg CategoryTheory.End.of
      (restrict_comp B.toCommGroupScheme B.toCommGroupScheme b.unop a.unop f.asHom)

/-- Forgetting the ring gives the published relative-Hom presheaf, up to the natural
isomorphism sending an endomorphism to its underlying morphism. -/
def relativeEndRingFunctorForgetIso :
    relativeEndRingFunctor B ⋙ forget RingCat ≅
      relativeHomFunctor B.toCommGroupScheme B.toCommGroupScheme ⋙ forget AddCommGrpCat :=
  NatIso.ofComponents
    (fun T => (CategoryTheory.End.homEquiv (X := (baseChange T.unop.hom).obj B)).toIso)
    (fun _ => rfl)

/-- The forward component sends an endomorphism to its underlying morphism. -/
@[simp] theorem relativeEndRingFunctorForgetIso_hom_app (T : (Over S)ᵒᵖ)
    (f : (relativeEndRingFunctor B).obj T) :
    (relativeEndRingFunctorForgetIso B).hom.app T f = f.asHom := rfl

/-- The inverse component regards a relative homomorphism as an endomorphism. -/
@[simp] theorem relativeEndRingFunctorForgetIso_inv_app (T : (Over S)ᵒᵖ)
    (g : (relativeHomFunctor B.toCommGroupScheme B.toCommGroupScheme).obj T) :
    (relativeEndRingFunctorForgetIso B).inv.app T g =
      CategoryTheory.End.of (X := (baseChange T.unop.hom).obj B) g := rfl

variable {I : Type uI} [Fintype I] {O : Type uO} [Ring O] (b : Basis I ℤ O)

/-- Actual integral actions, restricted by the canonical iterated-base-change comparisons. -/
abbrev relativeIntegralActionFunctor :=
  Langlands.FiniteFreeRingHom.actionFunctor b (relativeEndRingFunctor B)

/-- The corresponding finite unit and multiplication equations on actual End tuples. -/
abbrev relativeIntegralActionSolutionsFunctor :=
  Langlands.FiniteFreeRingHom.solutionsFunctor b (relativeEndRingFunctor B)

/-- The actual-action/finite-tuple equivalence on every scheme over the base. -/
def relativeIntegralActionSolutionsIso :
    relativeIntegralActionFunctor B b ≅
      relativeIntegralActionSolutionsFunctor B b :=
  Langlands.FiniteFreeRingHom.actionSolutionsIso b (relativeEndRingFunctor B)

/-- The exact full category of locally noetherian tests used by relative End representability. -/
abbrev locallyNoetherianTestInclusion (S : Scheme.{u}) :=
  ObjectProperty.ι (fun T : Over S => IsLocallyNoetherian T.left)

/-- The same comparison on all locally noetherian test schemes and all their morphisms. -/
def locallyNoetherianIntegralActionSolutionsIso :
    (locallyNoetherianTestInclusion S).op ⋙
        relativeIntegralActionFunctor B b ≅
      (locallyNoetherianTestInclusion S).op ⋙
        relativeIntegralActionSolutionsFunctor B b :=
  Functor.isoWhiskerLeft (locallyNoetherianTestInclusion S).op
    (relativeIntegralActionSolutionsIso B b)

end Langlands.AbelianScheme
