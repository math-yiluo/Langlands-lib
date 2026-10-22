import Mathlib.CategoryTheory.Abelian.RightDerived
import Mathlib.CategoryTheory.Action.Basic

/-!
# Acyclic resolutions and comparison with right-derived functors

These are proposition definitions, not theorem proofs. The augmentation is a
quasi-isomorphism from the object in degree zero; no comparison isomorphism is
assumed. See the paired Markdown for the original sources and draft status.
-/

open CategoryTheory CategoryTheory.Limits

namespace Langlands.Cohomology

universe u v u' v' w

/-- A right resolution maps to any injective resolution of the same object,
and two augmentation-compatible lifts are homotopic. -/
def ResolutionLiftStatement : Prop :=
  ∀ (C : Type u) [Category.{v} C] [Abelian C]
    (A : C) (K : CochainComplex C ℕ)
    (ε : (CochainComplex.single₀ C).obj A ⟶ K),
    QuasiIso ε →
    ∀ (I : InjectiveResolution A),
      (∃ φ : K ⟶ I.cocomplex, ε ≫ φ = I.ι) ∧
      ∀ (φ ψ : K ⟶ I.cocomplex),
        ε ≫ φ = I.ι → ε ≫ ψ = I.ι → Nonempty (Homotopy φ ψ)

/-- An acyclic right resolution computes the actual right-derived functors.
The comparison is the homology of any lift, followed by the inverse of the
existing injective-resolution identification. -/
def AcyclicResolutionComparisonStatement : Prop :=
  ∀ (C : Type u) [Category.{v} C] [Abelian C] [HasInjectiveResolutions C]
    (D : Type u') [Category.{v'} D] [Abelian D]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F]
    (A : C) (K : CochainComplex C ℕ)
    (ε : (CochainComplex.single₀ C).obj A ⟶ K),
    QuasiIso ε →
    (∀ (i n : ℕ), IsZero ((F.rightDerived (n + 1)).obj (K.X i))) →
    ∀ (I : InjectiveResolution A) (φ : K ⟶ I.cocomplex),
      ε ≫ φ = I.ι →
      QuasiIso ((F.mapHomologicalComplex _).map φ) ∧
      ∀ n : ℕ,
        IsIso
          ((F.mapHomologicalComplex _ ⋙ HomologicalComplex.homologyFunctor D _ n).map φ ≫
            (I.isoRightDerivedObj F n).inv)

/-- The comparison to the fixed right-derived functor does not depend on the
injective resolution or its augmentation-compatible lift. Acyclicity is not
needed for this equality of maps. -/
def ResolutionComparisonIndependenceStatement : Prop :=
  ∀ (C : Type u) [Category.{v} C] [Abelian C] [HasInjectiveResolutions C]
    (D : Type u') [Category.{v'} D] [Abelian D]
    (F : C ⥤ D) [F.Additive]
    (A : C) (K : CochainComplex C ℕ)
    (ε : (CochainComplex.single₀ C).obj A ⟶ K),
    QuasiIso ε →
    ∀ (I J : InjectiveResolution A)
      (φ : K ⟶ I.cocomplex) (ψ : K ⟶ J.cocomplex),
      ε ≫ φ = I.ι → ε ≫ ψ = J.ι →
      ∀ n : ℕ,
        (F.mapHomologicalComplex _ ⋙ HomologicalComplex.homologyFunctor D _ n).map φ ≫
            (I.isoRightDerivedObj F n).inv =
          (F.mapHomologicalComplex _ ⋙ HomologicalComplex.homologyFunctor D _ n).map ψ ≫
            (J.isoRightDerivedObj F n).inv

/-- Augmentation-compatible maps between right resolutions commute with the
comparison to right-derived functors. This identity holds before imposing
acyclicity on the terms of the resolutions. -/
def ResolutionComparisonNaturalityStatement : Prop :=
  ∀ (C : Type u) [Category.{v} C] [Abelian C] [HasInjectiveResolutions C]
    (D : Type u') [Category.{v'} D] [Abelian D]
    (F : C ⥤ D) [F.Additive]
    (A B : C) (K L : CochainComplex C ℕ)
    (ε : (CochainComplex.single₀ C).obj A ⟶ K)
    (η : (CochainComplex.single₀ C).obj B ⟶ L),
    QuasiIso ε → QuasiIso η →
    ∀ (f : A ⟶ B) (g : K ⟶ L),
      ε ≫ g = (CochainComplex.single₀ C).map f ≫ η →
      ∀ (I : InjectiveResolution A) (J : InjectiveResolution B)
        (φ : K ⟶ I.cocomplex) (ψ : L ⟶ J.cocomplex),
        ε ≫ φ = I.ι → η ≫ ψ = J.ι →
        ∀ n : ℕ,
          (F.mapHomologicalComplex _ ⋙ HomologicalComplex.homologyFunctor D _ n).map g ≫
              (F.mapHomologicalComplex _ ⋙ HomologicalComplex.homologyFunctor D _ n).map ψ ≫
              (J.isoRightDerivedObj F n).inv =
            (F.mapHomologicalComplex _ ⋙ HomologicalComplex.homologyFunctor D _ n).map φ ≫
              (I.isoRightDerivedObj F n).inv ≫ (F.rightDerived n).map f

/-- A natural transformation between additive functors commutes with the
resolution comparison. This is a functor-level compatibility, without a claim
that any particular coefficient-change construction has yet been supplied. -/
def ResolutionComparisonTransformationStatement : Prop :=
  ∀ (C : Type u) [Category.{v} C] [Abelian C] [HasInjectiveResolutions C]
    (D : Type u') [Category.{v'} D] [Abelian D]
    (F G : C ⥤ D) [F.Additive] [G.Additive] (α : F ⟶ G)
    (A : C) (K : CochainComplex C ℕ)
    (ε : (CochainComplex.single₀ C).obj A ⟶ K),
    QuasiIso ε →
    ∀ (I : InjectiveResolution A) (φ : K ⟶ I.cocomplex),
      ε ≫ φ = I.ι →
      ∀ n : ℕ,
        (HomologicalComplex.homologyFunctor D _ n).map
              ((NatTrans.mapHomologicalComplex α _).app K) ≫
            (G.mapHomologicalComplex _ ⋙ HomologicalComplex.homologyFunctor D _ n).map φ ≫
            (I.isoRightDerivedObj G n).inv =
          (F.mapHomologicalComplex _ ⋙ HomologicalComplex.homologyFunctor D _ n).map φ ≫
            (I.isoRightDerivedObj F n).inv ≫ (NatTrans.rightDerived α n).app A

/-- The ordinary comparison is equivariant for actual actions on the resolved
object and complex, even when the chosen lift is only an ordinary cochain map.
This is algebraic equivariance; no continuity or smoothness is asserted. -/
def AcyclicResolutionEquivarianceStatement : Prop :=
  ∀ (C : Type u) [Category.{v} C] [Abelian C] [HasInjectiveResolutions C]
    (D : Type u') [Category.{v'} D] [Abelian D]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F]
    (G : Type w) [Monoid G]
    (A : Action C G) (K : Action (CochainComplex C ℕ) G)
    (ε : ((CochainComplex.single₀ C).mapAction G).obj A ⟶ K),
    QuasiIso ε.hom →
    (∀ (i n : ℕ), IsZero ((F.rightDerived (n + 1)).obj (K.V.X i))) →
    ∀ (I : InjectiveResolution A.V) (φ : K.V ⟶ I.cocomplex),
      ε.hom ≫ φ = I.ι →
      ∀ n : ℕ,
        ∃ e :
            ((F.mapHomologicalComplex _ ⋙
                HomologicalComplex.homologyFunctor D _ n).mapAction G).obj K ≅
              ((F.rightDerived n).mapAction G).obj A,
          e.hom.hom =
            (F.mapHomologicalComplex _ ⋙ HomologicalComplex.homologyFunctor D _ n).map φ ≫
              (I.isoRightDerivedObj F n).inv

/-- The coherent algebraic comparison family. Every component remains a
separate theorem obligation; none is assumed to define the conjunction. -/
def AcyclicResolutionComparisonStatements : Prop :=
  ResolutionLiftStatement.{u, v} ∧
  AcyclicResolutionComparisonStatement.{u, v, u', v'} ∧
  ResolutionComparisonIndependenceStatement.{u, v, u', v'} ∧
  ResolutionComparisonNaturalityStatement.{u, v, u', v'} ∧
  ResolutionComparisonTransformationStatement.{u, v, u', v'} ∧
  AcyclicResolutionEquivarianceStatement.{u, v, u', v', w}

end Langlands.Cohomology
