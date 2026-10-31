import Langlands.AlgebraicGeometry.Modules.UniversalPerfectSectionsRepresentative

/-! # Universal perfect representatives under a scalar tower -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.Modules

attribute [local instance] HasDerivedCategory.standard

/-- Scalar extension of a given universal perfect representative is a
universal perfect representative of the base-changed actual module. -/
def UniversalPerfectSectionsScalarTowerStatement : Prop :=
  ∀ (R : CommRingCat.{u}) (X : Scheme.{u}) (f : X ⟶ Spec R)
    (M : X.Modules) (K : CochainComplex (ModuleCat.{u} R) ℤ),
    IsUniversalPerfectSectionsRepresentative f M K →
    ∀ (S : CommRingCat.{u}) (φ : R ⟶ S),
      IsUniversalPerfectSectionsRepresentative
        (pullback.snd f (Spec.map φ))
        ((Scheme.Modules.pullback (pullback.fst f (Spec.map φ))).obj M)
        ((Langlands.Cohomology.ModuleComplex.baseChange φ.hom).obj K)

end Langlands.AlgebraicGeometry.Modules
