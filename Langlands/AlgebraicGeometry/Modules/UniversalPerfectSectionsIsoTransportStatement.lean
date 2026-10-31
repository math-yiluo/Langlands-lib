import Langlands.AlgebraicGeometry.Modules.UniversalPerfectSectionsRepresentative

/-! # Transport of a fixed universal representative through isomorphisms -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.Modules

attribute [local instance] HasDerivedCategory.standard

/-- A fixed universal representative transports through a scheme isomorphism
and an isomorphism of the actual coefficient modules. -/
def UniversalPerfectSectionsIsoTransportStatement : Prop :=
  ∀ (R : CommRingCat.{u}) (X Y : Scheme.{u}) (e : X ≅ Y)
    (g : Y ⟶ Spec R) (M : X.Modules) (N : Y.Modules),
    (M ≅ (Scheme.Modules.pullback e.hom).obj N) →
    ∀ (K : CochainComplex (ModuleCat.{u} R) ℤ),
      IsUniversalPerfectSectionsRepresentative g N K →
      IsUniversalPerfectSectionsRepresentative (e.hom ≫ g) M K

end Langlands.AlgebraicGeometry.Modules
