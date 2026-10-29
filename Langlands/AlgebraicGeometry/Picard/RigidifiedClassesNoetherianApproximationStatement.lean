import Langlands.AlgebraicGeometry.Picard.RigidifiedClassesEqualizerClosedStatement

/-! # Noetherian approximation of the agreement of two rigidified classes -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard

/-- An abelian scheme over `Spec R` with two actual rigidified classes descends to an abelian
scheme over a noetherian `Spec R₀` with two classes, compatibly with agreement: for every test
object `T'` over `Spec R`, the pullbacks of `q` and `r` to `T'` agree exactly when the pullbacks
of `q₀` and `r₀` to `T'`, viewed over `Spec R₀` through `Spec.map φ`, agree. -/
def RigidifiedClassesNoetherianApproximationStatement : Prop :=
  ∀ (R : CommRingCat.{u}) (A : AbelianScheme (Spec R))
    (q r : RigidifiedClasses A (Over.mk (𝟙 (Spec R)))),
    ∃ (R₀ : CommRingCat.{u}) (_ : IsNoetherianRing R₀) (φ : R₀ ⟶ R)
      (A₀ : AbelianScheme (Spec R₀)) (q₀ r₀ : RigidifiedClasses A₀ (Over.mk (𝟙 (Spec R₀)))),
      ∀ (T' : Over (Spec R)) (h : T' ⟶ Over.mk (𝟙 (Spec R))),
        RigidifiedLineBundle.classesPullback A.X.hom (unitSection A)
            (unitSection_comp A) h q =
          RigidifiedLineBundle.classesPullback A.X.hom (unitSection A)
            (unitSection_comp A) h r ↔
        RigidifiedLineBundle.classesPullback A₀.X.hom (unitSection A₀)
            (unitSection_comp A₀)
            (Over.homMk (T'.hom ≫ Spec.map φ) :
              Over.mk (T'.hom ≫ Spec.map φ) ⟶ Over.mk (𝟙 (Spec R₀))) q₀ =
          RigidifiedLineBundle.classesPullback A₀.X.hom (unitSection A₀)
            (unitSection_comp A₀)
            (Over.homMk (T'.hom ≫ Spec.map φ) :
              Over.mk (T'.hom ≫ Spec.map φ) ⟶ Over.mk (𝟙 (Spec R₀))) r₀

end Langlands.AbelianScheme
