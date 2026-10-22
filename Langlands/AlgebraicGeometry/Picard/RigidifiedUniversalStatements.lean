import Langlands.AlgebraicGeometry.Picard.RigidifiedUniversalBundle

/-! # Uniqueness target for universal rigidified line bundles -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.Picard.RigidifiedLineBundle

/-- Two universal rigidified bundles have a unique compatible isomorphism of their
parameter schemes. Compatibility means existence of an isomorphism of rigidified bundles,
not uniqueness of that bundle isomorphism. -/
def UniversalBundleUniquenessStatement : Prop :=
  Langlands.SchemeModule.RigidifiedModule.PullbackCoherenceStatement.{u} →
    ∀ (S X : Scheme.{u}) (f : X ⟶ S) (ε : S ⟶ X)
      (section_eq : ε ≫ f = 𝟙 S) (P Q : Over S)
      (L : relative f ε section_eq P) (M : relative f ε section_eq Q),
      IsUniversal f ε section_eq L → IsUniversal f ε section_eq M →
        ∃! e : P ≅ Q, Nonempty ((relativePullback f ε section_eq e.hom).obj M ≅ L)

end Langlands.AlgebraicGeometry.Picard.RigidifiedLineBundle
