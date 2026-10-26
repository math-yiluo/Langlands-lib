import Langlands.AlgebraicGeometry.Picard.RigidifiedUniversalBundle

/-! # Universal rigidified bundles from representations of the class presheaf -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.Picard.RigidifiedLineBundle

/-- A representation of the actual class presheaf by an `S`-scheme `P` is induced by an
actual universal rigidified line bundle on `P ×_S X`, whose canonical classifying map is the
representation's hom equivalence on every test scheme. -/
def RepresentationUniversalBundleStatement : Prop :=
  ∀ (S X : Scheme.{u}) (f : X ⟶ S) (ε : S ⟶ X) (section_eq : ε ≫ f = 𝟙 S)
    (coherence : Langlands.SchemeModule.RigidifiedModule.PullbackCoherenceStatement.{u})
    (P : Over S) (r : (classPresheaf coherence f ε section_eq).RepresentableBy P),
    ∃ L : relative f ε section_eq P,
      IsUniversal f ε section_eq L ∧
        ∀ (T : Over S) (h : T ⟶ P), classifyingMap f ε section_eq L T h = r.homEquiv h

end Langlands.AlgebraicGeometry.Picard.RigidifiedLineBundle
