import Langlands.Cohomology.Tate.OrdinaryCupDefinitions
import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree

universe u

open CategoryTheory

namespace Langlands.Tate

/-- Zero-degree normalization and coefficient naturality of the actual ordinary cup. -/
def OrdinaryCupLaws : Prop :=
  ∀ (R G : Type u) [CommRing R] [Group G],
    (∀ (A B C : Rep.{u} R G) (φ : Pairing A B C)
      (a : A.ρ.invariants) (b : B.ρ.invariants),
      ordinaryCup φ 0 0 ((groupCohomology.H0Iso A).inv a)
        ((groupCohomology.H0Iso B).inv b) =
        (groupCohomology.H0Iso C).inv (φ.onInvariants a b)) ∧
    (∀ (A A' B B' C C' : Rep.{u} R G)
      (φ : Pairing A B C) (φ' : Pairing A' B' C')
      (f : A ⟶ A') (g : B ⟶ B') (h : C ⟶ C'),
      (∀ a b, h.hom (φ.bilinear a b) = φ'.bilinear (f.hom a) (g.hom b)) →
      ∀ (p q : ℕ) (a : groupCohomology A p) (b : groupCohomology B q),
        groupCohomology.map (MonoidHom.id G) h (p + q) (ordinaryCup φ p q a b) =
          ordinaryCup φ' p q (groupCohomology.map (MonoidHom.id G) f p a)
            (groupCohomology.map (MonoidHom.id G) g q b))

end Langlands.Tate
