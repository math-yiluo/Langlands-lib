import Langlands.AlgebraicGeometry.FiniteFreeQuasiAffineQuotient
import Langlands.AlgebraicGeometry.ProjectiveSpace
import Mathlib.AlgebraicGeometry.Morphisms.Immersion

/-! # Quotients of quasi-projective schemes over a field by free finite group actions -/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option autoImplicit false

namespace Langlands.AlgebraicGeometry

/-- Quotients of quasi-projective schemes over a field by free actions of finite
groups. Let `X` be a scheme over a field `K` with an immersion into a finite
projective space over `K` compatible with the structure maps, and let a finite
group `G` act freely on `X` by automorphisms over `K`, in the sense of
`FiniteFreeSchemeAction`. Then the action has an effective quotient
`X ⟶ Y`: a finite étale surjective map, invariant under the action, whose
kernel pair is the disjoint union of the graphs of the action and which is the
coequalizer of the two projections from that union. Moreover `Y` is again
quasi-projective over `K`: it has a structure map to `Spec K` through which the
quotient map is a map over `K`, and an immersion into a finite projective space
over `K` compatible with it. The statement is in universe `0`. -/
def FiniteFreeQuasiProjectiveQuotientStatement : Prop :=
  ∀ (K : Type) [Field K] (X : Scheme.{0}) (s : X ⟶ Spec (CommRingCat.of K)) (N : ℕ)
    (j : X ⟶ ProjectiveSpace K N), IsImmersion j → j ≫ projectiveSpaceToSpec K N = s →
    ∀ (G : Type) [Group G] [Finite G] (A : FiniteFreeSchemeAction G X),
      (∀ g : G, (A.act g).hom ≫ s = s) →
      ∃ (Q : A.EffectiveQuotient) (t : Q.scheme ⟶ Spec (CommRingCat.of K)) (M : ℕ)
        (j' : Q.scheme ⟶ ProjectiveSpace K M),
        IsImmersion j' ∧ j' ≫ projectiveSpaceToSpec K M = t ∧ Q.map ≫ t = s

end Langlands.AlgebraicGeometry
