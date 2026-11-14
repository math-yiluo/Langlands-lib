import Langlands.GroupScheme.Rational.InnerDiscrepancy
import Langlands.GroupScheme.Adjoint.InnerAction
import Langlands.GroupScheme.Adjoint.SplitTorus
import Langlands.GroupScheme.AutomorphicActionPointIso

/-! # Faithfulness of the actual descended inner action -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme



namespace IsAdjointQuotient

variable {k : Type u} [Field k]
    {G A : GroupScheme (Spec (CommRingCat.of k))}
    {q : G ⟶ A} (hq : IsAdjointQuotient q)

/-- Only the identity quotient point acts trivially on every relative test. -/
theorem innerAction_eq_one_of_act_eq {T : Over (Spec (CommRingCat.of k))}
    (x : T ⟶ A.X)
    (hx : ∀ (U : Over (Spec (CommRingCat.of k))) (b : U ⟶ T) (g : U ⟶ G.X),
      hq.innerAction.act (b ≫ x) g = g) : x = 1 :=
  hq.innerAction_kernel x (fun {U} b g => hx U b g)

/-- An adjoint point is determined by its inner action after a finite flat
surjective homomorphism, including an inseparable isogeny. -/
theorem innerAction_point_ext_of_isogeny {C : GroupScheme (Spec (CommRingCat.of k))}
    (φ : C ⟶ G) (hφ : IsIsogeny φ) {T : Over (Spec (CommRingCat.of k))}
    (x y : T ⟶ A.X)
    (hxy : ∀ (U : Over (Spec (CommRingCat.of k))) (b : U ⟶ T) (g : U ⟶ C.X),
      hq.innerAction.act (b ≫ x) (g ≫ φ.hom.hom) =
        hq.innerAction.act (b ≫ y) (g ≫ φ.hom.hom)) : x = y := by
  let := hφ.1
  let := hφ.2.1
  let := hφ.2.2
  apply hq.innerAction_isFaithful x y
  intro U b g
  apply AutomorphicAction.hom_ext_of_local_quotient_lift φ g _ _
  intro V c z hz
  rw [hq.innerAction.naturality, hq.innerAction.naturality, hz]
  simpa only [Category.assoc] using hxy V (c ≫ b) z

end IsAdjointQuotient

end Langlands.GroupScheme
