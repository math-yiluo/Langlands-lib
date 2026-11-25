import Langlands.GroupScheme.Torus.Split
import Langlands.GroupScheme.OddOrthogonalMatrix.InnerAutomorphismEquiv

/-! # Unique original-field conjugators for the full odd norm-one group -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.OddOrthogonalMatrix

section Transport

variable {S : Scheme.{u}} {G H : GroupScheme S}

/-- Actual points transport multiplicatively through a group-scheme isomorphism. -/
def pointsIsoEquiv (e : G ≅ H) (T : Over S) : (T ⟶ G.X) ≃* (T ⟶ H.X) :=
  isoPointsEquiv e T

/-- Conjugating an inner automorphism through an actual isomorphism transports its point. -/
theorem autMulEquivOfIso_innerIso (e : G ≅ H) (g : Over.mk (𝟙 S) ⟶ G.X) :
    Aut.autMulEquivOfIso e (Aut.of (G.innerIso g)) = Aut.of (H.innerIso (g ≫ e.hom.hom.hom)) := by
  apply Aut.ext
  apply Iso.ext
  change e.inv ≫ (G.innerIso g).hom ≫ e.hom = _
  rw [innerIso_hom_comp, Iso.inv_hom_id_assoc]

end Transport

variable {K : Type u} [Field K] {n : ℕ}

/-- Rational points of the full split odd norm-one group are exactly its
automorphisms by conjugation, over the original field. -/
def fullInnerAutEquiv (hn : 2 ≤ n) :
    (Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ (groupScheme (Fin n) K).X) ≃*
      CategoryTheory.Aut (groupScheme (Fin n) K) :=
  ((pointsIsoEquiv (identityComponentIso (K := K) hn).symm _).trans
    (TypeBNumbering.identityInnerAutEquiv hn)).trans
      (Aut.autMulEquivOfIso (identityComponentIso hn))

/-- This equivalence is the actual inner-conjugation homomorphism. -/
@[simp] theorem fullInnerAutEquiv_apply (hn : 2 ≤ n)
    (g : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ (groupScheme (Fin n) K).X) :
    fullInnerAutEquiv hn g = Aut.of ((groupScheme (Fin n) K).innerIso g) := by
  let e := identityComponentIso (K := K) hn
  change Aut.autMulEquivOfIso e
    (Aut.of ((identityComponent (groupScheme (Fin n) K)).innerIso (g ≫ e.inv.hom.hom))) = _
  rw [autMulEquivOfIso_innerIso]
  simp only [Category.assoc, ← Grp.comp_hom_hom, e.inv_hom_id, Grp.id_hom_hom, Category.comp_id]

/-- The inverse equivalence supplies the unique original-field conjugating point. -/
theorem fullInnerAutEquiv_symm_spec (hn : 2 ≤ n)
    (σ : CategoryTheory.Aut (groupScheme (Fin n) K)) :
    (groupScheme (Fin n) K).innerIso ((fullInnerAutEquiv hn).symm σ) = σ.asIso := by
  exact congrArg Aut.asIso
    ((fullInnerAutEquiv_apply hn _).symm.trans ((fullInnerAutEquiv hn).apply_symm_apply σ))

end Langlands.GroupScheme.OddOrthogonalMatrix
