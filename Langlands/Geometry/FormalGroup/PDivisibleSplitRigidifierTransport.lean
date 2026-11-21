import Langlands.Geometry.FormalGroup.HarrisSplitPDivisiblePoint
import Langlands.Geometry.FormalGroup.PDivisibleRationalSplitBaseChange

/-! # Composition on the original full split special fibres -/

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1250000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v

open CategoryTheory

namespace Langlands.PDivisibleGroup

open GroupScheme.Cartier

private theorem transportIso_trans {C : Type u} [Category.{v} C] {X Y Z X' Y' Z' : C}
    (i : X ≅ X') (j : Y ≅ Y') (k : Z ≅ Z') (f : X' ≅ Y') (g : Y' ≅ Z') :
    i.trans ((f.trans g).trans k.symm) =
      (i.trans (f.trans j.symm)).trans (j.trans (g.trans k.symm)) := by
  apply Iso.ext
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id_assoc]

variable {R₁ R₂ R₃ S : Type u} [CommRing R₁] [CommRing R₂] [CommRing R₃] [CommRing S]
  [Algebra R₁ S] [Algebra R₂ S] [Algebra R₃ S]
variable {p : ℕ} [Fact p.Prime] {A : Type v} [Ring A]
variable {G₁ : PDivisibleGroup (CommRingCat.of R₁) p} {G₂ : PDivisibleGroup (CommRingCat.of R₂) p}
  {G₃ : PDivisibleGroup (CommRingCat.of R₃) p}
variable (hExact : FiniteCartierDualExactnessStatement.{u})
variable {a : A →+* End G₁} {b : A →+* End G₂} {d : A →+* End G₃}

/-- The full rational map on the original split pullbacks, in terms of a primal map
whose source and target lie over the common base. -/
def splitQuasiIsogenyOnBaseChange
    (q : QuasiIsogeny ((baseChangeFunctor R₁ S p).obj G₁) ((baseChangeFunctor R₂ S p).obj G₂))
    (c : ℚ_[p]ˣ) :
    QuasiIsogeny ((baseChangeFunctor R₁ S p).obj (G₁.splitWithDual hExact))
      ((baseChangeFunctor R₂ S p).obj (G₂.splitWithDual hExact)) :=
  (rationalSplitBaseChangeIso (S := S) hExact G₁).trans
    ((splitRigidifier hExact q c).trans (rationalSplitBaseChangeIso (S := S) hExact G₂).symm)

theorem splitOrderRigidifierOnBaseChange_val
    (q : OrderQuasiIsogeny ((baseChangeEnd (S := S) G₁).comp a) ((baseChangeEnd (S := S) G₂).comp b))
    (c : ℚ_[p]ˣ) :
    (splitOrderRigidifierOnBaseChange (S := S) hExact a b q c).val =
      splitQuasiIsogenyOnBaseChange (G₁ := G₁) (G₂ := G₂) (S := S) hExact q.val c := rfl

/-- Composing on the original full pullbacks agrees with composing the primal maps
on the common base and multiplying their multiplier units. -/
theorem splitOrderRigidifierOnBaseChange_trans
    (q : OrderQuasiIsogeny ((baseChangeEnd (S := S) G₁).comp a) ((baseChangeEnd (S := S) G₂).comp b))
    (r : OrderQuasiIsogeny ((baseChangeEnd (S := S) G₂).comp b) ((baseChangeEnd (S := S) G₃).comp d))
    (c k : ℚ_[p]ˣ) :
    (splitOrderRigidifierOnBaseChange (S := S) hExact a d (q.trans r) (c * k)).val =
      (splitOrderRigidifierOnBaseChange (S := S) hExact a b q c).val.trans
        (splitOrderRigidifierOnBaseChange (S := S) hExact b d r k).val := by
  let i := rationalSplitBaseChangeIso (S := S) hExact G₁
  let j := rationalSplitBaseChangeIso (S := S) hExact G₂
  let l := rationalSplitBaseChangeIso (S := S) hExact G₃
  let f := splitRigidifier hExact q.val c
  let g := splitRigidifier hExact r.val k
  change i.trans ((splitRigidifier hExact (q.val.trans r.val) (c * k)).trans l.symm) =
    (i.trans (f.trans j.symm)).trans (j.trans (g.trans l.symm))
  rw [splitRigidifier_trans]
  exact transportIso_trans i j l f g

end Langlands.PDivisibleGroup
