import Langlands.Geometry.FormalGroup.PDivisibleSplitBaseChange
import Langlands.Geometry.FormalGroup.PDivisibleRationalBaseChange
import Langlands.Geometry.FormalGroup.PDivisibleSplitRigidifier

/-! # Base change and composition of rational split maps -/

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1700000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory
open scoped TensorProduct

namespace Langlands.PDivisibleGroup

open GroupScheme.Cartier

section Composition

variable {R : CommRingCat.{u}} {p : ℕ} [Fact p.Prime] {G H J : PDivisibleGroup R p}
variable (hExact : FiniteCartierDualExactnessStatement.{u})

/-- Composing split rational maps multiplies the similitude scalars. -/
theorem splitRigidifier_trans (e : QuasiIsogeny G H) (f : QuasiIsogeny H J) (c d : ℚ_[p]ˣ) :
    splitRigidifier hExact (e.trans f) (c * d) =
      (splitRigidifier hExact e c).trans (splitRigidifier hExact f d) := by
  apply Iso.ext
  simp only [Iso.trans_hom, Iso.trans_inv, splitRigidifier_hom]
  change RationalHom.prodMap (RationalHom.comp e.hom f.hom)
      ((↑(c * d) : ℚ_[p]) • RationalHom.dualMap hExact (RationalHom.comp f.inv e.inv)) =
    RationalHom.comp (RationalHom.prodMap e.hom ((c : ℚ_[p]) • RationalHom.dualMap hExact e.inv))
      (RationalHom.prodMap f.hom ((d : ℚ_[p]) • RationalHom.dualMap hExact f.inv))
  rw [RationalHom.prodMap_comp, RationalHom.smul_comp, RationalHom.comp_smul,
    smul_smul, ← RationalHom.dualMap_comp, Units.val_mul]

end Composition

section BaseChange

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
variable {p : ℕ} [Fact p.Prime] {G H : PDivisibleGroup (CommRingCat.of R) p}
variable (hExact : FiniteCartierDualExactnessStatement.{u})

open RationalHom

local notation "F" => baseChangeFunctor R S p

/-- The actual dual comparison is natural for rational tower maps. -/
theorem baseChangeDualIso_rational (f : RationalHom G H) :
    comp (baseChangeMap (S := S) (dualMap hExact f)) (ofHom (baseChangeDualIso (S := S) G hExact).hom) =
      comp (ofHom (baseChangeDualIso (S := S) H hExact).hom) (dualMap hExact (baseChangeMap (S := S) f)) := by
  induction f using TensorProduct.inductionOn with
  | add f g hf hg => simp only [map_add, add_comp, comp_add, hf, hg]
  | tmul q f =>
    simp only [dualMap_tmul, baseChangeMap_tmul, ofHom_apply, comp_tmul, mul_one, one_mul]
    exact congrArg (q ⊗ₜ[ℤ_[p]] ·) (baseChangeDualIso_naturality (S := S) G hExact f)

/-- The split pullback comparison in the category of actual rational maps. -/
def rationalSplitBaseChangeIso (G : PDivisibleGroup (CommRingCat.of R) p) :
    QuasiIsogeny ((F).obj (G.splitWithDual hExact)) (((F).obj G).splitWithDual hExact) :=
  RationalCategory.inclusion.mapIso (baseChangeSplitIso (S := S) G hExact)


end BaseChange
end Langlands.PDivisibleGroup
