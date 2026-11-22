import Langlands.GroupScheme.Cartier.FiniteDualProduct
import Langlands.GroupScheme.Torus.Lattice

/-! # Similitude of the actual alternating finite Cartier pairing -/

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1300000
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.Cartier.FiniteDual

variable {R : CommRingCat.{u}} {G H : CommGroupScheme (Spec R)}
variable [IsFinite G.X.hom] [Flat G.X.hom] [LocallyOfFinitePresentation G.X.hom]
variable [IsFinite H.X.hom] [Flat H.X.hom] [LocallyOfFinitePresentation H.X.hom]

/-- The evaluation pairing, viewed as a homomorphism of the actual dual points. -/
def finiteSchemePairingDual (G : CommGroupScheme (Spec R))
    [IsFinite G.X.hom] [Flat G.X.hom] [LocallyOfFinitePresentation G.X.hom]
    (T : Over (Spec R)) (x : T ⟶ G.X) : (T ⟶ (schemeDual G).X) →* (T ⟶ (Gm (Spec R)).X) :=
  MonoidHom.mk' (fun y => finiteSchemePairing G T y x)
    (fun y z => finiteSchemePairing_mul G T y z x)

private theorem comp_nsmul_toMul_hom {A B : CommGroupScheme (Spec R)} (T : Over (Spec R))
    (x : T ⟶ A.X) (f : A ⟶ B) (k : ℕ) :
    x ≫ (k • f).toMul.hom.hom = (x ≫ f.toMul.hom.hom) ^ k := by
  let L : (A ⟶ B) →+ Additive (T ⟶ B.X) := {
    toFun f := Additive.ofMul (x ≫ f.toMul.hom.hom)
    map_zero' := congrArg Additive.ofMul (MonObj.comp_one x)
    map_add' a b := congrArg Additive.ofMul (GroupScheme.comp_groupHom_add x a b) }
  exact congrArg Additive.toMul (map_nsmul L k f)

/-- The finite split map preserves the actual alternating evaluation up to the
integer multiplier given by composing the dual component with the adjoint. -/
theorem productWithDualPairing_similitude
    (f : G ⟶ H) (g : schemeDual G ⟶ schemeDual H) (k : ℕ)
    (h : g ≫ schemeDualMap f = k • (𝟙 (schemeDual G)))
    (T : Over (Spec R)) (x y : T ⟶ (productWithDual G).X) :
    let b := (productWithDualMap f g).toMul.hom.hom
    productWithDualPairing H T (x ≫ b) (y ≫ b) = (productWithDualPairing G T x y) ^ k := by
  have hpair (z : T ⟶ G.X) (w : T ⟶ (schemeDual G).X) :
      finiteSchemePairing H T (w ≫ g.toMul.hom.hom) (z ≫ f.toMul.hom.hom) =
        (finiteSchemePairing G T w z) ^ k := by
    have hmul := congrArg (fun a : schemeDual G ⟶ schemeDual G => w ≫ a.toMul.hom.hom) h
    change w ≫ (g.toMul.hom.hom ≫ (schemeDualMap f).toMul.hom.hom) =
      w ≫ (k • (𝟙 (schemeDual G))).toMul.hom.hom at hmul
    rw [← Category.assoc, comp_nsmul_toMul_hom T w (𝟙 (schemeDual G)) k] at hmul
    change (w ≫ g.toMul.hom.hom) ≫ (schemeDualMap f).toMul.hom.hom = (w ≫ 𝟙 _) ^ k at hmul
    rw [Category.comp_id] at hmul
    rw [finiteSchemePairing_dualMap f T z, hmul]
    exact (finiteSchemePairingDual G T z).map_pow w k
  dsimp only
  rw [productWithDualPairing_apply, productWithDualPairing_apply,
    productWithDualPoints_map, productWithDualPoints_map]
  dsimp only
  rw [hpair, hpair, mul_pow, inv_pow]

end Langlands.GroupScheme.Cartier.FiniteDual
