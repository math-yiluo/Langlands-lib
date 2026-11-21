import Langlands.GroupScheme.Cartier.FiniteDualNaturalPairing
import Langlands.GroupScheme.Cartier.FiniteDualAffineCharacters

/-! # Additivity of actual finite Cartier dual morphisms -/

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.Cartier.FiniteDual

variable {R : CommRingCat.{u}}

private theorem points_comp_add {G H : CommGroupScheme (Spec R)}
    (f g : G ⟶ H) (T : Over (Spec R)) (x : T ⟶ G.X) :
    x ≫ (f + g).toMul.hom.hom = (x ≫ f.toMul.hom.hom) * (x ≫ g.toMul.hom.hom) :=
  MonObj.comp_mul _ _ _

attribute [local instance] finiteScheme_isAffine finiteScheme_cocomm finiteScheme_finite
  finiteScheme_projective

variable (G : CommGroupScheme (Spec R)) [IsFinite G.X.hom] [Flat G.X.hom]
  [LocallyOfFinitePresentation G.X.hom]

/-- Evaluation on all relative tests determines the actual dual point at an affine test. -/
theorem finiteSchemePairing_separates_dual (B : Type u) [CommRing B] [Algebra R B]
    {y z : specOver R B ⟶ (schemeDual G).X}
    (h : ∀ (T : Over (Spec R)) (a : T ⟶ specOver R B) (x : T ⟶ G.X),
      finiteSchemePairing G T (a ≫ y) x = finiteSchemePairing G T (a ≫ z) x) : y = z := by
  let A := AffineCoordinates.hopfAlgebra G.toGrp
  let e := AffineCoordinates.hopfSpecIso G.toGrp
  apply (affineCharacterEquiv R A B).injective
  change characterOfPoint R A y = characterOfPoint R A z
  apply relativeHom_ext
  intro T a x
  rw [characterOfPoint_local, characterOfPoint_local]
  have hz := h T a (x ≫ e.hom.hom.hom)
  have he : e.hom.hom.hom ≫ e.inv.hom.hom = 𝟙 (specOver R A) :=
    congrArg (fun f => f.hom.hom) e.hom_inv_id
  have hc : (x ≫ e.hom.hom.hom) ≫ e.inv.hom.hom = x := by
    rw [Category.assoc, he]
    exact Category.comp_id (show T ⟶ specOver R A from x)
  change schemePairing R A T (a ≫ y) ((x ≫ e.hom.hom.hom) ≫ e.inv.hom.hom) =
    schemePairing R A T (a ≫ z) ((x ≫ e.hom.hom.hom) ≫ e.inv.hom.hom) at hz
  rwa [hc] at hz

variable {G} {H : CommGroupScheme (Spec R)} [IsFinite H.X.hom] [Flat H.X.hom]
  [LocallyOfFinitePresentation H.X.hom]

/-- Dualizing a sum of group homomorphisms adds the actual dual homomorphisms. -/
theorem schemeDualMap_add (f g : G ⟶ H) :
    schemeDualMap (f + g) = schemeDualMap f + schemeDualMap g := by
  change Additive.ofMul (schemeDualMap (f + g)).toMul =
    Additive.ofMul (schemeDualMap f + schemeDualMap g).toMul
  apply congrArg Additive.ofMul
  apply Grp.hom_ext
  let B := Dual R (AffineCoordinates.hopfAlgebra H.toGrp)
  apply finiteSchemePairing_separates_dual G B
  intro T y x
  calc
    finiteSchemePairing G T (y ≫ (schemeDualMap (f + g)).toMul.hom.hom) x =
        finiteSchemePairing H T y (x ≫ (f + g).toMul.hom.hom) :=
      (finiteSchemePairing_dualMap (f + g) T x y).symm
    _ = finiteSchemePairing H T y (x ≫ f.toMul.hom.hom) *
        finiteSchemePairing H T y (x ≫ g.toMul.hom.hom) := by
      rw [points_comp_add, map_mul]
    _ = finiteSchemePairing G T (y ≫ (schemeDualMap f).toMul.hom.hom) x *
        finiteSchemePairing G T (y ≫ (schemeDualMap g).toMul.hom.hom) x :=
      congrArg₂ (· * ·) (finiteSchemePairing_dualMap f T x y) (finiteSchemePairing_dualMap g T x y)
    _ = finiteSchemePairing G T
        (y ≫ (schemeDualMap f + schemeDualMap g).toMul.hom.hom) x := by
      let y' : T ⟶ (schemeDual H).X := y
      have hsum := points_comp_add (schemeDualMap f) (schemeDualMap g) T y'
      exact (finiteSchemePairing_mul G T (y' ≫ (schemeDualMap f).toMul.hom.hom)
        (y' ≫ (schemeDualMap g).toMul.hom.hom) x).symm.trans
          (congrArg (fun t => finiteSchemePairing G T t x) hsum.symm)

/-- The dual arrows act additively on the actual Hom groups. -/
def schemeDualMapAdd : (G ⟶ H) →+ (schemeDual H ⟶ schemeDual G) :=
  AddMonoidHom.mk' schemeDualMap schemeDualMap_add

/-- Duality sends multiplication by a natural number to multiplication by the
same natural number on the actual dual group scheme. -/
theorem schemeDualMap_nsmul_id (n : ℕ) :
    schemeDualMap (n • (𝟙 G)) = n • (𝟙 (schemeDual G)) := by
  change schemeDualMapAdd (n • (𝟙 G)) = _
  rw [map_nsmul]
  exact congrArg (n • ·) schemeDualMap_id

end Langlands.GroupScheme.Cartier.FiniteDual
