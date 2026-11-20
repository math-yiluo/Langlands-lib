import Langlands.AbelianScheme.Torsion
import Langlands.GroupScheme.Torus.WeilRestrictionGaloisPoints

/-! # Tensor-unit coordinates of torsion in the Weil group -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped TensorProduct CategoryTheory.MonObj

namespace Langlands.GroupScheme.WeilGm

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {F B : Type u} [Field F] [CommRing B] [Algebra F B] [Module.Finite F B]

local notation "A" => CommRingCat.of F
local notation "W" => groupScheme A B

/-- The actual torsion subgroup of the Weil restriction of `Gₘ`. -/
def weilTorsion (F B : Type u) [Field F] [CommRing B] [Algebra F B] [Module.Finite F B]
    (n : ℕ) : GroupScheme (Spec (CommRingCat.of F)) :=
  letI := (commGroupScheme (CommRingCat.of F) B).comm
  torsion (groupScheme (CommRingCat.of F) B) (n : ℤ)

/-- The canonical inclusion of the torsion subgroup. -/
def weilTorsionInclusion (n : ℕ) : weilTorsion F B n ⟶ W :=
  letI := (commGroupScheme A B).comm
  torsionι W (n : ℤ)

private abbrev affineTest (R : CommAlgCat.{u} A) := (algSpec A).obj (op R)

/-- On any affine test algebra the Weil torsion points are the roots of unity in the
original coefficient tensor. -/
def weilTorsionAffineEquiv (n : ℕ) (R : CommAlgCat.{u} A) :
    (weilTorsion F B n).affinePoints R ≃* rootsOfUnity n (B ⊗[F] R) := by
  letI := (commGroupScheme A B).comm
  let T := affineTest R
  let e := affineUnitsEquiv A B R
  refine (torsionPointsEquiv W (n : ℤ) T).trans
    { toFun := fun x => ⟨e x.val, (mem_rootsOfUnity n _).mpr ?_⟩
      invFun := fun t => ⟨e.symm t.val, (mem_torsionPoints W (n : ℤ) T _).mpr ?_⟩
      left_inv := fun x => Subtype.ext (e.symm_apply_apply x.val)
      right_inv := fun t => Subtype.ext (e.apply_symm_apply t.val)
      map_mul' := fun x y => Subtype.ext (map_mul e x.val y.val) }
  · have hx : x.val ^ n = 1 := by
      simpa only [zpow_natCast] using (mem_torsionPoints W (n : ℤ) T _).mp x.property
    rw [← map_pow, hx, map_one]
  · have ht := (mem_rootsOfUnity n _).mp t.property
    change e.symm t.val ^ (n : ℤ) = 1
    rw [zpow_natCast, ← map_pow, ht, map_one]

/-- The unit of a torsion point is its image under the inclusion into the Weil group. -/
theorem weilTorsionAffineEquiv_val (n : ℕ) (R : CommAlgCat.{u} A)
    (x : (weilTorsion F B n).affinePoints R) :
    (weilTorsionAffineEquiv n R x).val =
      affineUnitsEquiv A B R (x ≫ (weilTorsionInclusion n).hom.hom) := rfl

/-- The root-of-unity model uses coefficient extension on the right tensor factor. -/
theorem weilTorsionAffineEquiv_val_naturality (n : ℕ) {R S : CommAlgCat.{u} A}
    (g : R ⟶ S) (x : (weilTorsion F B n).affinePoints R) :
    (weilTorsionAffineEquiv n S ((weilTorsion F B n).affinePointMap g x)).val =
      Units.map (Algebra.TensorProduct.lTensor (S := B) B g.hom).toMonoidHom
        (weilTorsionAffineEquiv n R x).val := by
  rw [weilTorsionAffineEquiv_val, weilTorsionAffineEquiv_val]
  change affineUnitsEquiv A B S (((algSpec A).map g.op ≫ x) ≫
    (weilTorsionInclusion n).hom.hom) = _
  rw [Category.assoc, affineUnitsEquiv_naturality]

end Langlands.GroupScheme.WeilGm
