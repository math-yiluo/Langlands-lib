import Langlands.GroupScheme.Torus.WeilRestriction
import Langlands.GroupScheme.Torus.Split
import Langlands.Shimura.Unitary.DeligneGroupScheme

/-! # The Deligne torus is the Weil restriction `Res_{ℂ/ℝ} 𝔾ₘ` -/

noncomputable section

open CategoryTheory Opposite AlgebraicGeometry
open scoped TensorProduct CategoryTheory.MonObj

namespace Langlands.Shimura.DeligneTorus

variable (S : Type) [CommRing S] [Algebra ℝ S]

/-- The isomorphism `ℂ ⊗[ℝ] S ≃ Complexification S`: tensor commutativity followed by the
inverse of `tensorEquiv S`. -/
def complexTensorEquiv : ℂ ⊗[ℝ] S ≃ₐ[ℝ] Complexification S :=
  (Algebra.TensorProduct.comm ℝ ℂ S).trans ((tensorEquiv S).symm.restrictScalars ℝ)

@[simp] theorem complexTensorEquiv_tmul (z : ℂ) (s : S) :
    complexTensorEquiv S (z ⊗ₜ s) = s • complexMap S z :=
  rfl

/-- The isomorphism is `S`-linear for the action of `S` on the right tensor factor. -/
theorem complexTensorEquiv_mul_tmul (x : ℂ ⊗[ℝ] S) (s : S) :
    complexTensorEquiv S (x * (1 ⊗ₜ s)) = s • complexTensorEquiv S x := by
  rw [map_mul, complexTensorEquiv_tmul, map_one, mul_comm, Algebra.smul_def, Algebra.smul_def,
    mul_one]

/-- The isomorphism commutes with every map of real algebras. -/
theorem complexTensorEquiv_natural {S T : Type} [CommRing S] [Algebra ℝ S] [CommRing T]
    [Algebra ℝ T] (φ : S →ₐ[ℝ] T) (x : ℂ ⊗[ℝ] S) :
    complexTensorEquiv T (Algebra.TensorProduct.lTensor (S := ℂ) ℂ φ x) =
      map φ.toRingHom (complexTensorEquiv S x) := by
  induction x using TensorProduct.inductionOn with
  | tmul z s =>
    ext <;> simp
  | add x y hx hy =>
    simp only [map_add, hx, hy]

/-- Points of `Res_{ℂ/ℝ} 𝔾ₘ` in the quadratic model of the Deligne torus. -/
def weilPointsEquiv (T : Over (Spec (CommRingCat.of ℝ))) :
    (T ⟶ (GroupScheme.WeilGm.groupScheme (CommRingCat.of ℝ) ℂ).X) ≃*
      Points ((algΓ (CommRingCat.of ℝ)).obj T).unop :=
  (GroupScheme.WeilGm.pointsEquiv (CommRingCat.of ℝ) ℂ T).trans
    (Units.mapEquiv (complexTensorEquiv ((algΓ (CommRingCat.of ℝ)).obj T).unop).toMulEquiv)

/-- Points of the Deligne group scheme in its quadratic model. -/
abbrev deligneSchemePointsEquiv (T : Over (Spec (CommRingCat.of ℝ))) :
    (T ⟶ groupScheme.X) ≃* Points ((algΓ (CommRingCat.of ℝ)).obj T).unop :=
  GroupScheme.Corepresented.pointsEquiv (R := CommRingCat.of ℝ) functor corepresentableBy T

/-- The quadratic model of the points of `Res_{ℂ/ℝ} 𝔾ₘ` is natural in the test scheme. -/
theorem weilPointsEquiv_naturality {T T' : Over (Spec (CommRingCat.of ℝ))} (a : T' ⟶ T)
    (x : T ⟶ (GroupScheme.WeilGm.groupScheme (CommRingCat.of ℝ) ℂ).X) :
    weilPointsEquiv T' (a ≫ x) =
      (functor.map ((algΓ (CommRingCat.of ℝ)).map a).unop).hom (weilPointsEquiv T x) := by
  apply Units.ext
  change complexTensorEquiv ((algΓ (CommRingCat.of ℝ)).obj T').unop
    (GroupScheme.WeilGm.pointsEquiv _ ℂ T' (a ≫ x)).val = _
  rw [GroupScheme.WeilGm.pointsEquiv_naturality]
  exact complexTensorEquiv_natural ((algΓ (CommRingCat.of ℝ)).map a).unop.hom _

/-- `Res_{ℂ/ℝ} 𝔾ₘ` is the Deligne torus. -/
def weilRestrictionIso :
    GroupScheme.WeilGm.groupScheme (CommRingCat.of ℝ) ℂ ≅ groupScheme :=
  GroupScheme.isoOfPointModels
    (fun T : Over (Spec (CommRingCat.of ℝ)) => Points ((algΓ (CommRingCat.of ℝ)).obj T).unop)
    (fun a => (functor.map ((algΓ (CommRingCat.of ℝ)).map a).unop).hom)
    weilPointsEquiv deligneSchemePointsEquiv
    (fun a x => weilPointsEquiv_naturality a x)
    (fun a y => GroupScheme.Corepresented.pointsEquiv_naturality (R := CommRingCat.of ℝ)
      functor corepresentableBy a y)

/-- On the points over `T`, the isomorphism is the unit map of `complexTensorEquiv Γ(T)`. -/
theorem weilRestrictionIso_hom_points (T : Over (Spec (CommRingCat.of ℝ)))
    (x : T ⟶ (GroupScheme.WeilGm.groupScheme (CommRingCat.of ℝ) ℂ).X) :
    deligneSchemePointsEquiv T (x ≫ weilRestrictionIso.hom.hom.hom) =
      Units.map (complexTensorEquiv ((algΓ (CommRingCat.of ℝ)).obj T).unop).toMonoidHom
        (GroupScheme.WeilGm.pointsEquiv (CommRingCat.of ℝ) ℂ T x) :=
  GroupScheme.isoOfPointModels_hom
    (fun T : Over (Spec (CommRingCat.of ℝ)) => Points ((algΓ (CommRingCat.of ℝ)).obj T).unop)
    (fun a => (functor.map ((algΓ (CommRingCat.of ℝ)).map a).unop).hom)
    weilPointsEquiv deligneSchemePointsEquiv
    (fun a x => weilPointsEquiv_naturality a x)
    (fun a y => GroupScheme.Corepresented.pointsEquiv_naturality (R := CommRingCat.of ℝ)
      functor corepresentableBy a y) T x

end Langlands.Shimura.DeligneTorus
