import Langlands.GroupScheme.Rational.VectorLieCoordinates
import Langlands.GroupScheme.Rational.CentralVectorQuotientStatement

/-! # A linear vector action agrees with its differential in vector coordinates -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.RelativeRoot

variable {k : Type u} [Field k]
    {H V : GroupScheme (Spec (CommRingCat.of k))} {d : ℕ}
    {b : AutomorphicAction H V}
    {e : ∀ T : Over (Spec (CommRingCat.of k)),
      (T ⟶ V.X) ≃* Multiplicative (Fin d → Γ(T.left, ⊤))}

/-- The actual action in the supplied coordinates is a linear automorphism
over every test scheme's ring of global functions. -/
def IsLinearVectorCoordinates.actionLinearEquiv
    (he : IsLinearVectorCoordinates b e)
    (T : Over (Spec (CommRingCat.of k))) (h : T ⟶ H.X) :
    (Fin d → Γ(T.left, ⊤)) ≃ₗ[Γ(T.left, ⊤)] (Fin d → Γ(T.left, ⊤)) where
  toFun x := (e T (b.act h ((e T).symm (Multiplicative.ofAdd x)))).toAdd
  invFun x := (e T (b.act h⁻¹ ((e T).symm (Multiplicative.ofAdd x)))).toAdd
  left_inv x := by
    simp only [ofAdd_toAdd, MulEquiv.symm_apply_apply, b.act_inv_act,
      MulEquiv.apply_symm_apply, toAdd_ofAdd]
  right_inv x := by
    simp only [ofAdd_toAdd, MulEquiv.symm_apply_apply, b.act_act_inv,
      MulEquiv.apply_symm_apply, toAdd_ofAdd]
  map_add' x y := by
    rw [ofAdd_add, map_mul, b.act_mul_right, map_mul, toAdd_mul]
  map_smul' c x := by
    have hlin := he.2 T h c ((e T).symm (Multiplicative.ofAdd x))
    simpa only [MulEquiv.apply_symm_apply, toAdd_ofAdd, RingHom.id_apply] using hlin

/-- The all-test scalar-linearity hypothesis holds in coefficient-algebra coordinates. -/
theorem IsLinearVectorCoordinates.vectorAffineCoordinates_smul
    (he : IsLinearVectorCoordinates b e)
    {A : Type u} [CommRing A] [Algebra k A]
    (h : Lie.AffinePoints H A) (c : A) (v : Lie.AffinePoints V A) :
    (vectorAffineCoordinates e A (b.act h
      ((vectorAffineCoordinates e A).symm
        (Multiplicative.ofAdd (c • (vectorAffineCoordinates e A v).toAdd))))).toAdd =
      c • (vectorAffineCoordinates e A (b.act h v)).toAdd := by
  let T := (algSpec (CommRingCat.of k)).obj (op (CommAlgCat.of k A))
  let r : Γ(T.left, ⊤) ≅ CommRingCat.of A := Scheme.ΓSpecIso (CommRingCat.of A)
  let q : T ⟶ V.X :=
    (e T).symm (Multiplicative.ofAdd ((r.inv c) • (e T v).toAdd))
  have hq : q = (vectorAffineCoordinates e A).symm
      (Multiplicative.ofAdd (c • (vectorAffineCoordinates e A v).toAdd)) := by
    apply (vectorAffineCoordinates e A).injective
    apply Multiplicative.toAdd.injective
    rw [MulEquiv.apply_symm_apply]
    funext j
    change r.hom ((e T q).toAdd j) = c * r.hom ((e T v).toAdd j)
    dsimp only [q]
    rw [MulEquiv.apply_symm_apply, toAdd_ofAdd]
    change r.hom (r.inv c * (e T v).toAdd j) = _
    rw [r.hom.hom.map_mul, r.inv_hom_id_apply]
  rw [← hq]
  have hlin := he.2 T h (r.inv c) v
  funext j
  change r.hom ((e T (b.act h q)).toAdd j) =
    c * r.hom ((e T (b.act h v)).toAdd j)
  rw [show (e T (b.act h q)).toAdd =
      (r.inv c) • (e T (b.act h v)).toAdd from hlin]
  change r.hom (r.inv c * (e T (b.act h v)).toAdd j) = _
  rw [r.hom.hom.map_mul, r.inv_hom_id_apply]

/-- Multiplying a constant vector by epsilon gives its actual tangent point. -/
theorem vectorLiePoint_eq_epsilon_smul
    (he : IsNaturalVectorCoordinates e)
    {A : Type u} [CommRing A] [Algebra k A]
    (v : Lie.AffinePoints V A) :
    (vectorLiePoint e he (vectorAffineCoordinates e A v).toAdd).val =
      (vectorAffineCoordinates e (DualNumber A)).symm
        (Multiplicative.ofAdd
          ((TrivSqZeroExt.inr (1 : A) : DualNumber A) •
            (vectorAffineCoordinates e (DualNumber A) (Lie.constant V v)).toAdd)) := by
  apply (vectorAffineCoordinates e (DualNumber A)).injective
  apply Multiplicative.toAdd.injective
  rw [vectorAffineCoordinates_vectorLiePoint, MulEquiv.apply_symm_apply, toAdd_ofAdd]
  change (fun j => TrivSqZeroExt.inr ((vectorAffineCoordinates e A v).toAdd j)) =
    (TrivSqZeroExt.inr (1 : A) : DualNumber A) •
      (vectorAffineCoordinates e (DualNumber A)
        (Lie.affineMap V (TrivSqZeroExt.inlAlgHom k A A) v)).toAdd
  rw [he.vectorAffineCoordinates_naturality]
  funext j
  apply TrivSqZeroExt.ext <;> simp

variable [IsAffineHom V.X.hom]

/-- The differential on a vector's epsilon point has the same coefficients as the
original linear action on that vector. -/
theorem IsLinearVectorCoordinates.vectorLieCoordinates_differential
    (he : IsLinearVectorCoordinates b e)
    (A : CommAlgCat.{u} (CommRingCat.of k))
    (h : Lie.AffinePoints H A) (v : Lie.AffinePoints V A) :
    vectorLieCoordinates e he.1 A
        (b.differential h
          (Additive.ofMul (vectorLiePoint e he.1 (vectorAffineCoordinates e A v).toAdd))) =
      (vectorAffineCoordinates e A (b.act h v)).toAdd := by
  funext j
  change ((vectorAffineCoordinates e (DualNumber A)
    (b.act (Lie.constant H h)
      (vectorLiePoint e he.1 (vectorAffineCoordinates e A v).toAdd).val)).toAdd j).snd = _
  rw [vectorLiePoint_eq_epsilon_smul, he.vectorAffineCoordinates_smul]
  simp only [Lie.constant]
  rw [← b.affineAct_naturality, he.1.vectorAffineCoordinates_naturality]
  change ((TrivSqZeroExt.inr (1 : A) : DualNumber A) *
    (TrivSqZeroExt.inlAlgHom k A A)
      ((vectorAffineCoordinates e A (b.act h v)).toAdd j)).snd =
    (vectorAffineCoordinates e A (b.act h v)).toAdd j
  simp

/-- In the induced finite Lie coordinates, the differential is the original
linear vector action over every coefficient algebra. -/
theorem IsLinearVectorCoordinates.coordinateAction_eq
    (he : IsLinearVectorCoordinates b e)
    (A : CommAlgCat.{u} (CommRingCat.of k))
    (h : Lie.AffinePoints H A) (x : Fin d → A) :
    b.coordinateAction (finiteLieCoordinatesOfVector e he.1) A h x =
      (vectorAffineCoordinates e A
        (b.act h ((vectorAffineCoordinates e A).symm (Multiplicative.ofAdd x)))).toAdd := by
  let v := (vectorAffineCoordinates e A).symm (Multiplicative.ofAdd x)
  have hv : (vectorAffineCoordinates e A v).toAdd = x :=
    congrArg Multiplicative.toAdd ((vectorAffineCoordinates e A).apply_symm_apply _)
  have hl := he.vectorLieCoordinates_differential A h v
  rw [hv] at hl
  exact hl

end Langlands.GroupScheme.RelativeRoot
