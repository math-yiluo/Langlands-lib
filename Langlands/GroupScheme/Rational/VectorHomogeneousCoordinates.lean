import Langlands.GroupScheme.Lie.HomogeneousCoordinates
import Langlands.GroupScheme.Rational.VectorLinearAction
import Langlands.GroupScheme.CorepresentedAffineComparison

/-! # Homogeneous coordinates for actual linear vector actions -/

set_option backward.isDefEq.respectTransparency false

noncomputable section
universe u
open CategoryTheory Opposite AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.RelativeRoot

variable {k : Type u} [Field k]
    {V : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom V.X.hom]
    {d m : ℕ}
    (e : ∀ T : Over (Spec (CommRingCat.of k)),
      (T ⟶ V.X) ≃* Multiplicative (Fin d → Γ(T.left, ⊤)))
    (he : IsNaturalVectorCoordinates e)
    (v : Module.Basis (Fin m) k (Additive (lieKernel V k)))

/-- Change vector coordinates by the coefficient-natural transition to a Lie basis. -/
def vectorCoordinatesInBasis (T : Over (Spec (CommRingCat.of k))) :
    (T ⟶ V.X) ≃* Multiplicative (Fin m → Γ(T.left, ⊤)) where
  toFun x := Multiplicative.ofAdd
    ((finiteLieCoordinatesOfVector e he).basisTransition v
      (((algΓ (CommRingCat.of k)).obj T).unop) (e T x).toAdd)
  invFun x := (e T).symm (Multiplicative.ofAdd
    (((finiteLieCoordinatesOfVector e he).basisTransition v
      (((algΓ (CommRingCat.of k)).obj T).unop)).symm x.toAdd))
  left_inv x := by
    simp only [toAdd_ofAdd, LinearEquiv.symm_apply_apply, ofAdd_toAdd,
      MulEquiv.symm_apply_apply]
  right_inv x := by
    simp only [MulEquiv.apply_symm_apply, toAdd_ofAdd,
      LinearEquiv.apply_symm_apply, ofAdd_toAdd]
  map_mul' x y := by
    simp only [map_mul, toAdd_mul, map_add, ofAdd_add]

theorem vectorCoordinatesInBasis_natural :
    IsNaturalVectorCoordinates (vectorCoordinatesInBasis e he v) := by
  intro T W f x
  let fΓ : ((algΓ (CommRingCat.of k)).obj T).unop ⟶
      ((algΓ (CommRingCat.of k)).obj W).unop :=
    ((algΓ (CommRingCat.of k)).map f).unop
  change (finiteLieCoordinatesOfVector e he).basisTransition v
      (((algΓ (CommRingCat.of k)).obj W).unop) (e W (f ≫ x)).toAdd =
    fun i => fΓ.hom
      ((finiteLieCoordinatesOfVector e he).basisTransition v
        (((algΓ (CommRingCat.of k)).obj T).unop) (e T x).toAdd i)
  rw [he T W f]
  exact (finiteLieCoordinatesOfVector e he).basisTransition_naturality v fΓ _

/-- On an affine test, this is the same transition in the coefficient algebra. -/
theorem vectorAffineCoordinates_inBasis
    (A : CommAlgCat.{u} (CommRingCat.of k)) (x : Lie.AffinePoints V A) :
    (vectorAffineCoordinates (vectorCoordinatesInBasis e he v) A x).toAdd =
      (finiteLieCoordinatesOfVector e he).basisTransition v A
        (vectorAffineCoordinates e A x).toAdd := by
  let T := (algSpec (CommRingCat.of k)).obj (op A)
  let f := (Corepresented.affineSectionsIso A).hom
  have hf (z : ((algΓ (CommRingCat.of k)).obj T).unop) :
      f.hom z = (Scheme.ΓSpecIso (CommRingCat.of A)).hom z :=
    congrArg (fun g => g z) (Corepresented.affineSectionsIso_hom_ringHom A)
  have h := (finiteLieCoordinatesOfVector e he).basisTransition_naturality v f
    (e T x).toAdd
  have hf' : (fun i => f.hom ((e T x).toAdd i)) =
      (vectorAffineCoordinates e A x).toAdd := by
    funext i
    exact hf _
  rw [hf'] at h
  funext i
  exact (hf _).symm.trans (congrFun h i).symm

variable {e he v}
    {S : CommGroupScheme (Spec (CommRingCat.of k))}
    {b : AutomorphicAction S.toGrp V}

/-- The original action is diagonal on every affine test in homogeneous coordinates. -/
theorem IsLinearVectorCoordinates.homogeneous_affine_action
    (hb : IsLinearVectorCoordinates b e)
    (q : HomogeneousLieBasis b (𝟙 S.toGrp))
    (A : CommAlgCat.{u} (CommRingCat.of k))
    (s : Lie.AffinePoints S.toGrp A) (x : Lie.AffinePoints V A)
    (i : Fin q.dimension) :
    (vectorAffineCoordinates (vectorCoordinatesInBasis e hb.1 q.basis) A
      (b.act s x)).toAdd i =
        (Lie.characterValue (q.weight i) s : A) *
          (vectorAffineCoordinates (vectorCoordinatesInBasis e hb.1 q.basis) A x).toAdd i := by
  let c := finiteLieCoordinatesOfVector e hb.1
  let z := (vectorAffineCoordinates e A x).toAdd
  have h := q.differential_coordinates c A s ((c.equiv A).symm z) i
  simp only [Grp.id_hom_hom, Category.comp_id] at h
  have ht :
      c.basisTransition q.basis A (b.coordinateAction c A s z) i =
        (Lie.characterValue (q.weight i) s : A) *
          c.basisTransition q.basis A z i := by
    change (c.inBasis q.basis).equiv A
        ((c.equiv A).symm ((c.equiv A)
          (b.differential s ((c.equiv A).symm z)))) i = _
    rw [LinearEquiv.symm_apply_apply]
    exact h
  rw [hb.coordinateAction_eq] at ht
  simp only [z, ofAdd_toAdd, MulEquiv.symm_apply_apply] at ht
  rw [vectorAffineCoordinates_inBasis, vectorAffineCoordinates_inBasis]
  exact ht

end Langlands.GroupScheme.RelativeRoot
