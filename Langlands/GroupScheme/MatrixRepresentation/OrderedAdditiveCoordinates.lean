import Langlands.GroupScheme.MatrixRepresentation.OrderedAdditiveProducts
import Langlands.GroupScheme.MatrixRepresentation.AffineCoefficients
import Langlands.GroupScheme.Rational.OrderedProductPoints

/-! # Coordinate pullback of an actual ordered additive product -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj Matrix

namespace Langlands.GroupScheme.MatrixRepresentation.OrderedAdditiveCoordinates

open OrderedAdditiveProducts

variable {k : Type u} [Field k]
    {G : GroupScheme (Spec (.of k))} [IsAffineHom G.X.hom] {d : ℕ}
    (x : Fin d → (VectorGroup.groupScheme (.of k) 1 ⟶ G))

private theorem affinePoint_naturality {A B : CommAlgCat.{u} k}
    (f : A ⟶ B) (t : Fin 1 → A) :
    (algSpec (.of k)).map f.op ≫
        VectorGroup.affinePoint (R := .of k) A t =
      VectorGroup.affinePoint (R := .of k) B (fun i => f.hom (t i)) := by
  unfold VectorGroup.affinePoint
  rw [← Functor.map_comp]
  congr 1
  apply Quiver.Hom.unop_inj
  apply CommAlgCat.hom_ext
  apply MvPolynomial.algHom_ext
  intro i
  simp only [unop_comp, Quiver.Hom.unop_op, CommAlgCat.hom_comp,
    CommAlgCat.hom_ofHom, AlgHom.comp_apply, MvPolynomial.aeval_X]

omit [IsAffineHom G.X.hom] in
/-- Ordered multiplication commutes with every change of test algebra. -/
theorem orderedPoint_naturality {A B : CommAlgCat.{u} k}
    (f : A ⟶ B) (t : Fin d → A) :
    Lie.affineMap G f.hom (orderedPoint x A t) =
      orderedPoint x B (fun i => f.hom (t i)) := by
  change (algSpec (.of k)).map f.op ≫
      RelativeRoot.orderedPoints x
        (fun i => VectorGroup.affinePoint (R := .of k) A (fun _ => t i)) = _
  rw [RelativeRoot.orderedPoints_naturality]
  unfold RelativeRoot.orderedPoints orderedPoint
  simp only [affinePoint_naturality]

omit [IsAffineHom G.X.hom] in
@[simp]
theorem orderedPoint_zero (A : CommAlgCat.{u} k) :
    orderedPoint x A 0 = 1 := by
  unfold orderedPoint
  have h (i : Fin d) :
      VectorGroup.affinePoint A (fun _ : Fin 1 => (0 : Fin d → A) i) ≫
        (x i).hom.hom = 1 := by
    change VectorGroup.affinePoint A (0 : Fin 1 → A) ≫ (x i).hom.hom = 1
    rw [VectorGroup.affinePoint_zero, MonObj.one_comp]
  simp only [h, List.ofFn_const, List.prod_replicate, one_pow]

/-- The actual coordinate pullback, evaluated at the universal ordered point. -/
def coordinateMap : CharacterUnits.Coord G →ₐ[k] MvPolynomial (Fin d) k :=
  Lie.pointCoordinates G
    (orderedPoint x (.of k (MvPolynomial (Fin d) k)) MvPolynomial.X)

/-- Evaluating the actual ordered-coordinate pullback gives the original point. -/
theorem pointCoordinates_orderedPoint (A : CommAlgCat.{u} k) (t : Fin d → A) :
    Lie.pointCoordinates G (orderedPoint x A t) =
      (MvPolynomial.aeval t).comp (coordinateMap x) := by
  have h := Lie.pointCoordinates_naturality G (MvPolynomial.aeval t)
    (orderedPoint x (.of k (MvPolynomial (Fin d) k)) MvPolynomial.X)
  have hn := orderedPoint_naturality x
    (CommAlgCat.ofHom (MvPolynomial.aeval t) :
      CommAlgCat.of k (MvPolynomial (Fin d) k) ⟶ A) MvPolynomial.X
  simp only [CommAlgCat.hom_ofHom, MvPolynomial.aeval_X] at hn
  rw [hn] at h
  exact h

/-- The ordered-coordinate map preserves the actual identity evaluation. -/
theorem coordinateMap_origin (a : CharacterUnits.Coord G) :
    (coordinateMap x a).coeff 0 = Lie.coordinateOrigin G a := by
  have h := pointCoordinates_orderedPoint x (.of k k) 0
  rw [orderedPoint_zero] at h
  have ha := DFunLike.congr_fun h a
  change Lie.coordinateOrigin G a =
    MvPolynomial.aeval (0 : Fin d → k) (coordinateMap x a) at ha
  simpa only [MvPolynomial.aeval_eq_eval, MvPolynomial.eval_zero,
    MvPolynomial.constantCoeff_eq] using ha.symm

/-- Bijectivity of this actual pullback supplies the ordered polynomial coordinates. -/
def coordinateEquiv (hx : Function.Bijective (coordinateMap x)) :
    CharacterUnits.Coord G ≃ₐ[k] MvPolynomial (Fin d) k :=
  AlgEquiv.ofBijective (coordinateMap x) hx

@[simp]
theorem coordinateEquiv_apply (hx : Function.Bijective (coordinateMap x))
    (a : CharacterUnits.Coord G) :
    coordinateEquiv x hx a = coordinateMap x a := rfl

/-- When the actual ordered pullback is bijective, every affine point has a
unique ordered parameter tuple. -/
theorem orderedPoint_bijective (hx : Function.Bijective (coordinateMap x))
    (A : CommAlgCat.{u} k) : Function.Bijective (orderedPoint x A) := by
  constructor
  · intro t s h
    have he := congrArg (Lie.pointCoordinates G) h
    rw [pointCoordinates_orderedPoint, pointCoordinates_orderedPoint] at he
    funext i
    have hi := DFunLike.congr_fun he
      ((coordinateEquiv x hx).symm (MvPolynomial.X i))
    simpa only [AlgHom.comp_apply, ← coordinateEquiv_apply x hx,
      AlgEquiv.apply_symm_apply, MvPolynomial.aeval_X] using hi
  · intro g
    let F := (Lie.pointCoordinates G g).comp (coordinateEquiv x hx).symm.toAlgHom
    let t : Fin d → A := fun i => F (MvPolynomial.X i)
    refine ⟨t, ?_⟩
    apply (Lie.pointCoordinates G).injective
    rw [pointCoordinates_orderedPoint]
    have hF : MvPolynomial.aeval t = F := by
      apply MvPolynomial.algHom_ext
      intro i
      exact MvPolynomial.aeval_X t i
    rw [hF]
    ext a
    change Lie.pointCoordinates G g
      ((coordinateEquiv x hx).symm (coordinateEquiv x hx a)) =
        Lie.pointCoordinates G g a
    rw [AlgEquiv.symm_apply_apply]

variable {n : Type} [Fintype n] [DecidableEq n]
    (ρ : MatrixRepresentation G n)

/-- The ordered polynomial matrix is the actual universal matrix pulled back
by the canonical ordered-coordinate map. -/
theorem universalCharacterMatrix_coordinateMap :
    ρ.universalCharacterMatrix.map (coordinateMap x) = actionPolynomial ρ x := by
  have h := AffineCoefficients.universalCharacterMatrix_map ρ
    (.of k (MvPolynomial (Fin d) k))
    (orderedPoint x (.of k (MvPolynomial (Fin d) k)) MvPolynomial.X)
  have he := actionPolynomial_aeval ρ x (.of k (MvPolynomial (Fin d) k)) MvPolynomial.X
  have hX : MvPolynomial.aeval (MvPolynomial.X : Fin d → MvPolynomial (Fin d) k) =
      AlgHom.id k (MvPolynomial (Fin d) k) := by
    apply MvPolynomial.algHom_ext
    intro i
    exact MvPolynomial.aeval_X _ i
  rw [hX] at he
  change actionPolynomial ρ x = _ at he
  exact h.trans (by simpa only [Matrix.map_id] using he.symm)

end Langlands.GroupScheme.MatrixRepresentation.OrderedAdditiveCoordinates
