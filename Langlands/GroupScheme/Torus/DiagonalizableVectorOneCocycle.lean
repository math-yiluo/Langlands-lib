import Langlands.GroupScheme.Torus.DiagonalizableVectorCocycle
import Langlands.GroupScheme.Rational.SplitTorusVectorCocycle

/-! # Linear vector one-cocycles on diagonalizable groups are coboundaries -/

noncomputable section
universe u
open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory

namespace Langlands.GroupScheme.diagonalizableVectorOneCocycle
open RelativeRoot

variable {k : Type u} [Field k] (Λ : Type u) [AddCommGroup Λ]
    {V : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom V.X.hom]
    (a : AutomorphicAction (Diagonalizable.groupScheme (CommRingCat.of k) Λ).toGrp V)
    {d : ℕ}
    (e : ∀ T : Over (Spec (CommRingCat.of k)),
      (T ⟶ V.X) ≃* Multiplicative (Fin d → Γ(T.left, ⊤)))
    (he : IsLinearVectorCoordinates a e)
    (c : a.Cocycle (Over.mk (𝟙 (Spec (CommRingCat.of k)))))

local notation "𝔻" => CommGroupScheme.toGrp (Diagonalizable.groupScheme (CommRingCat.of k) Λ)

/-- The coordinate vector of the cocycle on an affine test point. -/
def coordinates {A : Type u} [CommRing A] [Algebra k A]
    (t : Lie.AffinePoints (𝔻) A) : Fin d → A :=
  (vectorAffineCoordinates e A (c.affineEval t)).toAdd

/-- The degree-zero coefficient of the cocycle at the universal point. -/
def constant : Fin d → k :=
  fun j => (coordinates Λ a e c
    (Diagonalizable.Averaging.universalPoint (CommRingCat.of k) Λ) j).coeff 0

omit [IsAffineHom V.X.hom] in
include he in
/-- Cocycle coordinates commute with extension of coefficients. -/
theorem coordinates_naturality
    {A B : Type u} [CommRing A] [Algebra k A] [CommRing B] [Algebra k B]
    (f : A →ₐ[k] B) (t : Lie.AffinePoints (𝔻) A) :
    coordinates Λ a e c (Lie.affineMap _ f t) = fun j => f (coordinates Λ a e c t j) := by
  simp only [coordinates, ← c.affineEval_naturality,
    he.1.vectorAffineCoordinates_naturality]

omit [IsAffineHom V.X.hom] in
include he in
/-- The degree-zero coefficient at the extended universal point is the constant vector. -/
theorem coeff_zero_point {A : Type u} [CommRing A] [Algebra k A] :
    (fun j => (coordinates Λ a e c
      (Diagonalizable.Averaging.point (CommRingCat.of k) Λ A) j).coeff 0) =
      fun j => algebraMap k A (constant Λ a e c j) := by
  rw [Diagonalizable.Averaging.point, coordinates_naturality Λ a e he c]
  funext j
  exact AddMonoidAlgebra.coeff_mapAlgHom _ _ _

include he in
/-- The degree-zero coefficient gives the coboundary formula on every affine test. -/
theorem coordinates_eq_constant_sub_action
    {A : Type u} [CommRing A] [Algebra k A] (t : Lie.AffinePoints (𝔻) A) :
    coordinates Λ a e c t =
      (fun j => algebraMap k A (constant Λ a e c j)) -
        (vectorAffineCoordinates e A (a.act t ((vectorAffineCoordinates e A).symm
          (Multiplicative.ofAdd fun j => algebraMap k A (constant Λ a e c j))))).toAdd := by
  let P := Diagonalizable.Averaging.point (CommRingCat.of k) Λ A
  let t' := Lie.affineMap _ (Diagonalizable.Averaging.const (CommRingCat.of k) Λ A) t
  let τ := (Diagonalizable.Averaging.translation Λ
    (Diagonalizable.Averaging.pointsEquiv (CommRingCat.of k) Λ A t)).restrictScalars k
  -- the cocycle identity at `t' * P`, in coordinates
  have hmul := congrArg
    (fun x : Lie.AffinePoints V (AddMonoidAlgebra A Λ) =>
      fun j => ((vectorAffineCoordinates e (AddMonoidAlgebra A Λ) x).toAdd j).coeff 0)
    (c.affineEval_mul t' P)
  simp only [map_mul, toAdd_mul] at hmul
  -- left side: translation invariance of the degree-zero coefficient
  have hleft : (fun j => ((vectorAffineCoordinates e (AddMonoidAlgebra A Λ)
      (c.affineEval (t' * P))).toAdd j).coeff 0) =
      fun j => algebraMap k A (constant Λ a e c j) := by
    have htr := Diagonalizable.Averaging.translation_point (CommRingCat.of k) Λ t
    change Lie.affineMap _ τ P = t' * P at htr
    rw [← htr, ← coeff_zero_point Λ a e he c]
    funext j
    change (coordinates Λ a e c (Lie.affineMap _ τ P) j).coeff 0 = _
    rw [coordinates_naturality Λ a e he c]
    exact Diagonalizable.Averaging.coeff_zero_translation Λ _ _
  -- first term on the right: a constant point
  have hfirst : (fun j => ((vectorAffineCoordinates e (AddMonoidAlgebra A Λ)
      (c.affineEval t')).toAdd j).coeff 0) = coordinates Λ a e c t := by
    rw [← c.affineEval_naturality]
    exact diagonalizableVectorCocycle.coeff_zero_coefficientInclusion Λ a e he _
  -- second term on the right: the action of a constant point
  have hsecond : (fun j => ((vectorAffineCoordinates e (AddMonoidAlgebra A Λ)
      (a.act t' (c.affineEval P))).toAdd j).coeff 0) =
      (vectorAffineCoordinates e A (a.act t ((vectorAffineCoordinates e A).symm
          (Multiplicative.ofAdd fun j => algebraMap k A (constant Λ a e c j))))).toAdd := by
    rw [diagonalizableVectorCocycle.coeff_zero_act Λ a e he t]
    have hP := coeff_zero_point Λ a e he c (A := A)
    simp only [coordinates] at hP
    rw [hP]
  have hsum : (fun j => algebraMap k A (constant Λ a e c j)) =
      coordinates Λ a e c t +
        (vectorAffineCoordinates e A (a.act t ((vectorAffineCoordinates e A).symm
          (Multiplicative.ofAdd fun j => algebraMap k A (constant Λ a e c j))))).toAdd := by
    rw [← hfirst, ← hsecond, ← hleft]
    funext j
    have := congrFun hmul j
    simpa only [Pi.add_apply, AddMonoidAlgebra.coeff_add, Finsupp.add_apply] using this
  exact (eq_sub_iff_add_eq).2 hsum.symm

/-- The actual rational point given by the constant vector. -/
def conjugator : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ V.X :=
  (Lie.affineSelfTestIso (CommRingCat.of k)).inv ≫
    (vectorAffineCoordinates e k).symm (Multiplicative.ofAdd (constant Λ a e c))

omit [IsAffineHom V.X.hom] in
include he in
/-- The rational conjugator restricts to the scalar extension of its constant vector. -/
theorem conjugator_coordinates {A : Type u} [CommRing A] [Algebra k A] :
    vectorAffineCoordinates e A
      (AutomorphicAction.Cocycle.baseMap _ ≫ conjugator Λ a e c) =
      Multiplicative.ofAdd fun j => algebraMap k A (constant Λ a e c j) := by
  rw [conjugator, ← Category.assoc, Lie.baseMap_comp_affineSelfTestIso_inv]
  change vectorAffineCoordinates e A (Lie.affineMap V (Algebra.ofId k A) _) = _
  apply Multiplicative.toAdd.injective
  rw [he.1.vectorAffineCoordinates_naturality, MulEquiv.apply_symm_apply]
  rfl

include he in
/-- Every actual one-cocycle of a diagonalizable group acting linearly on a vector
group, with any character group, is an actual rational coboundary. -/
theorem cocycle_eq_coboundary : c = a.coboundary (conjugator Λ a e c) := by
  have : IsAffine (𝔻).X.left :=
    isAffine_of_isAffineHom (Diagonalizable.groupScheme (CommRingCat.of k) Λ).X.hom
  apply AutomorphicAction.Cocycle.affineEval_ext
  intro A t
  apply (vectorAffineCoordinates e A).injective
  apply Multiplicative.toAdd.injective
  have hq := conjugator_coordinates Λ a e he c (A := A)
  have hc := coordinates_eq_constant_sub_action Λ a e he c t
  rw [← hq, MulEquiv.symm_apply_apply] at hc
  change coordinates Λ a e c t = _
  rw [hc]
  simp only [AutomorphicAction.Cocycle.affineEval, AutomorphicAction.eval_coboundary,
    a.act_inv, map_mul, map_inv, toAdd_mul, toAdd_inv, hq, toAdd_ofAdd, sub_eq_add_neg]

include he in
/-- Existence form. -/
theorem exists_coboundary : ∃ v : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ V.X,
    c = a.coboundary v :=
  ⟨conjugator Λ a e c, cocycle_eq_coboundary Λ a e he c⟩

end Langlands.GroupScheme.diagonalizableVectorOneCocycle
