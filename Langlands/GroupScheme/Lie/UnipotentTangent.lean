import Langlands.GroupScheme.Lie.RepresentationDifferential
import Langlands.GroupScheme.GeneralLinearDualNumberCoefficient
import Langlands.GroupScheme.Rational.UnipotentProductBound

/-! # Nilpotent actual tangent matrices of unipotent groups -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj Matrix

namespace Langlands.GroupScheme.MatrixRepresentation

open GeneralLinear.DualNumber

variable {R : CommRingCat.{u}} {G : GroupScheme (Spec R)} {n : ℕ}

/-- The affine matrix of a tangent point is precisely `1 + epsilon*M`. -/
theorem affineMatrix_lieKernel (ρ : MatrixRepresentation G (Fin n))
    (A : Type u) [CommRing A] [Algebra R A] (X : lieKernel G A) :
    ρ.affineMatrix (CommAlgCat.of R (DualNumber A)) X.val =
      matrixUnit (ρ.tangentMatrix A X) := by
  have h := congrArg Subtype.val (ρ.pointKernelEquiv_tangentMatrix A X)
  change pointUnit (ρ.tangentMatrix A X) = X.val ≫ ρ.hom.hom at h
  rw [affineMatrix_apply, ← h, pointUnit_matrix]

/-- The all-test product bound also holds in the affine algebra's coordinates. -/
theorem HasUnipotentProductBound.affine (ρ : MatrixRepresentation G (Fin n))
    {d : ℕ} (hρ : ρ.HasUnipotentProductBound d) (S : CommAlgCat.{u} R)
    (l : List ((algSpec R).obj (op S) ⟶ G.X)) (hl : d ≤ l.length) :
    (l.map (fun x => (ρ.affineMatrix S x).val - 1)).prod = 0 := by
  let f := (Corepresented.affineSectionsIso S).inv.hom.toRingHom
  have hf : Function.Injective f :=
    (ConcreteCategory.bijective_of_isIso (Corepresented.affineSectionsIso S).inv).1
  have hc (x : (algSpec R).obj (op S) ⟶ G.X) :
      f.mapMatrix ((ρ.affineMatrix S x).val - 1) =
        (ρ.pointMatrix ((algSpec R).obj (op S)) x).val - 1 := by
    rw [map_sub, map_one, pointMatrix_eq_affineMatrix]
    rfl
  have hmap : f.mapMatrix (l.map (fun x => (ρ.affineMatrix S x).val - 1)).prod =
      (l.map (fun x => (ρ.pointMatrix ((algSpec R).obj (op S)) x).val - 1)).prod := by
    rw [map_list_prod, List.map_map]
    simp only [Function.comp_def, hc]
    rfl
  have hz := hmap.trans (hρ _ l hl)
  apply Matrix.ext
  intro i j
  apply hf
  have h := congrArg (fun M => M i j) hz
  exact h.trans (map_zero f).symm

variable {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))}

/-- Successively differentiating the uniform ordered product identity, with a
new dual-number parameter at each step. -/
theorem tangentMatrix_pow_mul_differences_eq_zero
    (hG : IsUnipotent G) (ρ : MatrixRepresentation G (Fin n)) (r : ℕ) :
    ∀ (A : Type u) [CommRing A] [Algebra k A] (X : lieKernel G A)
      (l : List (Lie.AffinePoints G A)), r + l.length = n →
        (ρ.tangentMatrix A X) ^ r *
          (l.map (fun x => (ρ.affineMatrix (CommAlgCat.of k A) x).val - 1)).prod = 0 := by
  induction r with
  | zero =>
    intro A _ _ X l hl
    rw [pow_zero, one_mul]
    exact (hasUnipotentProductBound_of_isUnipotent hG n ρ).affine
      ρ (CommAlgCat.of k A) l (by omega)
  | succ r ih =>
    intro A _ _ X l hl
    let i : A →ₐ[k] DualNumber A := TrivSqZeroExt.inlAlgHom k A A
    let Y := lieKernelMap G i X
    let l' := l.map (Lie.constant G)
    have hlen : r + (X.val :: l').length = n := by
      simp only [List.length_cons, l', List.length_map]
      omega
    have hz := ih (DualNumber A) Y (X.val :: l') hlen
    have hM : ρ.tangentMatrix (DualNumber A) Y =
        (ρ.tangentMatrix A X).map (TrivSqZeroExt.inlHom A A) :=
      ρ.tangentMatrix_naturality i X
    have hconst (x : Lie.AffinePoints G A) :
        (ρ.affineMatrix (CommAlgCat.of k (DualNumber A)) (Lie.constant G x)).val - 1 =
          (TrivSqZeroExt.inlHom A A).mapMatrix
            ((ρ.affineMatrix (CommAlgCat.of k A) x).val - 1) := by
      rw [map_sub, map_one]
      change (ρ.affineMatrix (CommAlgCat.of k (DualNumber A))
        ((algSpec (CommRingCat.of k)).map (CommAlgCat.ofHom i).op ≫ x)).val - 1 = _
      rw [affineMatrix_naturality]
      rfl
    have hprod :
        (l'.map (fun x =>
          (ρ.affineMatrix (CommAlgCat.of k (DualNumber A)) x).val - 1)).prod =
        (TrivSqZeroExt.inlHom A A).mapMatrix
          (l.map (fun x => (ρ.affineMatrix (CommAlgCat.of k A) x).val - 1)).prod := by
      rw [map_list_prod]
      simp only [l', List.map_map, Function.comp_def, hconst]
    rw [hM, List.map_cons, List.prod_cons, affineMatrix_lieKernel,
      matrixUnit_val, add_sub_cancel_left, hprod, ← Matrix.map_pow, ← mul_assoc] at hz
    have he := congrArg epsilonCoefficient hz
    change epsilonCoefficient
      ((ρ.tangentMatrix A X ^ r).map (TrivSqZeroExt.inlHom A A) *
        epsilonMatrix (ρ.tangentMatrix A X) *
        ((l.map (fun x => (ρ.affineMatrix (CommAlgCat.of k A) x).val - 1)).prod).map
          (TrivSqZeroExt.inlHom A A)) = 0 at he
    rw [epsilonCoefficient_constant_sandwich] at he
    simpa only [pow_succ, mul_assoc] using he

/-- Every actual tangent matrix is nilpotent with exponent at most its dimension,
even for a tangent vector over a nonreduced test algebra. -/
theorem tangentMatrix_pow_eq_zero_of_isUnipotent (hG : IsUnipotent G)
    (ρ : MatrixRepresentation G (Fin n)) (A : Type u) [CommRing A] [Algebra k A]
    (X : lieKernel G A) : (ρ.tangentMatrix A X) ^ n = 0 := by
  simpa using tangentMatrix_pow_mul_differences_eq_zero hG ρ n A X [] (by simp)

/-- In particular the actual representation differential is nilpotent. -/
theorem isNilpotent_tangentMatrix_of_isUnipotent (hG : IsUnipotent G)
    (ρ : MatrixRepresentation G (Fin n)) (A : Type u) [CommRing A] [Algebra k A]
    (X : lieKernel G A) : IsNilpotent (ρ.tangentMatrix A X) :=
  ⟨n, tangentMatrix_pow_eq_zero_of_isUnipotent hG ρ A X⟩

end Langlands.GroupScheme.MatrixRepresentation
