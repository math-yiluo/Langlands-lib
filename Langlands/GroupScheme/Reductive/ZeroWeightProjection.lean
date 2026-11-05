import Langlands.GroupScheme.Rational.CharacterRestrictionFiniteIndex
import Langlands.GroupScheme.Reductive.InvariantPolynomialDescent
import Langlands.GroupScheme.MatrixRepresentation.NormalFixedCoordinates
import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-! # Polynomial pullback along the central zero-weight projection -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped Matrix CategoryTheory.MonObj

namespace Langlands.GroupScheme.MatrixRepresentation

section LinearPullback

variable {k : Type u} [CommRing k]
  {n : Type} [Fintype n] [DecidableEq n]

/-- Pull a polynomial back along a coordinate linear map. -/
def linearPullback (P : Matrix n n k) (F : MvPolynomial n k) : MvPolynomial n k :=
  MvPolynomial.eval₂ MvPolynomial.C
    (fun i => ∑ j, MvPolynomial.C (P i j) * MvPolynomial.X j) F

omit [DecidableEq n] in
/-- Polynomial substitution evaluates as the corresponding scalar-extended matrix. -/
theorem eval₂_linearPullback (P : Matrix n n k) (F : MvPolynomial n k)
    {A : Type*} [CommRing A] (f : k →+* A) (x : n → A) :
    MvPolynomial.eval₂ f x (linearPullback P F) =
      MvPolynomial.eval₂ f (P.map f *ᵥ x) F := by
  rw [linearPullback, ← MvPolynomial.eval₂_assoc]
  congr 1
  funext i
  simp [Matrix.mulVec, dotProduct]

omit [DecidableEq n] in
/-- Linear pullback preserves each specified homogeneous degree. -/
theorem linearPullback_isHomogeneous (P : Matrix n n k) {F : MvPolynomial n k}
    {d : ℕ} (hF : F.IsHomogeneous d) :
    (linearPullback P F).IsHomogeneous d := by
  simpa only [linearPullback, Nat.one_mul] using hF.eval₂ (n := 1) MvPolynomial.C
    (fun i => ∑ j, MvPolynomial.C (P i j) * MvPolynomial.X j)
    (fun c => MvPolynomial.isHomogeneous_C _ c)
    (by
      intro i
      apply MvPolynomial.IsHomogeneous.sum
      intro j _
      exact MvPolynomial.isHomogeneous_C_mul_X (P i j) j)

omit [DecidableEq n] in
/-- A matrix fixing a vector preserves every polynomial value there. -/
theorem eval_linearPullback_of_fixed (P : Matrix n n k) (F : MvPolynomial n k)
    (v : n → k) (hv : P *ᵥ v = v) :
    MvPolynomial.eval v (linearPullback P F) = MvPolynomial.eval v F := by
  have h := eval₂_linearPullback P F (RingHom.id k) v
  have hP : P.map (RingHom.id k) = P := rfl
  simpa only [MvPolynomial.eval₂_id, hP, hv] using h

variable {G : GroupScheme (Spec (CommRingCat.of k))}

/-- Pullback by a commuting linear map preserves all-test-scheme invariance. -/
theorem IsInvariantPolynomial.linearPullback {ρ : MatrixRepresentation G n}
    {F : MvPolynomial n k} (hF : ρ.IsInvariantPolynomial F) (P : Matrix n n k)
    (hP : ∀ (T : Over (Spec (CommRingCat.of k))) (g : T ⟶ G.X),
      P.map (scalarMap T) * (ρ.pointMatrix T g : Matrix n n Γ(T.left, ⊤)) =
        (ρ.pointMatrix T g : Matrix n n Γ(T.left, ⊤)) * P.map (scalarMap T)) :
    ρ.IsInvariantPolynomial (linearPullback P F) := by
  intro T g x
  rw [eval₂_linearPullback, eval₂_linearPullback, Matrix.mulVec_mulVec,
    hP T g, ← Matrix.mulVec_mulVec]
  exact hF T g _

end LinearPullback

namespace CentralZeroWeight

open splitTorus CharacterRestrictionFiniteIndex

set_option backward.isDefEq.respectTransparency false

variable {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))}
  {N : ℕ} (ρ : MatrixRepresentation G (Fin N))
  (I : Type u) [Fintype I] [DecidableEq I]
  (j : splitTorus (Spec (CommRingCat.of k)) I ⟶ G)

/-- The coefficient of the trivial character in the universal torus matrix. -/
def projection : Matrix (Fin N) (Fin N) k :=
  weight ρ I j 0

/-- The trivial-weight coefficient is an idempotent. -/
theorem projection_mul_self :
    projection ρ I j * projection ρ I j = projection ρ I j := by
  simpa only [projection, ite_true] using weight_mul_weight ρ I j 0 0

/-- Torus-fixed vectors are fixed by the trivial-weight projection. -/
theorem projection_fixed (v : Fin N → k) (hv : (ρ.restrict j).IsFixedVector v) :
    projection ρ I j *ᵥ v = v := by
  classical
  let A := CommAlgCat.of (CommRingCat.of k) (AddMonoidAlgebra k (I → ℤ))
  have h := hv.affine A (universalPoint (R := CommRingCat.of k) I)
  rw [affineMatrix_restrict] at h
  change (universalMatrix ρ I j : Matrix (Fin N) (Fin N)
    (AddMonoidAlgebra k (I → ℤ))) *ᵥ
      (fun b => algebraMap k (AddMonoidAlgebra k (I → ℤ)) (v b)) =
      (fun b => algebraMap k (AddMonoidAlgebra k (I → ℤ)) (v b)) at h
  funext a
  have ha := congrArg (fun z : AddMonoidAlgebra k (I → ℤ) => z.coeff 0) (congrFun h a)
  simpa only [affineMatrix_apply, Category.assoc, Matrix.mulVec, dotProduct,
    AddMonoidAlgebra.coe_algebraMap, Function.comp_apply, Algebra.algebraMap_self,
    RingHom.id_apply, AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply,
    AddMonoidAlgebra.coeff_mul_single_zero, AddMonoidAlgebra.coeff_single,
    Finsupp.single_eq_same, projection, weight, Matrix.of_apply, universalMatrix] using ha

/-- The trivial-weight projection is unchanged by every affine torus action. -/
theorem projection_mul_affine {B : Type u} [CommRing B] [Algebra k B]
    (t : Lie.AffinePoints (splitTorus (Spec (CommRingCat.of k)) I) B) :
    (projection ρ I j).map (algebraMap k B) *
        (ρ.affineMatrix (CommAlgCat.of (CommRingCat.of k) B) (t ≫ j.hom.hom)).val =
      (projection ρ I j).map (algebraMap k B) := by
  classical
  have hM : (ρ.affineMatrix (CommAlgCat.of (CommRingCat.of k) B)
      (t ≫ j.hom.hom)).val =
      ∑ m ∈ weightSupport ρ I j,
        ((exponentValue I (algebraPointsEquiv I B t) (.ofAdd m) : Bˣ) : B) •
          (weight ρ I j m).map (algebraMap k B) := by
    ext a b
    rw [Matrix.sum_apply, affineMatrix_apply, Category.assoc,
      ← (algebraPointsEquiv I B).symm_apply_apply t, affinePointsEquiv_eval]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [Matrix.smul_apply, Matrix.map_apply, Algebra.smul_def, smul_eq_mul, mul_comm]
    simp only [MulEquiv.apply_symm_apply]
  by_cases h0 : (0 : I → ℤ) ∈ weightSupport ρ I j
  · rw [hM, Matrix.mul_sum, projection]
    simp_rw [Matrix.mul_smul, ← Matrix.map_mul, weight_mul_weight ρ I j 0]
    rw [Finset.sum_eq_single 0]
    · simp only [ite_true, ofAdd_zero, map_one, Units.val_one, one_smul]
    · intro m _ hm
      rw [ite_eq_right (Ne.symm hm), Matrix.map_zero _ (map_zero _), smul_zero]
    · exact fun h => (h h0).elim
  · rw [projection, weight_eq_zero ρ I j h0]
    simp

/-- The affine identity transports to the torus points of every test scheme. -/
theorem projection_mul_points
    (T : Over (Spec (CommRingCat.of k)))
    (t : T ⟶ (splitTorus (Spec (CommRingCat.of k)) I).X) :
    (projection ρ I j).map (scalarMap T) *
        ((ρ.restrict j).pointMatrix T t : Matrix (Fin N) (Fin N) Γ(T.left, ⊤)) =
      (projection ρ I j).map (scalarMap T) := by
  have : IsAffineHom (splitTorus (Spec (CommRingCat.of k)) I).X.hom :=
    isAffineHom_splitTorus _ I
  have : IsAffine (splitTorus (Spec (CommRingCat.of k)) I).X.left :=
    isAffine_of_isAffineHom (splitTorus (Spec (CommRingCat.of k)) I).X.hom
  obtain ⟨⟨B⟩, ⟨ψ⟩⟩ :=
    (essImage_algSpec (G := (splitTorus (Spec (CommRingCat.of k)) I).X)).mpr inferInstance
  let f : B →+* Γ(T.left, ⊤) :=
    (t ≫ ψ.inv).left.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom
  have h := projection_mul_affine ρ I j ψ.hom
  have e₁ : ((ρ.restrict j).pointMatrix T t : Matrix (Fin N) (Fin N) Γ(T.left, ⊤)) =
      (ρ.affineMatrix B (ψ.hom ≫ j.hom.hom)).val.map f := by
    have ht : t ≫ j.hom.hom ≫ ρ.hom.hom =
        (t ≫ ψ.inv) ≫ (ψ.hom ≫ j.hom.hom ≫ ρ.hom.hom) := by simp
    rw [pointMatrix_restrict, pointMatrix_apply, Category.assoc, ht,
      GeneralLinear.pointsEquiv_naturality, GeneralLinear.pointsEquiv_eq_affinePointsEquiv]
    rfl
  have e₂ : (projection ρ I j).map (scalarMap T) =
      ((projection ρ I j).map (algebraMap k B)).map f := by
    change (projection ρ I j).map (scalars T) = _
    rw [← scalars_naturality (t ≫ ψ.inv), scalars_algSpec, Matrix.map_map]
    rfl
  rw [e₁, e₂, ← Matrix.map_mul, h]

/-- Centrality makes the projection commute with the full group action. -/
theorem projection_commute (hc : IsCentral j) [IsAffine G.X.left]
    (T : Over (Spec (CommRingCat.of k))) (g : T ⟶ G.X) :
    (projection ρ I j).map (scalarMap T) *
        (ρ.pointMatrix T g : Matrix (Fin N) (Fin N) Γ(T.left, ⊤)) =
      (ρ.pointMatrix T g : Matrix (Fin N) (Fin N) Γ(T.left, ⊤)) *
        (projection ρ I j).map (scalarMap T) :=
  weight_commute_points ρ I j hc T g 0

/-- Every polynomial pulled back by the projection is torus invariant. -/
theorem linearPullback_torus_invariant (F : MvPolynomial (Fin N) k) :
    (ρ.restrict j).IsInvariantPolynomial (linearPullback (projection ρ I j) F) := by
  intro T t x
  rw [eval₂_linearPullback, eval₂_linearPullback, Matrix.mulVec_mulVec,
    projection_mul_points]

/-- Pullback preserves invariance under every subgroup when the torus is central. -/
theorem linearPullback_restrict_invariant (hc : IsCentral j) [IsAffine G.X.left]
    {H : GroupScheme (Spec (CommRingCat.of k))} (q : H ⟶ G)
    {F : MvPolynomial (Fin N) k} (hF : (ρ.restrict q).IsInvariantPolynomial F) :
    (ρ.restrict q).IsInvariantPolynomial (linearPullback (projection ρ I j) F) := by
  apply hF.linearPullback
  intro T g
  rw [pointMatrix_restrict]
  exact projection_commute ρ I j hc T _

end CentralZeroWeight

end Langlands.GroupScheme.MatrixRepresentation
