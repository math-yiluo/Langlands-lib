import Langlands.GroupScheme.Rational.RootActionWeights
import Langlands.GroupScheme.Reductive.RankOneSteinbergOperators
import Langlands.GroupScheme.Reductive.SplitRankOneRootCellUniversal
import Mathlib.Algebra.Polynomial.Roots

/-! # Binomial pairings of actual rank-one root coefficients -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj Matrix Polynomial

namespace Langlands.GroupScheme.MatrixRepresentation.RankOneRootCoefficient

variable {k : Type u} [Field k] {n : Type} [Fintype n] [DecidableEq n]

/-- A linear functional on a coordinate vector is its finite basis expansion. -/
theorem dual_apply_eq_sum (ℓ : Module.Dual k (n → k)) (v : n → k) :
    ℓ v = ∑ i, ℓ (Pi.single i 1) * v i := by
  have hv : v = ∑ i, v i • Pi.single i (1 : k) := by
    ext j
    simp [Pi.single_apply]
  conv_lhs => rw [hv, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_smul, smul_eq_mul, mul_comm]

/-- Scalar matrix coefficient of a polynomial matrix at an original vector. -/
def coefficientPolynomial (M : Matrix n n k[X]) (ℓ : Module.Dual k (n → k))
    (v : n → k) : k[X] :=
  ∑ i, ∑ j, Polynomial.C (ℓ (Pi.single i 1) * v j) * M i j

theorem coefficientPolynomial_eval (M : Matrix n n k[X])
    (ℓ : Module.Dual k (n → k)) (v : n → k) (t : k) :
    (coefficientPolynomial M ℓ v).eval t =
      ℓ (M.map (Polynomial.eval t) *ᵥ v) := by
  rw [dual_apply_eq_sum]
  simp only [coefficientPolynomial, Polynomial.eval_finsetSum, Polynomial.eval_mul,
    Polynomial.eval_C, Matrix.mulVec, dotProduct, Matrix.map_apply, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem coefficientPolynomial_coeff (M : Matrix n n k[X])
    (ℓ : Module.Dual k (n → k)) (v : n → k) (a : ℕ) :
    (coefficientPolynomial M ℓ v).coeff a =
      ℓ ((fun i j => (M i j).coeff a) *ᵥ v) := by
  rw [dual_apply_eq_sum]
  simp only [coefficientPolynomial, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul,
    Matrix.mulVec, dotProduct, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Equality on the complement of the rank-one cell divisor determines the
entire polynomial, by clearing that nonzero linear factor. -/
theorem polynomial_eq_of_cell_eval [Infinite k] (P Q : k[X]) (t : k)
    (h : ∀ s : k, 1 + s * t ≠ 0 → P.eval s = Q.eval s) :
    P = Q := by
  let L : k[X] := 1 + Polynomial.X * Polynomial.C t
  have hL : L ≠ 0 := by
    intro hz
    have he := congrArg (fun P : k[X] => P.coeff 0) hz
    simp [L] at he
  apply mul_left_cancel₀ hL
  apply Polynomial.funext
  intro s
  simp only [Polynomial.eval_mul]
  by_cases hs : 1 + s * t = 0
  · have hLs : L.eval s = 0 := by
      simpa only [L, Polynomial.eval_add, Polynomial.eval_one,
        Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_C] using hs
    simp only [hLs, zero_mul]
  · rw [h s hs]

open AdditiveDividedPowers

variable (E F : MatrixRepresentation (VectorGroup.groupScheme (CommRingCat.of k) 1) n)
    (ℓ : Module.Dual k (n → k)) (v : n → k) (m : ℕ)

theorem coefficientPolynomial_univariate_coeff (a : ℕ) :
    (coefficientPolynomial (univariateMatrix E) ℓ v).coeff a =
      ℓ (dividedPower E a v) := by
  rw [coefficientPolynomial_coeff, dividedPower_eq_toLin]
  rfl

set_option maxHeartbeats 600000 in
/-- The scalar rank-one cell identity fixes every pairing of the two actual
divided-power coefficient families, including its off-diagonal terms. -/
theorem dividedPower_pairing_of_cell_identity [Infinite k]
    (hcell : ∀ s t : k, 1 + s * t ≠ 0 →
      ℓ ((univariateMatrix E).map (Polynomial.eval s) *ᵥ
        ((univariateMatrix F).map (Polynomial.eval t) *ᵥ v)) = (1 + s * t) ^ m)
    (a b : ℕ) :
    ℓ (dividedPower E a (dividedPower F b v)) =
      if b = a then (m.choose a : k) else 0 := by
  have hfirst (t : k) :
      coefficientPolynomial (univariateMatrix E) ℓ
          ((univariateMatrix F).map (Polynomial.eval t) *ᵥ v) =
        (1 + Polynomial.C t * Polynomial.X) ^ m := by
    apply polynomial_eq_of_cell_eval _ _ t
    intro s hs
    rw [coefficientPolynomial_eval, hcell s t hs]
    simp only [Polynomial.eval_pow, Polynomial.eval_add, Polynomial.eval_one,
      Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X, mul_comm t s]
  have hcoeff (t : k) :
      ℓ (dividedPower E a
        ((univariateMatrix F).map (Polynomial.eval t) *ᵥ v)) =
          (m.choose a : k) * t ^ a := by
    have he := congrArg (fun P : k[X] => P.coeff a) (hfirst t)
    rw [coefficientPolynomial_univariate_coeff] at he
    rw [he]
    have hb := AdditiveDividedPowers.coeff_aeval_C_mul_X
      (P := (1 + Polynomial.X : k[X]) ^ m) t a
    simpa only [map_pow, map_add, map_one, Polynomial.aeval_X,
      Polynomial.coeff_one_add_X_pow, Algebra.algebraMap_self, RingHom.id_apply] using hb
  let ℓa : Module.Dual k (n → k) := ℓ.comp (dividedPower E a)
  have hsecond : coefficientPolynomial (univariateMatrix F) ℓa v =
      Polynomial.C (m.choose a : k) * Polynomial.X ^ a := by
    apply Polynomial.funext
    intro t
    rw [coefficientPolynomial_eval]
    change ℓ (dividedPower E a
      ((univariateMatrix F).map (Polynomial.eval t) *ᵥ v)) = _
    rw [hcoeff]
    simp
  have he := congrArg (fun P : k[X] => P.coeff b) hsecond
  rw [coefficientPolynomial_univariate_coeff, Polynomial.coeff_C_mul,
    Polynomial.coeff_X_pow] at he
  change ℓ (dividedPower E a (dividedPower F b v)) = _ at he
  simpa only [mul_ite, mul_one, mul_zero] using he

/-- Nonvanishing of a binomial coefficient forces the actual lowering
coefficient to act nontrivially on the original vector. -/
theorem dividedPower_ne_zero_of_cell_identity [Infinite k]
    (hcell : ∀ s t : k, 1 + s * t ≠ 0 →
      ℓ ((univariateMatrix E).map (Polynomial.eval s) *ᵥ
        ((univariateMatrix F).map (Polynomial.eval t) *ᵥ v)) = (1 + s * t) ^ m)
    (a : ℕ) (ha : (m.choose a : k) ≠ 0) :
    dividedPower F a v ≠ 0 := by
  intro hz
  have he := dividedPower_pairing_of_cell_identity E F ℓ v m hcell a a
  rw [hz, map_zero, map_zero, ite_eq_left rfl] at he
  exact ha he.symm

/-- Every retained coefficient of the actual lowering root action is nonzero
at a Steinberg exponent, once the scalar rank-one cell identity is established. -/
theorem steinberg_dividedPower_ne_zero_of_cell_identity [Infinite k]
    (p : ℕ) [Fact p.Prime] [CharP k p] (r : ℕ)
    (hcell : ∀ s t : k, 1 + s * t ≠ 0 →
      ℓ ((univariateMatrix E).map (Polynomial.eval s) *ᵥ
        ((univariateMatrix F).map (Polynomial.eval t) *ᵥ v)) =
          (1 + s * t) ^ (p ^ r - 1))
    (a : ℕ) (ha : a ≤ p ^ r - 1) :
    dividedPower F a v ≠ 0 :=
  dividedPower_ne_zero_of_cell_identity E F ℓ v (p ^ r - 1) hcell a
    (RankOneSteinberg.choose_steinberg_cast_ne_zero p r a ha)

section ActualRootCell

variable {G : GroupScheme (Spec (CommRingCat.of k))}
    {T : CommGroupScheme (Spec (CommRingCat.of k))}
    (ρ : MatrixRepresentation G n) (i : T.toGrp ⟶ G)
    (ν : cocharacterLattice T) (xp xm : RootCell.Ga k ⟶ G)

/-- The root-cell coordinate of an affine additive point is its affine parameter
transported to global sections. -/
theorem crd_affinePoint (A : CommAlgCat.{u} k) (s : A) :
    RootCell.crd (VectorGroup.affinePoint (R := CommRingCat.of k) (d := 1) A
      (fun _ => s)) = (Scheme.ΓSpecIso (CommRingCat.of A)).inv s := by
  rw [VectorGroup.affinePoint_eq_scalarPoint]
  exact RootCell.crd_pt _

set_option maxHeartbeats 600000 in
/-- The actual root-cell relation gives the matrix factorization over every
commutative test algebra, including nonreduced algebras. -/
theorem affineMatrix_cell_relation
    (hcell : ∀ Z : Over (Spec (CommRingCat.of k)), RootCell.RelationOver i ν xp xm Z)
    (A : CommAlgCat.{u} k) (s t : A) (u : Aˣ) (hu : (u : A) = 1 + s * t) :
    (ρ.restrict xp).affineMatrix A
        (VectorGroup.affinePoint (R := CommRingCat.of k) (d := 1) A (fun _ => s)) *
      (ρ.restrict xm).affineMatrix A
        (VectorGroup.affinePoint (R := CommRingCat.of k) (d := 1) A (fun _ => t)) =
      (ρ.restrict xm).affineMatrix A
        (VectorGroup.affinePoint (R := CommRingCat.of k) (d := 1) A
          (fun _ => (↑u⁻¹ : A) * t)) *
      ρ.affineMatrix A
        ((Gm.affinePointsEquiv ((algSpec (CommRingCat.of k)).obj (op A)).hom).symm u ≫
          (CommGroupScheme.groupHom ν).hom.hom ≫ i.hom.hom) *
      (ρ.restrict xp).affineMatrix A
        (VectorGroup.affinePoint (R := CommRingCat.of k) (d := 1) A
          (fun _ => (↑u⁻¹ : A) * s)) := by
  let Z := (algSpec (CommRingCat.of k)).obj (op A)
  let φ := (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom
  let ua : Γ(Z.left, ⊤)ˣ := Units.map φ.toMonoidHom u
  let a (c : A) := VectorGroup.affinePoint (R := CommRingCat.of k) (d := 1) A
    (fun _ => c)
  have hcrd (c : A) : RootCell.crd (a c) = φ c := crd_affinePoint A c
  have hu' : (ua : Γ(Z.left, ⊤)) = 1 + RootCell.crd (a s) * RootCell.crd (a t) := by
    change φ (u : A) = _
    rw [hu, map_add, map_one, map_mul, hcrd, hcrd]
  have hs' : RootCell.crd (a ((↑u⁻¹ : A) * s)) =
      (↑ua⁻¹ : Γ(Z.left, ⊤)) * RootCell.crd (a s) := by
    rw [hcrd, hcrd, map_mul]
    rfl
  have ht' : RootCell.crd (a ((↑u⁻¹ : A) * t)) =
      (↑ua⁻¹ : Γ(Z.left, ⊤)) * RootCell.crd (a t) := by
    rw [hcrd, hcrd, map_mul]
    rfl
  have hunit : (Gm.pointsEquiv _ Z).symm ua =
      (Gm.affinePointsEquiv Z.hom).symm u := rfl
  have h := hcell Z (a s) (a t) (a ((↑u⁻¹ : A) * s))
    (a ((↑u⁻¹ : A) * t)) ua hu' hs' ht'
  have hm := congrArg (ρ.affineMatrix A) h
  simp only [map_mul, hunit] at hm
  rw [MatrixRepresentation.affineMatrix_restrict,
    MatrixRepresentation.affineMatrix_restrict,
    MatrixRepresentation.affineMatrix_restrict,
    MatrixRepresentation.affineMatrix_restrict]
  exact hm

set_option maxHeartbeats 600000 in
/-- A raising-fixed vector, a lowering-fixed functional and their actual
coroot weight imply the scalar cell identity. -/
theorem scalar_cell_identity
    (hcell : ∀ Z : Over (Spec (CommRingCat.of k)), RootCell.RelationOver i ν xp xm Z)
    (hxp : ∀ s : k, (ρ.restrict xp).affineAction (CommAlgCat.of k k)
      (VectorGroup.affinePoint (R := CommRingCat.of k) (d := 1)
        (CommAlgCat.of k k) (fun _ => s)) v = v)
    (hxm : ∀ (t : k) (w : n → k),
      ℓ ((ρ.restrict xm).affineAction (CommAlgCat.of k k)
        (VectorGroup.affinePoint (R := CommRingCat.of k) (d := 1)
          (CommAlgCat.of k k) (fun _ => t)) w) = ℓ w)
    (hν : ∀ u : kˣ, ρ.affineAction (CommAlgCat.of k k)
      ((Gm.affinePointsEquiv
          ((algSpec (CommRingCat.of k)).obj (op (CommAlgCat.of k k))).hom).symm u ≫
        (CommGroupScheme.groupHom ν).hom.hom ≫ i.hom.hom) v = (u : k) ^ m • v)
    (hnorm : ℓ v = 1) (s t : k) (hst : 1 + s * t ≠ 0) :
    ℓ ((univariateMatrix (ρ.restrict xp)).map (Polynomial.eval s) *ᵥ
      ((univariateMatrix (ρ.restrict xm)).map (Polynomial.eval t) *ᵥ v)) =
      (1 + s * t) ^ m := by
  let A := CommAlgCat.of k k
  let a (c : k) := VectorGroup.affinePoint (R := CommRingCat.of k) (d := 1) A
    (fun _ => c)
  let u : kˣ := Units.mk0 (1 + s * t) hst
  have hE (c : k) :
      (univariateMatrix (ρ.restrict xp)).map (Polynomial.eval c) =
        ((ρ.restrict xp).affineMatrix A (a c) : Matrix n n k) := by
    have he := univariateMatrix_aeval (ρ.restrict xp) (CommAlgCat.of k k) c
    change (univariateMatrix (ρ.restrict xp)).map
      (Polynomial.aeval (R := k) (A := k) c : k[X] → k) =
        ((ρ.restrict xp).affineMatrix A (a c) : Matrix n n k) at he
    rw [Polynomial.coe_aeval_eq_eval] at he
    exact he
  have hF (c : k) :
      (univariateMatrix (ρ.restrict xm)).map (Polynomial.eval c) =
        ((ρ.restrict xm).affineMatrix A (a c) : Matrix n n k) := by
    have he := univariateMatrix_aeval (ρ.restrict xm) (CommAlgCat.of k k) c
    change (univariateMatrix (ρ.restrict xm)).map
      (Polynomial.aeval (R := k) (A := k) c : k[X] → k) =
        ((ρ.restrict xm).affineMatrix A (a c) : Matrix n n k) at he
    rw [Polynomial.coe_aeval_eq_eval] at he
    exact he
  have hm := congrArg Units.val (affineMatrix_cell_relation ρ i ν xp xm hcell A s t u rfl)
  have ha := congrArg (fun M : Matrix n n k => M *ᵥ v) hm
  simp only [Units.val_mul, ← Matrix.mulVec_mulVec] at ha
  change (ρ.restrict xp).affineAction A (a s)
      ((ρ.restrict xm).affineAction A (a t) v) =
    (ρ.restrict xm).affineAction A (a ((↑u⁻¹ : k) * t))
      (ρ.affineAction A
        ((Gm.affinePointsEquiv
            ((algSpec (CommRingCat.of k)).obj (op A)).hom).symm u ≫
          (CommGroupScheme.groupHom ν).hom.hom ≫ i.hom.hom)
        ((ρ.restrict xp).affineAction A (a ((↑u⁻¹ : k) * s)) v)) at ha
  rw [hxp, hν] at ha
  rw [hE, hF]
  change ℓ ((ρ.restrict xp).affineAction A (a s)
    ((ρ.restrict xm).affineAction A (a t) v)) = _
  rw [ha, hxm, map_smul, hnorm, smul_eq_mul, mul_one]
  rfl

section FixedData

variable
    (hcell : ∀ Z : Over (Spec (CommRingCat.of k)), RootCell.RelationOver i ν xp xm Z)
    (hxp : ∀ s : k, (ρ.restrict xp).affineAction (CommAlgCat.of k k)
      (VectorGroup.affinePoint (R := CommRingCat.of k) (d := 1)
        (CommAlgCat.of k k) (fun _ => s)) v = v)
    (hxm : ∀ (t : k) (w : n → k),
      ℓ ((ρ.restrict xm).affineAction (CommAlgCat.of k k)
        (VectorGroup.affinePoint (R := CommRingCat.of k) (d := 1)
          (CommAlgCat.of k k) (fun _ => t)) w) = ℓ w)
    (hν : ∀ u : kˣ, ρ.affineAction (CommAlgCat.of k k)
      ((Gm.affinePointsEquiv
          ((algSpec (CommRingCat.of k)).obj (op (CommAlgCat.of k k))).hom).symm u ≫
        (CommGroupScheme.groupHom ν).hom.hom ≫ i.hom.hom) v = (u : k) ^ m • v)
    (hnorm : ℓ v = 1)

include hcell hxp hxm hν hnorm

/-- The actual root-cell relation and fixed-vector data determine all binomial
pairings of the original raising and lowering coefficients. -/
theorem dividedPower_pairing [Infinite k] (a b : ℕ) :
    ℓ (dividedPower (ρ.restrict xp) a (dividedPower (ρ.restrict xm) b v)) =
      if b = a then (m.choose a : k) else 0 := by
  apply dividedPower_pairing_of_cell_identity
  exact scalar_cell_identity ℓ v m ρ i ν xp xm hcell hxp hxm hν hnorm

/-- A nonzero binomial coefficient forces nonzero lowering action using the
actual root-cell relation and the original fixed-vector data. -/
theorem dividedPower_ne_zero [Infinite k] (a : ℕ) (ha : (m.choose a : k) ≠ 0) :
    dividedPower (ρ.restrict xm) a v ≠ 0 := by
  apply dividedPower_ne_zero_of_cell_identity (ρ.restrict xp) (ρ.restrict xm) ℓ v m
    (scalar_cell_identity ℓ v m ρ i ν xp xm hcell hxp hxm hν hnorm) a ha

end FixedData

end ActualRootCell

end Langlands.GroupScheme.MatrixRepresentation.RankOneRootCoefficient
