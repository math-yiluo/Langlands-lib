import Langlands.GroupScheme.Rational.PathSimpleMatrices
import Mathlib.Data.Matrix.Basis

/-! # Root-coordinate matrices on the normalized path basis -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 200000

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped Matrix CategoryTheory.MonObj

namespace Langlands.GroupScheme.SplitPinning

open MatrixRepresentation MatrixRepresentation.AdditiveDividedPowers
open Langlands.LinearAlgebra.RootDatumPathWeights

variable {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] {p : SplitPinning G}
  {d : Type} [Fintype d] [DecidableEq d] {ρ : MatrixRepresentation G d}

namespace RootParametrization

variable {α : p.rootIndex} (z : p.RootParametrization α)

/-- Extending a rational root coordinate gives its ordinary affine scalar coordinate. -/
theorem affinePoint_eq_constantPoint_rationalPoint
    (A : CommAlgCat.{u} k) (c : k) :
    VectorGroup.affinePoint (R := CommRingCat.of k) (d := 1) A
        (fun _ => algebraMap k A c) ≫ z.hom.hom.hom =
      G.constantPoint (z.rationalPoint c) ((algSpec (CommRingCat.of k)).obj (op A)) := by
  let T := (algSpec (CommRingCat.of k)).obj (op A)
  have hc : T.hom.appTop ((Scheme.ΓSpecIso (CommRingCat.of k)).inv c) =
      (Scheme.ΓSpecIso (CommRingCat.of A)).inv (algebraMap k A c) := by
    exact (ConcreteCategory.congr_hom
      (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap k A))) c).symm
  rw [VectorGroup.affinePoint_eq_scalarPoint]
  change z.point T _ = _
  rw [← hc, ← z.toUnit_comp_rationalPoint]
  rfl

/-- With vanishing higher divided powers, the rational root matrix has its exact coordinate. -/
theorem rationalMatrix_eq_one_add (ρ : MatrixRepresentation G d)
    (h : ∀ m, 2 ≤ m → dividedPower (ρ.restrict z.hom) m = 0) (c : k) :
    (ρ.rationalMatrix (z.rationalPoint c) : Matrix d d k) =
      1 + c • coefficientMatrix (ρ.restrict z.hom) 1 := by
  have hlin := affineMatrix_eq_one_add (ρ.restrict z.hom) h (CommAlgCat.of k k) c
  rw [affineMatrix_restrict,
    show (fun _ : Fin 1 => c) = (fun _ : Fin 1 => algebraMap k k c) from rfl,
    z.affinePoint_eq_constantPoint_rationalPoint, ρ.affineMatrix_constantPoint] at hlin
  simpa using hlin

end RootParametrization

variable {L : ℕ} {β : Fin L → p.base.support} {lam : characterLattice p.torus}
  (hρ : p.IsHighestWeight ρ lam) (hβ : IsPathComponent β)
  (hlam : IsPathFundamental β lam) (x : p.NormalizedSimpleRootParametrizations)
  (v₀ : p.representationWeightSpace ρ (pathWeight β lam 0)) (hv₀ : v₀ ≠ 0)

/-- The elementary upper root matrix on two consecutive path lines. -/
def pathRootMatrix (i : Fin L) (c : k) : Matrix (Fin (L + 1)) (Fin (L + 1)) k :=
  1 + Matrix.single i.castSucc i.succ c

/-- The normalized simple root point adds its coordinate times the preceding vector. -/
theorem rationalRoot_normalizedPathVector_succ (i : Fin L) (c : k) :
    (ρ.rationalMatrix ((x (β i)).toRootParametrization.rationalPoint c) : Matrix d d k) *ᵥ
        (normalizedPathVector hρ hβ hlam x v₀ i.succ : d → k) =
      (normalizedPathVector hρ hβ hlam x v₀ i.succ : d → k) +
        c • (normalizedPathVector hρ hβ hlam x v₀ i.castSucc : d → k) := by
  have hx := NormalizedRootParametrization.isTorusEquivariant_path (lam := lam) i.2 (x (β i))
  have hhi : ∀ m, 2 ≤ m → dividedPower (ρ.restrict (x (β i)).hom) m = 0 :=
    fun m hm => pathRootMap_dividedPower_eq_zero hρ hβ hlam
      (by omega : (i : ℕ) < i + 1) (by omega) hx hm
  rw [(x (β i)).toRootParametrization.rationalMatrix_eq_one_add ρ hhi c,
    one_add_smul_mulVec]
  change _ + c • dividedPower (ρ.restrict (x (β i)).hom) 1
    (normalizedPathVector hρ hβ hlam x v₀ (i + 1) : d → k) = _
  rw [dividedPower_normalizedPathVector_succ hρ hβ hlam x v₀ i.2]
  rfl

/-- A normalized simple root point fixes every other normalized path vector. -/
theorem rationalRoot_normalizedPathVector_other (i : Fin L) (c : k) (j : Fin (L + 1))
    (hj : j ≠ i.succ) :
    (ρ.rationalMatrix ((x (β i)).toRootParametrization.rationalPoint c) : Matrix d d k) *ᵥ
        (normalizedPathVector hρ hβ hlam x v₀ j : d → k) =
      (normalizedPathVector hρ hβ hlam x v₀ j : d → k) := by
  have hx := NormalizedRootParametrization.isTorusEquivariant_path (lam := lam) i.2 (x (β i))
  have hhi : ∀ m, 2 ≤ m → dividedPower (ρ.restrict (x (β i)).hom) m = 0 :=
    fun m hm => pathRootMap_dividedPower_eq_zero hρ hβ hlam
      (by omega : (i : ℕ) < i + 1) (by omega) hx hm
  have hz := pathRootMap_dividedPower_one_eq_zero hρ hβ hlam
    (by omega : (i : ℕ) < i + 1) (by omega) hx
    (j := j.val) (by omega) (fun h => hj (Fin.ext h))
    (normalizedPathVector hρ hβ hlam x v₀ j).2
  rw [(x (β i)).toRootParametrization.rationalMatrix_eq_one_add ρ hhi c,
    one_add_smul_mulVec]
  change _ + c • dividedPower (ρ.restrict (x (β i)).hom) 1
    (normalizedPathVector hρ hβ hlam x v₀ j : d → k) = _
  rw [hz, smul_zero, add_zero]

/-- The changed column of a rational simple root point in normalized coordinates. -/
theorem normalizedPathMatrix_rationalRoot_succ (i : Fin L) (c : k) (a : Fin (L + 1)) :
    normalizedPathMatrix hρ hβ hlam x v₀ hv₀
        ((x (β i)).toRootParametrization.rationalPoint c) a i.succ =
      (if i.succ = a then 1 else 0) + c * (if i.castSucc = a then 1 else 0) := by
  let B := normalizedPathBasis hρ hβ hlam x v₀ hv₀
  have hm := normalizedPathMatrix_apply hρ hβ hlam x v₀ hv₀
    ((x (β i)).toRootParametrization.rationalPoint c) a i.succ
  have ha := rationalRoot_normalizedPathVector_succ hρ hβ hlam x v₀ i c
  have hc := congrArg (fun z : d → k => B.repr z a) ha
  have he : B.repr
      ((normalizedPathVector hρ hβ hlam x v₀ i.succ : d → k) +
        c • (normalizedPathVector hρ hβ hlam x v₀ i.castSucc : d → k)) a =
      (if i.succ = a then 1 else 0) + c * (if i.castSucc = a then 1 else 0) := by
    rw [← normalizedPathBasis_apply hρ hβ hlam x v₀ hv₀ i.succ,
      ← normalizedPathBasis_apply hρ hβ hlam x v₀ hv₀ i.castSucc]
    change B.repr (B i.succ + c • B i.castSucc) a = _
    simp only [map_add, Finsupp.add_apply, map_smul, Finsupp.smul_apply,
      Module.Basis.repr_self_apply, smul_eq_mul]
  exact hm.trans (hc.trans he)

/-- All other columns of a rational simple root point are identity columns. -/
theorem normalizedPathMatrix_rationalRoot_other (i : Fin L) (c : k)
    (a b : Fin (L + 1)) (hb : b ≠ i.succ) :
    normalizedPathMatrix hρ hβ hlam x v₀ hv₀
        ((x (β i)).toRootParametrization.rationalPoint c) a b =
      (if b = a then 1 else 0) := by
  let B := normalizedPathBasis hρ hβ hlam x v₀ hv₀
  have hm := normalizedPathMatrix_apply hρ hβ hlam x v₀ hv₀
    ((x (β i)).toRootParametrization.rationalPoint c) a b
  have ha := rationalRoot_normalizedPathVector_other hρ hβ hlam x v₀ i c b hb
  have hc := congrArg (fun z : d → k => B.repr z a) ha
  have hB := congrArg (fun z : d → k => B.repr z a)
    (normalizedPathBasis_apply hρ hβ hlam x v₀ hv₀ b).symm
  exact hm.trans (hc.trans (hB.trans (B.repr_self_apply b a)))

/-- A rational simple root point is the elementary root matrix with its exact coordinate. -/
theorem normalizedPathMatrix_rationalRoot (i : Fin L) (c : k) :
    normalizedPathMatrix hρ hβ hlam x v₀ hv₀
        ((x (β i)).toRootParametrization.rationalPoint c) = pathRootMatrix i c := by
  apply Matrix.ext
  intro a b
  by_cases hb : b = i.succ
  · subst b
    have h := normalizedPathMatrix_rationalRoot_succ hρ hβ hlam x v₀ hv₀ i c a
    simpa [pathRootMatrix, Matrix.single_apply, Matrix.one_apply, eq_comm, mul_ite] using h
  · have h := normalizedPathMatrix_rationalRoot_other hρ hβ hlam x v₀ hv₀ i c a b hb
    simpa [pathRootMatrix, Matrix.single_apply, Matrix.one_apply, hb, eq_comm] using h

/-- The matrix of a simple root factor followed by its canonical reflection. -/
def pathSimpleFactorMatrix (i : Fin L) (c : k) :
    Matrix (Fin (L + 1)) (Fin (L + 1)) k :=
  pathReflectionMatrix i - Matrix.single i.castSucc i.castSucc c

/-- Multiplying the elementary root matrix and the reflection changes one diagonal entry. -/
theorem pathRootMatrix_mul_pathReflectionMatrix (i : Fin L) (c : k) :
    pathRootMatrix i c * pathReflectionMatrix i = pathSimpleFactorMatrix i c := by
  have hne : i.castSucc ≠ i.succ := by
    intro h
    have hv := congrArg Fin.val h
    simp only [Fin.val_castSucc, Fin.val_succ] at hv
    omega
  have hs : Matrix.single i.castSucc i.succ c * pathReflectionMatrix i =
      -Matrix.single i.castSucc i.castSucc c := by
    apply Matrix.ext
    intro a b
    by_cases ha : a = i.castSucc
    · subst a
      rw [Matrix.single_mul_apply_same, Matrix.neg_apply]
      by_cases hb : b = i.castSucc
      · subst b
        simp [pathReflectionMatrix]
      · by_cases hb' : b = i.succ
        · subst b
          simp [pathReflectionMatrix, hne, eq_comm]
        · simp [pathReflectionMatrix, hb, hb', eq_comm]
    · simp only [Matrix.single_mul_apply_of_ne c _ _ _ _ ha, Matrix.neg_apply,
        Matrix.single_apply_of_row_ne (Ne.symm ha), neg_zero]
  simp only [pathRootMatrix, pathSimpleFactorMatrix, Matrix.add_mul, Matrix.one_mul, hs,
    sub_eq_add_neg]

/-- The actual simple factor has the signed-transposition matrix with diagonal coordinate. -/
theorem normalizedPathMatrix_simpleFactor (i : Fin L) (c : k) :
    normalizedPathMatrix hρ hβ hlam x v₀ hv₀
        ((x (β i)).toRootParametrization.rationalPoint c *
          (x (β i)).reflectionRepresentative.point) = pathSimpleFactorMatrix i c := by
  rw [map_mul, normalizedPathMatrix_rationalRoot hρ hβ hlam x v₀ hv₀,
    normalizedPathMatrix_canonicalReflection hρ hβ hlam x v₀ hv₀,
    pathRootMatrix_mul_pathReflectionMatrix]

end Langlands.GroupScheme.SplitPinning
