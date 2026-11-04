import Langlands.GroupScheme.Lie.SemisimpleElement
import Langlands.GroupScheme.Rational.CharacterRestrictionFiniteIndex
import Mathlib.FieldTheory.Separable

/-! # Representation semisimplicity of split-torus tangent vectors -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Polynomial
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.Lie

variable {k : Type u} [Field k]

private theorem isSemisimple_of_idempotent
    {V : Type*} [AddCommGroup V] [Module k V]
    (f : Module.End k V) (hf : f * f = f) : f.IsSemisimple := by
  have hp : (X * (X - C (1 : k))).Separable := by
    have hc : IsCoprime (X - C (0 : k)) (X - C (1 : k)) :=
      isCoprime_X_sub_C_of_isUnit_sub (by simp)
    simpa using separable_X.mul (separable_X_sub_C (x := (1 : k))) (by simpa using hc)
  apply Module.End.isSemisimple_of_squarefree_aeval_eq_zero hp.squarefree
  simp only [map_mul, map_sub, aeval_X, map_one]
  rw [mul_sub, mul_one, hf, sub_self]

/-- An idempotent matrix is geometrically semisimple over every field. -/
theorem isGeometricallySemisimpleMatrix_of_idempotent
    {n : Type} [Fintype n] [DecidableEq n]
    (P : Matrix n n k) (hP : P * P = P) : IsGeometricallySemisimpleMatrix P := by
  apply isSemisimple_of_idempotent
  change Matrix.toLinAlgEquiv' (P.map (algebraMap k (AlgebraicClosure k))) *
      Matrix.toLinAlgEquiv' (P.map (algebraMap k (AlgebraicClosure k))) = _
  rw [← map_mul, ← RingHom.mapMatrix_apply, ← map_mul, hP]
  rfl

/-- A finite sum of pairwise commuting geometrically semisimple matrices is
geometrically semisimple. -/
theorem isGeometricallySemisimpleMatrix_sum
    {n : Type} [Fintype n] [DecidableEq n]
    {J : Type*} (s : Finset J) (M : J → Matrix n n k)
    (hs : ∀ i ∈ s, IsGeometricallySemisimpleMatrix (M i))
    (hc : ∀ i ∈ s, ∀ j ∈ s, Commute (M i) (M j)) :
    IsGeometricallySemisimpleMatrix (∑ i ∈ s, M i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using
      (isGeometricallySemisimpleMatrix_zero (k := k) (n := n))
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha]
    have hsa := hs a (Finset.mem_insert_self a s)
    have hss := ih (fun i hi => hs i (Finset.mem_insert_of_mem hi))
      (fun i hi j hj => hc i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj))
    have hcomm : Commute (M a) (∑ i ∈ s, M i) :=
      Commute.sum_right s M _ fun i hi =>
        hc a (Finset.mem_insert_self a s) i (Finset.mem_insert_of_mem hi)
    unfold IsGeometricallySemisimpleMatrix at hsa hss ⊢
    rw [Matrix.map_add _ (map_add _), map_add]
    exact hsa.add_of_commute
      ((hcomm.map (algebraMap k (AlgebraicClosure k)).mapMatrix).map
        Matrix.toLinAlgEquiv'.toRingHom) hss

open splitTorus CharacterRestrictionFiniteIndex

variable {G : GroupScheme (Spec (CommRingCat.of k))} {N : ℕ}

/-- Extracting epsilon coefficients in the actual weight-evaluation formula
expresses a torus tangent matrix as a linear combination of its weight projectors. -/
theorem tangentMatrix_splitTorus_weight_sum
    (ρ : MatrixRepresentation G (Fin N)) (I : Type u) [Fintype I] [DecidableEq I]
    (j : splitTorus (Spec (CommRingCat.of k)) I ⟶ G)
    (X : lieKernel (splitTorus (Spec (CommRingCat.of k)) I) k) :
    ρ.tangentMatrix k (targetMap j k X) =
      ∑ m ∈ weightSupport ρ I j,
        (exponentValue I (algebraPointsEquiv I (DualNumber k) X.val)
          (Multiplicative.ofAdd m) : DualNumber k).snd • weight ρ I j m := by
  ext a b
  change (GeneralLinear.affinePointsEquiv (Fin N) (CommRingCat.of k)
    (CommAlgCat.of (CommRingCat.of k) (DualNumber k))
      (X.val ≫ j.hom.hom ≫ ρ.hom.hom) a b).snd = _
  have h := affinePointsEquiv_eval ρ I j
    (algebraPointsEquiv I (DualNumber k) X.val) a b
  rw [MulEquiv.symm_apply_apply] at h
  rw [h, TrivSqZeroExt.snd_sum, Matrix.sum_apply]
  exact Finset.sum_congr rfl fun m _ => by
    simp only [TrivSqZeroExt.snd_smul, Matrix.smul_apply, smul_eq_mul, mul_comm]

/-- Every linear combination of the actual torus weight projectors is
geometrically semisimple. -/
theorem isGeometricallySemisimpleMatrix_sum_weight
    (ρ : MatrixRepresentation G (Fin N)) (I : Type u) [Fintype I] [DecidableEq I]
    (j : splitTorus (Spec (CommRingCat.of k)) I ⟶ G) (c : (I → ℤ) → k) :
    IsGeometricallySemisimpleMatrix
      (∑ m ∈ weightSupport ρ I j, c m • weight ρ I j m) := by
  apply isGeometricallySemisimpleMatrix_sum
  · intro m _
    exact (isGeometricallySemisimpleMatrix_of_idempotent (weight ρ I j m)
      (by simpa using weight_mul_weight ρ I j m m)).smul (c m)
  · intro m _ n _
    have h : Commute (weight ρ I j m) (weight ρ I j n) := by
      change weight ρ I j m * weight ρ I j n = weight ρ I j n * weight ρ I j m
      rw [weight_mul_weight, weight_mul_weight]
      by_cases hmn : m = n
      · subst n
        rfl
      · simp [hmn, Ne.symm hmn]
    exact (h.smul_left (c m)).smul_right (c n)

/-- The image of any standard split-torus tangent vector is semisimple in
every algebraic representation of the target group. -/
theorem isSemisimpleElement_targetMap_splitTorus
    (I : Type u) [Fintype I] [DecidableEq I]
    (j : splitTorus (Spec (CommRingCat.of k)) I ⟶ G)
    (X : lieKernel (splitTorus (Spec (CommRingCat.of k)) I) k) :
    IsSemisimpleElement G (targetMap j k X) := by
  intro N ρ
  rw [tangentMatrix_splitTorus_weight_sum]
  exact isGeometricallySemisimpleMatrix_sum_weight ρ I j _

/-- Every actual tangent vector of a split torus is representation-semisimple. -/
theorem isSemisimpleElement_of_isSplitTorus
    {T : GroupScheme (Spec (CommRingCat.of k))} (hT : IsSplitTorus T)
    (X : lieKernel T k) : IsSemisimpleElement T X := by
  classical
  obtain ⟨I, hI, ⟨e⟩⟩ := hT
  let : Fintype I := Fintype.ofFinite I
  have h := isSemisimpleElement_targetMap_splitTorus I e.inv (targetMap e.hom k X)
  convert h using 1
  apply Subtype.ext
  change X.val = (X.val ≫ e.hom.hom.hom) ≫ e.inv.hom.hom
  rw [Category.assoc]
  change X.val = X.val ≫ (e.hom ≫ e.inv).hom.hom
  rw [e.hom_inv_id]
  exact (Category.comp_id X.val).symm

/-- Universe-general split-torus tangent semisimplicity with no geometric
assumptions on a target group or its representations. -/
def SplitTorusSemisimpleStatement : Prop :=
  ∀ (k : Type u) [Field k] (T : GroupScheme (Spec (CommRingCat.of k))),
    IsSplitTorus T → ∀ X : lieKernel T k, IsSemisimpleElement T X

theorem splitTorusSemisimpleStatement : SplitTorusSemisimpleStatement.{u} := by
  intro k _ T hT X
  exact isSemisimpleElement_of_isSplitTorus hT X

end Langlands.GroupScheme.Lie
