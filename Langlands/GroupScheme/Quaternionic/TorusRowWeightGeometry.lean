import Langlands.GroupScheme.Quaternionic.TorusCocharacterWeightSpace
import Langlands.GroupScheme.Quaternionic.QuadraticTorusWittBound

/-! # Totally singular sums of nonopposite torus row weights -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct Matrix

set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.Quaternionic.FirstKindInvolution

open FiniteAlgebraUnits FiniteAlgebraTorusWeights FiniteMatrixAlgebraTorusWeights
  SplitTorusRepresentationWeights QuadraticTorusWittBound

variable {K D : Type u} [Field K] [DivisionRing D] [Algebra K D]
  [FiniteDimensional K D] (σ : FirstKindInvolution K D)
  {n : Type} [Fintype n] [DecidableEq n]
  {I : Type u} [Fintype I] [DecidableEq I]

/-- The sum of finitely many full-torus row weight spaces. -/
def torusRowWeightSum (q : σ.QuadraticForms n)
    (i : splitTorus (Spec (CommRingCat.of K)) I ⟶ σ.isometryGroup q)
    (S : Finset (I → ℤ)) : Submodule D (n → D) :=
  ⨆ m ∈ S, σ.torusRowWeightSpace q i m

/-- The division-algebra dimensions of a finite set of row weight spaces add. -/
theorem finrank_torusRowWeightSum (q : σ.QuadraticForms n)
    (i : splitTorus (Spec (CommRingCat.of K)) I ⟶ σ.isometryGroup q)
    (S : Finset (I → ℤ)) :
    Module.finrank D (σ.torusRowWeightSum q i S) =
      ∑ m ∈ S, Module.finrank D (σ.torusRowWeightSpace q i m) := by
  classical
  unfold torusRowWeightSum
  induction S using Finset.induction_on with
  | empty => simp
  | insert a S ha ih =>
    rw [Finset.sum_insert ha, ← ih, Finset.iSup_insert]
    have hdisj : Disjoint (σ.torusRowWeightSpace q i a)
        (⨆ m ∈ S, σ.torusRowWeightSpace q i m) := by
      exact (rowWeightSpace_iSupIndep (i ≫ σ.isometryGroupι q)).disjoint_biSup
        (y := (S : Set (I → ℤ))) (by simpa using ha)
    have h := Submodule.finrank_sup_add_finrank_inf_eq
      (σ.torusRowWeightSpace q i a) (⨆ m ∈ S, σ.torusRowWeightSpace q i m)
    rw [hdisj.eq_bot, finrank_bot, add_zero] at h
    exact h

/-- Every row in a finite sum of row weight spaces is fixed by the sum of the
corresponding universal weight idempotents. -/
theorem vecMul_sum_weightElement_of_mem_torusRowWeightSum
    (q : σ.QuadraticForms n)
    (i : splitTorus (Spec (CommRingCat.of K)) I ⟶ σ.isometryGroup q)
    (S : Finset (I → ℤ)) {x : n → D} (hx : x ∈ σ.torusRowWeightSum q i S) :
    x ᵥ* (∑ m ∈ S, weightElement (i ≫ σ.isometryGroupι q) m) = x := by
  classical
  let f := ∑ m ∈ S, weightElement (i ≫ σ.isometryGroupι q) m
  let F : Module.End D (n → D) := f.toLinearMapRight' - LinearMap.id
  have hle : σ.torusRowWeightSum q i S ≤ LinearMap.ker F := by
    refine iSup_le fun m => iSup_le fun hm => ?_
    intro v hv
    change v ᵥ* f - v = 0
    rw [sub_eq_zero]
    change v ᵥ* (∑ p ∈ S, weightElement (i ≫ σ.isometryGroupι q) p) = v
    rw [Matrix.vecMul_sum]
    have hp (p : I → ℤ) :
        v ᵥ* weightElement (i ≫ σ.isometryGroupι q) p =
          if m = p then v else 0 :=
      rowWeightProjection_of_mem (i ≫ σ.isometryGroupι q) p m hv
    simp only [hp, Finset.sum_ite_eq, ite_eq_left hm]
  exact sub_eq_zero.mp (hle hx)

/-- The sandwich by a sum of nonopposite universal weight idempotents belongs
to the quadratic kernel. -/
theorem sum_weightElement_sandwich_mem_quadraticKernel (q : σ.QuadraticForms n)
    (i : splitTorus (Spec (CommRingCat.of K)) I ⟶ σ.isometryGroup q)
    (S : Finset (I → ℤ))
    (hS : ∀ m ∈ S, ∀ p ∈ S, m + p ≠ 0) :
    (∑ m ∈ S, weightElement (i ≫ σ.isometryGroupι q) m) * Quotient.out q *
      σ.matrix n (∑ m ∈ S, weightElement (i ≫ σ.isometryGroupι q) m) ∈
        σ.quadraticKernel n := by
  classical
  set j := i ≫ σ.isometryGroupι q
  have hu : IsometryCut.defect (σ.matrix n) (Quotient.out q)
      ((universalUnit j : (AddMonoidAlgebra K (I → ℤ) ⊗[K] Matrix n n D)ˣ) :
        AddMonoidAlgebra K (I → ℤ) ⊗[K] Matrix n n D) ∈
      (σ.quadraticKernel n).baseChange (AddMonoidAlgebra K (I → ℤ)) := by
    have h := defect_affinePoint_mem σ q
      (CommAlgCat.of (CommRingCat.of K) (AddMonoidAlgebra K (I → ℤ)))
      (splitTorus.universalPoint (R := CommRingCat.of K) I ≫ i.hom.hom)
    rw [Category.assoc] at h
    exact h
  have hv := (IsometryCut.isometrySubgroup
    (IsometryCut.isStable_alternatingSubspace (τ := σ.matrix n)) (Quotient.out q)
    (AddMonoidAlgebra K (I → ℤ))).inv_mem (x := universalUnit j) hu
  rw [IsometryCut.mem_isometrySubgroup, universalUnit_inv_eq_sum] at hv
  have hc := coeffTensor_mem_of_mem_baseChange _ 0 hv
  rw [coeffTensor_zero_defect_sum] at hc
  let s := weightSupport (rightRegularRepresentation
    (Module.finBasis K (Matrix n n D))) I j
  let e : (I → ℤ) → Matrix n n D := weightElement j
  let f : Matrix n n D := ∑ p ∈ S, e p
  let z : Matrix n n D :=
    (∑ m ∈ s, ∑ p ∈ s, if m + p = 0 then e m * Quotient.out q *
      σ.matrix n (e p) else 0) - Quotient.out q
  have hz : z ∈ (σ.matrix n).alternatingSubspace := hc
  have hf : f * z * σ.matrix n f ∈ (σ.matrix n).alternatingSubspace := by
    apply QuadraticTorusWittBound.sandwich_mem_alternatingSubspace (K := K) (A := Matrix n n D)
      (σ.matrix n) f
    exact hz
  have hcoef : f * z * σ.matrix n f = -(f * Quotient.out q * σ.matrix n f) :=
    QuadraticTorusWittBound.sandwich_coefficient (K := K) (A := Matrix n n D)
      (σ.matrix n) (Quotient.out q) s S e (weightElement_mul j) hS
  rw [hcoef] at hf
  exact neg_mem_iff.mp hf

/-- A finite selection of weights with no opposite pair has a totally singular
sum, over every field and in every characteristic. -/
theorem isTotallySingular_torusRowWeightSum (q : σ.QuadraticForms n)
    (i : splitTorus (Spec (CommRingCat.of K)) I ⟶ σ.isometryGroup q)
    (S : Finset (I → ℤ))
    (hS : ∀ m ∈ S, ∀ p ∈ S, m + p ≠ 0) :
    σ.IsTotallySingular q (σ.torusRowWeightSum q i S) := by
  intro x hx
  exact quadraticValue_eq_zero_of_vecMul_eq σ q _
    (σ.sum_weightElement_sandwich_mem_quadraticKernel q i S hS)
    (σ.vecMul_sum_weightElement_of_mem_torusRowWeightSum q i S hx)

/-- The sum of the division-algebra multiplicities over any finite selection
of nonopposite weights is bounded by the quadratic Witt index. -/
theorem sum_finrank_torusRowWeightSpace_le_quadraticWittIndex
    (q : σ.QuadraticForms n)
    (i : splitTorus (Spec (CommRingCat.of K)) I ⟶ σ.isometryGroup q)
    (S : Finset (I → ℤ))
    (hS : ∀ m ∈ S, ∀ p ∈ S, m + p ≠ 0) :
    (∑ m ∈ S, Module.finrank D (σ.torusRowWeightSpace q i m)) ≤
      σ.quadraticWittIndex q := by
  rw [← σ.finrank_torusRowWeightSum q i S]
  exact (σ.isTotallySingular_torusRowWeightSum q i S hS).finrank_le_quadraticWittIndex

end Langlands.GroupScheme.Quaternionic.FirstKindInvolution
