import Langlands.Representation.CyclicSpan
import Langlands.Representation.RestrictedTensor.Basic
import Mathlib.Data.Finset.NoncommProd
import Mathlib.Algebra.Module.Projective
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-! # Cyclic evaluation for commuting actions -/

noncomputable section
open scoped Classical TensorProduct

namespace Langlands.RestrictedTensor.CyclicEvaluation

universe uK uI uG uV

variable {K : Type uK} [Field K] {ι : Type uI}
variable {G : ι → Type uG} [∀ i, Monoid (G i)]
variable {V : Type uV} [AddCommGroup V] [Module K V]

/-- Actions at distinct coordinates commute on the ambient vector space. -/
def Commuting (σ : ∀ i, Representation K (G i) V) : Prop :=
  ∀ ⦃i j⦄, i ≠ j → ∀ (g : G i) (h : G j) (x : V),
    σ i g (σ j h x) = σ j h (σ i g x)

variable (σ : ∀ i, Representation K (G i) V) (hσ : Commuting σ)

include hσ in
/-- Distinct coordinate actions commute after extension to the monoid algebras. -/
theorem algebra_commute {i j : ι} (hij : i ≠ j)
    (a : MonoidAlgebra K (G i)) (b : MonoidAlgebra K (G j)) :
    Commute ((σ i).asAlgebraHom a) ((σ j).asAlgebraHom b) := by
  apply LinearMap.ext
  intro x
  change (σ i).asAlgebraHom a ((σ j).asAlgebraHom b x) =
    (σ j).asAlgebraHom b ((σ i).asAlgebraHom a x)
  induction a using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a a' ha ha' => simpa only [map_add, LinearMap.add_apply] using congrArg₂ (· + ·) ha ha'
  | single g c =>
    induction b using MonoidAlgebra.induction_linear with
    | zero => simp
    | add b b' hb hb' =>
      simpa only [map_add, LinearMap.add_apply] using congrArg₂ (· + ·) hb hb'
    | single h d => simp [Representation.asAlgebraHom_single, hσ hij g h x, smul_smul, mul_comm]

/-- Enumeration-independent finite product of the commuting algebra actions. -/
def algebraProduct (S : Finset ι) (a : ∀ i, MonoidAlgebra K (G i)) : Module.End K V :=
  S.noncommProd (fun i => (σ i).asAlgebraHom (a i))
    (fun _ _ _ _ hij => algebra_commute σ hσ hij _ _)

@[simp] theorem algebraProduct_empty (a : ∀ i, MonoidAlgebra K (G i)) :
    algebraProduct σ hσ ∅ a = 1 := rfl

theorem algebraProduct_insert (S : Finset ι) (i : ι) (hi : i ∉ S)
    (a : ∀ i, MonoidAlgebra K (G i)) :
    algebraProduct σ hσ (insert i S) a =
      (σ i).asAlgebraHom (a i) * algebraProduct σ hσ S a := by
  exact Finset.noncommProd_insert_of_notMem _ _ _ _ hi

theorem algebraProduct_insert_right (S : Finset ι) (i : ι) (hi : i ∉ S)
    (a : ∀ i, MonoidAlgebra K (G i)) :
    algebraProduct σ hσ (insert i S) a =
      algebraProduct σ hσ S a * (σ i).asAlgebraHom (a i) := by
  exact Finset.noncommProd_insert_of_notMem' _ _ _ _ hi

theorem algebraProduct_congr {S : Finset ι}
    {a b : ∀ i, MonoidAlgebra K (G i)} (hab : ∀ i ∈ S, a i = b i) :
    algebraProduct σ hσ S a = algebraProduct σ hσ S b :=
  Finset.noncommProd_congr rfl (fun i hi => congrArg (σ i).asAlgebraHom (hab i hi)) _

/-- An operator from a fresh coordinate commutes with the whole finite product. -/
theorem commute_algebraProduct (S : Finset ι) {i : ι} (hi : i ∉ S)
    (a : MonoidAlgebra K (G i)) (b : ∀ j, MonoidAlgebra K (G j)) :
    Commute ((σ i).asAlgebraHom a) (algebraProduct σ hσ S b) := by
  apply Finset.noncommProd_commute
  intro j hj
  exact algebra_commute σ hσ (i := i) (j := j) (fun hij => hi (hij.symm ▸ hj)) a (b j)

/-- A relation at the cyclic vector remains a relation after other coordinate actions. -/
theorem relation_annihilates (v : V) (S : Finset ι) {i : ι} (hi : i ∉ S)
    (a : MonoidAlgebra K (G i)) (b : ∀ j, MonoidAlgebra K (G j))
    (ha : (σ i).asAlgebraHom a v = 0) :
    (σ i).asAlgebraHom a (algebraProduct σ hσ S b v) = 0 := by
  have h := LinearMap.congr_fun (commute_algebraProduct σ hσ S hi a b).eq v
  change (σ i).asAlgebraHom a (algebraProduct σ hσ S b v) =
    algebraProduct σ hσ S b ((σ i).asAlgebraHom a v) at h
  rw [h, ha, map_zero]

/-- The product evaluated at `v` depends only on the individual orbit-span vectors. -/
theorem algebraProduct_congr_eval (v : V) (S : Finset ι)
    (a b : ∀ i, MonoidAlgebra K (G i))
    (hab : ∀ i ∈ S, (σ i).asAlgebraHom (a i) v = (σ i).asAlgebraHom (b i) v) :
    algebraProduct σ hσ S a v = algebraProduct σ hσ S b v := by
  induction S using Finset.induction_on with
  | empty => rfl
  | @insert i S hi ih =>
    rw [algebraProduct_insert σ hσ S i hi, Module.End.mul_apply]
    rw [ih (fun j hj => hab j (Finset.mem_insert_of_mem hj))]
    have hc := LinearMap.congr_fun (commute_algebraProduct σ hσ S hi (a i) b).eq v
    change (σ i).asAlgebraHom (a i) (algebraProduct σ hσ S b v) =
      algebraProduct σ hσ S b ((σ i).asAlgebraHom (a i) v) at hc
    rw [hc, hab i (Finset.mem_insert_self i S)]
    rw [algebraProduct_insert_right σ hσ S i hi, Module.End.mul_apply]

variable (v : V)

/-- The cyclic spaces retain the carrier universe of `V`. -/
abbrev Factor (i : ι) : Type uV := (Langlands.Cyclic.orbitSpan (σ i) v).toSubmodule

/-- A classical linear section used only to implement the canonical evaluation. -/
def presentationSection (i : ι) : Factor σ v i →ₗ[K] MonoidAlgebra K (G i) :=
  Classical.choose ((Langlands.Cyclic.presentation (σ i) v).exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.mpr (Langlands.Cyclic.presentation_surjective (σ i) v)))

@[simp] theorem presentation_section (i : ι) (x : Factor σ v i) :
    Langlands.Cyclic.presentation (σ i) v (presentationSection σ v i x) = x :=
  LinearMap.congr_fun (Classical.choose_spec
    ((Langlands.Cyclic.presentation (σ i) v).exists_rightInverse_of_surjective
      (LinearMap.range_eq_top.mpr (Langlands.Cyclic.presentation_surjective (σ i) v)))) x

@[simp] theorem presentationSection_eval (i : ι) (x : Factor σ v i) :
    (σ i).asAlgebraHom (presentationSection σ v i x) v = (x : V) :=
  congrArg Subtype.val (presentation_section σ v i x)

/-- Extend chosen presentations of a finite tuple by zero outside the finite set. -/
def tupleAlgebra (S : Finset ι) (x : ∀ i : S, Factor σ v i) (j : ι) :
    MonoidAlgebra K (G j) :=
  if hj : j ∈ S then presentationSection σ v j (x ⟨j, hj⟩) else 0

@[simp] theorem tupleAlgebra_mem (S : Finset ι) (x : ∀ i : S, Factor σ v i) (i : S) :
    tupleAlgebra σ v S x i = presentationSection σ v i (x i) := by
  simp [tupleAlgebra, i.2]

/-- Evaluation of a tuple of cyclic vectors. -/
def tupleEval (S : Finset ι) (x : ∀ i : S, Factor σ v i) : V :=
  algebraProduct σ hσ S (tupleAlgebra σ v S x) v

theorem algebraProduct_erase_right (S : Finset ι) (i : ι) (hi : i ∈ S)
    (a : ∀ j, MonoidAlgebra K (G j)) :
    algebraProduct σ hσ S a =
      algebraProduct σ hσ (S.erase i) a * (σ i).asAlgebraHom (a i) :=
  (Finset.noncommProd_erase_mul S hi _ _).symm

/-- Isolate an updated coordinate on the right of the product. -/
theorem tupleEval_update (S : Finset ι) [DecidableEq S] (x : ∀ i : S, Factor σ v i)
    (i : S) (y : Factor σ v i) :
    tupleEval σ hσ v S (Function.update x i y) =
      algebraProduct σ hσ (S.erase i) (tupleAlgebra σ v S x) (y : V) := by
  unfold tupleEval
  rw [algebraProduct_erase_right σ hσ S i i.2, Module.End.mul_apply]
  have hrest : algebraProduct σ hσ (S.erase i)
      (tupleAlgebra σ v S (Function.update x i y)) =
      algebraProduct σ hσ (S.erase i) (tupleAlgebra σ v S x) := by
    apply algebraProduct_congr
    intro j hj
    have hjS := (Finset.mem_erase.mp hj).2
    have hji : (⟨j, hjS⟩ : S) ≠ i := fun he => (Finset.mem_erase.mp hj).1 (congrArg Subtype.val he)
    simp [tupleAlgebra, hjS, Function.update_of_ne hji]
  rw [hrest]
  simp only [tupleAlgebra_mem, Function.update_self, presentationSection_eval]

/-- Multilinear evaluation of finite tuples of cyclic vectors. -/
def evalMultilinear (S : Finset ι) :
    MultilinearMap K (fun i : S => Factor σ v i) V where
  toFun := tupleEval σ hσ v S
  map_update_add' x i a b := by
    rw [tupleEval_update, tupleEval_update, tupleEval_update]
    exact map_add _ _ _
  map_update_smul' x i c a := by
    rw [tupleEval_update, tupleEval_update]
    exact map_smul _ _ _

/-- The canonical finite-stage cyclic tensor evaluation. -/
def evalStage (S : Finset ι) : Stage K (Factor σ v) S →ₗ[K] V :=
  PiTensorProduct.lift (evalMultilinear σ hσ v S)

@[simp] theorem evalStage_tprod (S : Finset ι) (x : ∀ i : S, Factor σ v i) :
    evalStage σ hσ v S (PiTensorProduct.tprod K x) = tupleEval σ hσ v S x :=
  PiTensorProduct.lift.tprod _

/-- Evaluation descends the product of arbitrary monoid-algebra representatives. -/
theorem evalStage_presentation (S : Finset ι) (a : ∀ i, MonoidAlgebra K (G i)) :
    evalStage σ hσ v S (PiTensorProduct.tprod K
      (fun i : S => Langlands.Cyclic.presentation (σ i) v (a i))) =
      algebraProduct σ hσ S a v := by
  rw [evalStage_tprod]
  apply algebraProduct_congr_eval
  intro i hi
  simp [tupleAlgebra, hi]

/-- The presentation formula uniquely determines the finite-stage map. -/
theorem evalStage_unique (S : Finset ι) (f : Stage K (Factor σ v) S →ₗ[K] V)
    (hf : ∀ a : ∀ i, MonoidAlgebra K (G i),
      f (PiTensorProduct.tprod K (fun i : S => Langlands.Cyclic.presentation (σ i) v (a i))) =
        algebraProduct σ hσ S a v) : f = evalStage σ hσ v S := by
  ext x
  change f (PiTensorProduct.tprod K x) = evalStage σ hσ v S (PiTensorProduct.tprod K x)
  have hx : (fun i : S => Langlands.Cyclic.presentation (σ i) v (tupleAlgebra σ v S x i)) = x := by
    funext i
    simp
  rw [← hx, hf (tupleAlgebra σ v S x), evalStage_presentation]

set_option backward.isDefEq.respectTransparency false in
/-- The finite product is unchanged by adjoining identity algebra elements. -/
theorem algebraProduct_subset {S T : Finset ι} (hST : S ⊆ T)
    (a : ∀ i, MonoidAlgebra K (G i)) (ha : ∀ i ∈ T, i ∉ S → a i = 1) :
    algebraProduct σ hσ T a = algebraProduct σ hσ S a := by
  have hdis : Disjoint S (T \ S) := Finset.disjoint_sdiff
  have hprod : algebraProduct σ hσ (T \ S) a = 1 := by
    apply (Finset.noncommProd_eq_pow_card _ _ _ 1 ?_).trans (one_pow _)
    intro i hi
    rw [ha i (Finset.mem_sdiff.mp hi).1 (Finset.mem_sdiff.mp hi).2, map_one]
  have hunion := Finset.union_sdiff_of_subset hST
  change T.noncommProd _ _ = S.noncommProd _ _
  rw [← hunion, Finset.noncommProd_union_of_disjoint hdis]
  change algebraProduct σ hσ S a * algebraProduct σ hσ (T \ S) a = _
  rw [hprod, mul_one]
  rfl

/-- Products also ignore newly adjoined coordinates that merely fix the cyclic vector. -/
theorem algebraProduct_subset_eval {S T : Finset ι} (hST : S ⊆ T)
    (a b : ∀ i, MonoidAlgebra K (G i))
    (hab : ∀ i ∈ S, (σ i).asAlgebraHom (a i) v = (σ i).asAlgebraHom (b i) v)
    (ha : ∀ i ∈ T, i ∉ S → (σ i).asAlgebraHom (a i) v = v) :
    algebraProduct σ hσ T a v = algebraProduct σ hσ S b v := by
  let c : ∀ i, MonoidAlgebra K (G i) := fun i => if i ∈ S then b i else 1
  calc
    algebraProduct σ hσ T a v = algebraProduct σ hσ T c v := by
      apply algebraProduct_congr_eval
      intro i hi
      by_cases hiS : i ∈ S
      · simpa [c, hiS] using hab i hiS
      · simpa [c, hiS] using ha i hi hiS
    _ = algebraProduct σ hσ S c v := by
      rw [algebraProduct_subset σ hσ hST c (by intros; simp_all [c])]
    _ = algebraProduct σ hσ S b v := by
      rw [algebraProduct_congr σ hσ (a := c) (b := b) (by intros; simp_all [c])]

/-- Adjoining distinguished generators preserves tuple evaluation. -/
theorem tupleEval_extend {S T : Finset ι} (hST : S ⊆ T)
    (x : ∀ i : S, Factor σ v i) :
    tupleEval σ hσ v T (extend (fun i => Langlands.Cyclic.generator (σ i) v) x) =
      tupleEval σ hσ v S x := by
  apply algebraProduct_subset_eval σ hσ v hST
  · intro i hi
    simp [tupleAlgebra, hST hi, hi, extend]
  · intro i hi hiS
    simp [tupleAlgebra, hi, extend, hiS]

/-- Compatibility with every restricted-tensor transition. -/
theorem evalStage_transition {S T : Finset ι} (hST : S ⊆ T) :
    (evalStage σ hσ v T).comp
      (transition (fun i => Langlands.Cyclic.generator (σ i) v) hST) =
      evalStage σ hσ v S := by
  ext x
  simp [tupleEval_extend σ hσ v hST]

@[simp] theorem tupleEval_generator (S : Finset ι) :
    tupleEval σ hσ v S (fun i => Langlands.Cyclic.generator (σ i) v) = v := by
  have h := algebraProduct_subset_eval σ hσ v (Finset.empty_subset S)
    (tupleAlgebra σ v S (fun i => Langlands.Cyclic.generator (σ i) v))
    (fun _ => 1) (by simp) (by intros; simp_all [tupleAlgebra])
  simpa [tupleEval] using h

@[simp] theorem evalStage_generator (S : Finset ι) :
    evalStage σ hσ v S (PiTensorProduct.tprod K
      (fun i => Langlands.Cyclic.generator (σ i) v)) = v := by
  rw [evalStage_tprod, tupleEval_generator]

/-- The empty tensor, identified with the scalar one, evaluates to `v`. -/
@[simp] theorem evalStage_empty (x : ∀ i : (∅ : Finset ι), Factor σ v i) :
    evalStage σ hσ v ∅ (PiTensorProduct.tprod K x) = v := by
  rw [evalStage_tprod]
  rfl

/-- Under the empty-tensor scalar identification, evaluation is scalar multiplication by `v`. -/
theorem evalStage_empty_scalar (x : Stage K (Factor σ v) ∅) :
    evalStage σ hσ v ∅ x =
      PiTensorProduct.isEmptyEquiv (R := K) (s := fun i : (∅ : Finset ι) => Factor σ v i)
        (∅ : Finset ι) x • v := by
  induction x using PiTensorProduct.induction_on with
  | smul_tprod c x => simp [tupleEval]
  | add x y hx hy => simp [hx, hy, add_smul]

/-- A monoid-orbit vector, as an element of its cyclic space. -/
def orbitVector (i : ι) (g : G i) : Factor σ v i :=
  (Langlands.Cyclic.orbitSpan (σ i) v).toRepresentation g (Langlands.Cyclic.generator (σ i) v)

@[simp] theorem orbitVector_val (i : ι) (g : G i) :
    (orbitVector σ v i g : V) = σ i g v := rfl

/-- Enumeration-independent product of coordinate monoid operators. -/
def actionProduct (S : Finset ι) (g : ∀ i, G i) : Module.End K V :=
  S.noncommProd (fun i => σ i (g i)) (fun _ _ _ _ hij =>
    LinearMap.ext (fun x => hσ hij _ _ x))

/-- The pure-orbit formula for finite cyclic evaluation. -/
theorem evalStage_orbit (S : Finset ι) (g : ∀ i, G i) :
    evalStage σ hσ v S (PiTensorProduct.tprod K (fun i : S => orbitVector σ v i (g i))) =
      actionProduct σ hσ S g v := by
  have hpres : (fun i : S => orbitVector σ v i (g i)) =
      (fun i : S => Langlands.Cyclic.presentation (σ i) v (MonoidAlgebra.single (g i) 1)) := by
    funext i
    apply Subtype.ext
    simp
  rw [hpres, evalStage_presentation σ hσ v S (fun i => MonoidAlgebra.single (g i) 1)]
  simp only [algebraProduct, Representation.asAlgebraHom_single_one, actionProduct]

/-- Evaluation intertwines the action on a single tensor coordinate. -/
theorem tupleEval_coordinate (S : Finset ι) [DecidableEq S]
    (x : ∀ i : S, Factor σ v i) (i : S) (g : G i) :
    tupleEval σ hσ v S (Function.update x i
      ((Langlands.Cyclic.orbitSpan (σ i) v).toRepresentation g (x i))) =
      σ i g (tupleEval σ hσ v S x) := by
  rw [tupleEval_update]
  have hx : tupleEval σ hσ v S x =
      algebraProduct σ hσ (S.erase i) (tupleAlgebra σ v S x) (x i : V) := by
    simpa using tupleEval_update σ hσ v S x i (x i)
  rw [hx]
  have hc := LinearMap.congr_fun (commute_algebraProduct σ hσ (S.erase i)
    (Finset.notMem_erase (i : ι) S) (MonoidAlgebra.single g 1) (tupleAlgebra σ v S x)).eq (x i : V)
  change algebraProduct σ hσ (S.erase i) (tupleAlgebra σ v S x) (σ i g (x i : V)) = _
  simpa only [Representation.asAlgebraHom_single_one, Module.End.mul_apply] using hc.symm

/-- The endomorphism applying the restricted representation to coordinate `i`. -/
def coordinateAction (S : Finset ι) (i : S) (g : G i) :
    Module.End K (Stage K (Factor σ v) S) :=
  PiTensorProduct.map (Function.update
    (fun j : S => (LinearMap.id : Factor σ v j →ₗ[K] Factor σ v j)) i
    ((Langlands.Cyclic.orbitSpan (σ i) v).toRepresentation g))

@[simp] theorem coordinateAction_tprod (S : Finset ι) (i : S) (g : G i)
    (x : ∀ j : S, Factor σ v j) :
    coordinateAction σ v S i g (PiTensorProduct.tprod K x) =
      PiTensorProduct.tprod K (Function.update x i
        ((Langlands.Cyclic.orbitSpan (σ i) v).toRepresentation g (x i))) := by
  rw [coordinateAction, PiTensorProduct.map_tprod]
  congr 1
  funext j
  by_cases hji : j = i
  · subst j; simp
  · simp [Function.update_of_ne hji]

/-- Finite-coordinate equivariance, as an equality of linear maps. -/
theorem evalStage_coordinateAction (S : Finset ι) (i : S) (g : G i) :
    (evalStage σ hσ v S).comp (coordinateAction σ v S i g) =
      (σ i g).comp (evalStage σ hσ v S) := by
  ext x
  simp [tupleEval_coordinate]

/-- Insert any missing generator coordinates and act at the indicated coordinate. -/
def insertAction (S : Finset ι) (i : ι) (g : G i) :
    Stage K (Factor σ v) S →ₗ[K] Stage K (Factor σ v) (insert i S) :=
  (coordinateAction σ v (insert i S) ⟨i, Finset.mem_insert_self i S⟩ g).comp
    (transition (fun j => Langlands.Cyclic.generator (σ j) v) (Finset.subset_insert i S))

/-- Equivariance also holds when the acting coordinate must first be inserted. -/
theorem evalStage_insertAction (S : Finset ι) (i : ι) (g : G i) :
    (evalStage σ hσ v (insert i S)).comp (insertAction σ v S i g) =
      (σ i g).comp (evalStage σ hσ v S) := by
  rw [insertAction, ← LinearMap.comp_assoc, evalStage_coordinateAction,
    LinearMap.comp_assoc, evalStage_transition]

/-- The induced evaluation on the restricted tensor product with any exceptional set. -/
def eval (E : Finset ι) :
    Space K (Factor σ v) E (fun i => Langlands.Cyclic.generator (σ i) v) →ₗ[K] V :=
  lift E (fun i => Langlands.Cyclic.generator (σ i) v)
    (fun S => evalStage σ hσ v S.1)
    (fun _S _T h x => LinearMap.congr_fun (evalStage_transition σ hσ v h) x)

@[simp] theorem eval_of (E : Finset ι) (S : Index E) (x : Stage K (Factor σ v) S.1) :
    eval σ hσ v E (of K (Factor σ v) E
      (fun i => Langlands.Cyclic.generator (σ i) v) S x) = evalStage σ hσ v S.1 x := rfl

@[simp] theorem eval_pure (E : Finset ι) (S : Index E) (x : ∀ i : S.1, Factor σ v i) :
    eval σ hσ v E (pure E (fun i => Langlands.Cyclic.generator (σ i) v) S x) =
      tupleEval σ hσ v S.1 x := by
  simp [pure]

/-- Every all-generator pure tensor maps to the original cyclic vector. -/
@[simp] theorem eval_generator (E : Finset ι) (S : Index E) :
    eval σ hσ v E (pure E (fun i => Langlands.Cyclic.generator (σ i) v) S
      (fun i => Langlands.Cyclic.generator (σ i) v)) = v := by
  simp

end Langlands.RestrictedTensor.CyclicEvaluation
