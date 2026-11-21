import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.PiTensorProduct.DFinsupp

/-! Finite support and separation of tensor products of linear coordinates. -/

noncomputable section
set_option autoImplicit false

namespace Langlands

section Factor

variable {R V ι : Type*} [Field R] [AddCommGroup V] [Module R V] [DecidableEq ι]
  {W : ι → Type*} [∀ i, AddCommGroup (W i)] [∀ i, Module R (W i)]
  (p : ∀ i, V →ₗ[R] W i)
  (hfin : ∀ v, ∃ s : Finset ι, ∀ i ∉ s, p i v = 0)

private def coordinateValue (v : V) : Π₀ i, W i :=
  DFinsupp.mk (hfin v).choose (fun i => p i v)

private theorem coordinateValue_apply (v : V) (i : ι) : coordinateValue p hfin v i = p i v := by
  by_cases hi : i ∈ (hfin v).choose
  · exact DFinsupp.mk_of_mem hi
  · exact (DFinsupp.mk_of_notMem hi).trans ((hfin v).choose_spec i hi).symm

/-- Linear coordinates with pointwise finite support assemble into a direct-sum map. -/
def finiteSupportCoordinateMap : V →ₗ[R] Π₀ i, W i where
  toFun := coordinateValue p hfin
  map_add' v w := by ext i; simp only [DFinsupp.add_apply, coordinateValue_apply, map_add]
  map_smul' a v := by
    ext i
    simp only [DFinsupp.smul_apply, coordinateValue_apply, map_smul, RingHom.id_apply]

@[simp] theorem finiteSupportCoordinateMap_apply (v : V) (i : ι) :
    finiteSupportCoordinateMap p hfin v i = p i v :=
  coordinateValue_apply p hfin v i

end Factor

section Tensor

variable {R ι : Type*} [Field R] [Fintype ι] [DecidableEq ι]
  {κ : ι → Type*} [∀ i, DecidableEq (κ i)]
  {V : ι → Type*} [∀ i, AddCommGroup (V i)] [∀ i, Module R (V i)]
  {W : ∀ i, κ i → Type*} [∀ i j, AddCommGroup (W i j)] [∀ i j, Module R (W i j)]
  (p : ∀ i j, V i →ₗ[R] W i j)
  (hfin : ∀ i x, ∃ s : Finset (κ i), ∀ j ∉ s, p i j x = 0)

/-- Distribute the finite tensor product over the factor coordinate sums. -/
def finiteSupportTensorCoordinateMap :
    PiTensorProduct R V →ₗ[R] Π₀ j : (∀ i, κ i), PiTensorProduct R (fun i => W i (j i)) :=
  (PiTensorProduct.ofDFinsuppEquiv (R := R) (M := W)).toLinearMap ∘ₗ
    PiTensorProduct.map (fun i => finiteSupportCoordinateMap (p i) (hfin i))

@[simp] theorem finiteSupportTensorCoordinateMap_apply (x : PiTensorProduct R V) (j : ∀ i, κ i) :
    finiteSupportTensorCoordinateMap p hfin x j = PiTensorProduct.map (fun i => p i (j i)) x := by
  let L := (DFinsupp.lapply (R := R) j).comp (finiteSupportTensorCoordinateMap p hfin)
  have hL : L = PiTensorProduct.map (fun i => p i (j i)) := by
    apply PiTensorProduct.ext
    apply MultilinearMap.ext
    intro v
    change finiteSupportTensorCoordinateMap p hfin (PiTensorProduct.tprod R v) j = _
    simp [finiteSupportTensorCoordinateMap]
  exact LinearMap.congr_fun hL x

include hfin in
/-- Each tensor has only finitely many nonzero projected coordinates. -/
theorem finiteSupportTensorCoordinateMap_finite (x : PiTensorProduct R V) :
    {j : ∀ i, κ i | PiTensorProduct.map (fun i => p i (j i)) x ≠ 0}.Finite := by
  classical
  refine (finiteSupportTensorCoordinateMap p hfin x).support.finite_toSet.subset fun j hj => ?_
  exact DFinsupp.mem_support_iff.mpr (by
    rw [finiteSupportTensorCoordinateMap_apply]
    exact hj)

include hfin in
/-- When the factor coordinates separate their vectors, the tensor coordinates also separate. -/
theorem finiteSupportTensorCoordinateMap_detects
    (hsep : ∀ i x, (∀ j, p i j x = 0) → x = 0)
    (x : PiTensorProduct R V) (hx : ∀ j : (∀ i, κ i),
      PiTensorProduct.map (fun i => p i (j i)) x = 0) :
    x = 0 := by
  let f := fun i => finiteSupportCoordinateMap (p i) (hfin i)
  have hf (i : ι) : (f i).ker = ⊥ := by
    apply LinearMap.ker_eq_bot'.mpr
    intro v hv
    apply hsep i v
    intro j
    simpa only [f, finiteSupportCoordinateMap_apply, DFinsupp.zero_apply] using
      congrArg (fun w : (Π₀ j, W i j) => w j) hv
  choose q hq using fun i => (f i).exists_leftInverse_of_injective (hf i)
  have hcomp : PiTensorProduct.map q ∘ₗ PiTensorProduct.map f = LinearMap.id := by
    rw [← PiTensorProduct.map_comp, show (fun i => q i ∘ₗ f i) = (fun _ => LinearMap.id) from funext hq,
      PiTensorProduct.map_id]
  have hmap : Function.Injective (PiTensorProduct.map f) :=
    (show Function.LeftInverse (PiTensorProduct.map q) (PiTensorProduct.map f) from
      fun v => LinearMap.congr_fun hcomp v).injective
  have hinj : Function.Injective (finiteSupportTensorCoordinateMap p hfin) :=
    ((PiTensorProduct.ofDFinsuppEquiv (R := R) (M := W)).injective).comp hmap
  apply hinj
  rw [map_zero]
  ext j
  exact (finiteSupportTensorCoordinateMap_apply p hfin x j).trans (hx j)

end Tensor

end Langlands
