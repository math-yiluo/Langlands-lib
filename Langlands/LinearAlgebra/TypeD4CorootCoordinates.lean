import Langlands.GroupScheme.Reductive.IntegralWeylVector
import Langlands.LinearAlgebra.TypeDNumberedLinear
import Langlands.LinearAlgebra.TypeD4LeafParabolicTriple
import Mathlib.LinearAlgebra.RootSystem.Reduced

/-! # Integral coroot coordinates in type D4 -/

noncomputable section

open Matrix

namespace Langlands.LinearAlgebra

private def boundedD4Vector (d : Fin 4 → Fin 3) : Fin 4 → ℤ := fun j => (d j : ℤ) - 1

private theorem boundedD4Vector_eq_coordinateRoot :
    ∀ d : Fin 4 → Fin 3, boundedD4Vector d ⬝ᵥ boundedD4Vector d = 2 →
      ∃ i j : Fin 4, i < j ∧ ∃ s t : Bool, boundedD4Vector d = d4CoordinateRoot i j s t := by
  decide

/-- Integral vectors of squared norm two have exactly two signed coordinates. -/
theorem exists_d4CoordinateRoot_of_dotProduct_self_eq_two (x : Fin 4 → ℤ)
    (hx : x ⬝ᵥ x = 2) :
    ∃ i j : Fin 4, i < j ∧ ∃ s t : Bool, x = d4CoordinateRoot i j s t := by
  have hsq (j : Fin 4) : x j * x j ≤ 2 :=
    (Finset.single_le_sum (fun k _ => mul_self_nonneg (x k)) (Finset.mem_univ j)).trans_eq hx
  have hlo (j : Fin 4) : -1 ≤ x j := by
    by_contra! h
    nlinarith [hsq j, mul_nonneg (show 0 ≤ -x j - 2 by omega) (show 0 ≤ -x j by omega)]
  have hhi (j : Fin 4) : x j ≤ 1 := by
    by_contra! h
    nlinarith [hsq j, mul_nonneg (show 0 ≤ x j - 2 by omega) (show 0 ≤ x j by omega)]
  let d (j : Fin 4) : Fin 3 := ⟨(x j + 1).toNat, by have := hlo j; have := hhi j; omega⟩
  have hd : boundedD4Vector d = x := by
    funext j
    change (((x j + 1).toNat : ℕ) : ℤ) - 1 = x j
    have := hlo j
    omega
  rw [← hd] at hx ⊢
  exact boundedD4Vector_eq_coordinateRoot d hx

section BasedRootDatum

open IntegralWeylVector

variable {I X Y : Type*} [AddCommGroup X] [AddCommGroup Y]
    (P : RootDatum I X Y) (b : P.Base) (hspan : P.corootSpan ℤ = ⊤)
    (e : b.support ≃ Fin 4)

/-- Send the simple coroot basis to the standard integral coordinate vectors. -/
def d4CorootCoordinates : Y →ₗ[ℤ] (Fin 4 → ℤ) :=
  (corootBasis P b hspan).constr ℤ
    (fun i => TypeDNumberedVectors.simple (by decide : 2 ≤ 4) (e i))

@[simp]
theorem d4CorootCoordinates_simple (i : b.support) :
    d4CorootCoordinates P b hspan e (P.coroot i) =
      TypeDNumberedVectors.simple (by decide : 2 ≤ 4) (e i) := by
  rw [d4CorootCoordinates, ← corootBasis_apply P b hspan i, Module.Basis.constr_basis]

/-- The coordinates distinguish cocharacters in the integral coroot lattice. -/
theorem d4CorootCoordinates_injective :
    Function.Injective (d4CorootCoordinates P b hspan e) :=
  (corootBasis P b hspan).injective_constr_of_linearIndependent
    ((TypeDNumberedVectors.linearIndependent_simple (by decide : 2 ≤ 4)).comp e e.injective)

variable (hD : ∀ i j : b.support, P.pairing i.val j.val = CartanMatrix.D 4 (e i) (e j))

include hD in
private theorem d4CorootCoordinates_dotProduct_simple (i : b.support) (y : Y) :
    d4CorootCoordinates P b hspan e (P.coroot i) ⬝ᵥ d4CorootCoordinates P b hspan e y =
      P.root' i y := by
  let c := d4CorootCoordinates P b hspan e
  let v := c (P.coroot i)
  let f : Y →ₗ[ℤ] ℤ :=
    LinearMap.comp
      { toFun := fun w => v ⬝ᵥ w
        map_add' := fun x y => dotProduct_add _ _ _
        map_smul' := fun z x => dotProduct_smul z _ _ } c
  change f y = _
  have hf : f = P.root' i := by
    apply (corootBasis P b hspan).ext
    intro j
    rw [corootBasis_apply P b hspan j]
    change c (P.coroot i) ⬝ᵥ c (P.coroot j) = P.pairing i j
    rw [d4CorootCoordinates_simple, d4CorootCoordinates_simple,
      TypeDNumberedVectors.dotProduct_simple (by decide : 4 ≤ 4), hD]
  rw [hf]

section AllRoots

variable [Finite I] [P.IsReduced]

include hD in
/-- Every root evaluates on a cocharacter by the dot product with its coroot coordinates. -/
theorem d4CorootCoordinates_dotProduct_coroot (i : I) (y : Y) :
    d4CorootCoordinates P b hspan e (P.coroot i) ⬝ᵥ d4CorootCoordinates P b hspan e y =
      P.root' i y := by
  let c := d4CorootCoordinates P b hspan e
  have hsimple (j : I) (hj : j ∈ b.support) (v : Y) :
      c (P.coroot j) ⬝ᵥ c v = P.root' j v :=
    d4CorootCoordinates_dotProduct_simple P b hspan e hD ⟨j, hj⟩ v
  refine b.induction_reflect (p := fun j => ∀ v : Y, c (P.coroot j) ⬝ᵥ c v = P.root' j v) i
    ?_ hsimple ?_ y
  · intro j h v
    change c (P.coroot (P.reflectionPerm j j)) ⬝ᵥ c v =
      P.toLinearMap (P.root (P.reflectionPerm j j)) v
    rw [P.coroot_reflectionPerm, P.coreflection_apply_self, P.root_reflectionPerm,
      P.reflection_apply_self, map_neg, neg_dotProduct, h, map_neg, LinearMap.neg_apply]
  · intro j k hj hk v
    have hsym : P.pairing k j = P.pairing j k := by
      change P.root' k (P.coroot j) = P.root' j (P.coroot k)
      rw [← hsimple k hk, ← hj, dotProduct_comm]
    change c (P.coroot (P.reflectionPerm k j)) ⬝ᵥ c v =
      P.toLinearMap (P.root (P.reflectionPerm k j)) v
    rw [P.coroot_reflectionPerm, P.coreflection_apply_coroot, P.root_reflectionPerm,
      P.reflection_apply_root, map_sub, map_smul, sub_dotProduct, smul_dotProduct,
      hj, hsimple k hk, hsym, map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply]

include hD in
/-- The coordinates of every coroot in a simply connected D4 datum lie in the split D4 model. -/
theorem d4CorootCoordinates_exists_coordinateRoot (i : I) :
    ∃ a b' : Fin 4, a < b' ∧ ∃ s t : Bool,
      d4CorootCoordinates P b hspan e (P.coroot i) = d4CoordinateRoot a b' s t := by
  apply exists_d4CoordinateRoot_of_dotProduct_self_eq_two
  rw [d4CorootCoordinates_dotProduct_coroot P b hspan e hD]
  exact P.pairing_same i

end AllRoots

/-- The three integral cocharacters in the numbered simple-coroot basis. -/
def d4LeafParabolicCoweights (k : Fin 3) : Y :=
  ∑ j : Fin 4, d4LeafParabolicCoefficients k j • P.coroot (e.symm j).val

theorem d4CorootCoordinates_leafParabolicCoweights (k : Fin 3) :
    d4CorootCoordinates P b hspan e (d4LeafParabolicCoweights P b e k) =
      d4LeafParabolicCocharacters k := by
  unfold d4LeafParabolicCoweights
  simp only [map_sum, map_smul, d4CorootCoordinates_simple, Equiv.apply_symm_apply]
  exact d4LeafParabolicCoefficients_toCoordinates k

theorem d4LeafParabolicCoweights_sum :
    ∑ k : Fin 3, d4LeafParabolicCoweights P b e k = 0 := by
  unfold d4LeafParabolicCoweights
  rw [Finset.sum_comm]
  simp only [← Finset.sum_smul, d4LeafParabolicCoefficients_sum, zero_smul, Finset.sum_const_zero]

section Signs

variable [Finite I] [P.IsReduced]

include hspan hD in
/-- Every root outside the common zero face is negative at exactly one
cocharacter of the triple. -/
theorem d4LeafParabolicCoweights_negative_unique (i : I) :
    (∀ k : Fin 3, P.root' i (d4LeafParabolicCoweights P b e k) = 0) ∨
      ∃! k : Fin 3, P.root' i (d4LeafParabolicCoweights P b e k) < 0 := by
  obtain ⟨a, c, hac, s, t, h⟩ := d4CorootCoordinates_exists_coordinateRoot P b hspan e hD i
  simpa only [← h, ← d4CorootCoordinates_leafParabolicCoweights P b hspan e,
    d4CorootCoordinates_dotProduct_coroot P b hspan e hD] using
      d4LeafParabolicTriple_negative_unique a c (ne_of_lt hac) s t

include hspan hD in
/-- The difference of the first two cocharacters has precisely the common zero roots. -/
theorem d4LeafParabolicCoweights_difference_eq_zero_iff (i : I) :
    P.root' i (d4LeafParabolicCoweights P b e 0 - d4LeafParabolicCoweights P b e 1) = 0 ↔
      ∀ k : Fin 3, P.root' i (d4LeafParabolicCoweights P b e k) = 0 := by
  obtain ⟨a, c, hac, s, t, h⟩ := d4CorootCoordinates_exists_coordinateRoot P b hspan e hD i
  simpa only [← h, ← d4CorootCoordinates_leafParabolicCoweights P b hspan e, ← map_sub,
    d4CorootCoordinates_dotProduct_coroot P b hspan e hD] using
      (d4LeafParabolicTriple_zero_iff_difference a c hac s t).symm

end Signs

include hspan hD in
/-- In the standard basis the difference retains the two adjacent vertices 1 and 3. -/
theorem d4LeafParabolicCoweights_difference_pairing (j : b.support) :
    P.root' j (d4LeafParabolicCoweights P b e 0 - d4LeafParabolicCoweights P b e 1) =
      if e j = 0 ∨ e j = 2 then 2 else 0 := by
  rw [← d4CorootCoordinates_dotProduct_simple P b hspan e hD j,
    d4CorootCoordinates_simple, map_sub, d4CorootCoordinates_leafParabolicCoweights,
    d4CorootCoordinates_leafParabolicCoweights]
  exact d4LeafParabolicTriple_difference_pairing (e j)

include hD in
private theorem d4CorootCoordinates_coreflection (v : Y) (j : Fin 4) :
    d4CorootCoordinates P b hspan e (P.coreflection (e.symm j).val v) =
      d4CoordinateSimpleReflection (d4CorootCoordinates P b hspan e v) j := by
  rw [P.coreflection_apply, map_sub, map_smul,
    ← d4CorootCoordinates_dotProduct_simple P b hspan e hD (e.symm j) v,
    d4CorootCoordinates_simple, Equiv.apply_symm_apply]
  rfl

include hD in
private theorem d4CorootCoordinates_foldl_coreflection (w : List (Fin 4)) (v : Y) :
    d4CorootCoordinates P b hspan e
        (w.foldl (fun n j => P.coreflection (e.symm j).val n) v) =
      w.foldl d4CoordinateSimpleReflection (d4CorootCoordinates P b hspan e v) := by
  induction w generalizing v with
  | nil => rfl
  | cons j w ih =>
    rw [List.foldl_cons, List.foldl_cons, ih, d4CorootCoordinates_coreflection P b hspan e hD]

private theorem exists_weyl_foldl_coreflection (w : List (Fin 4)) (v : Y) :
    ∃ θ : P.Aut, θ ∈ P.weylGroup ∧
      θ.coweightEquiv v = w.foldl (fun n j => P.coreflection (e.symm j).val n) v := by
  induction w generalizing v with
  | nil => exact ⟨1, one_mem _, rfl⟩
  | cons j w ih =>
    obtain ⟨θ, hθ, h⟩ := ih (P.coreflection (e.symm j).val v)
    exact ⟨RootPairing.Equiv.reflection P (e.symm j).val * θ,
      mul_mem (P.reflection_mem_weylGroup _) hθ, h⟩

include hspan hD in
/-- In a Weyl conjugate chamber the cocharacter of each parabolic pairs
positively at its leaf and vanishes at the other three simple roots. -/
theorem exists_weyl_d4LeafParabolicCoweights_pairing (k : Fin 3) :
    ∃ θ : P.Aut, θ ∈ P.weylGroup ∧ ∀ j : b.support,
      P.root' j (θ.coweightEquiv (d4LeafParabolicCoweights P b e k)) =
        if e j = d4LeafParabolicVertex k then 2 else 0 := by
  obtain ⟨θ, hθ, h⟩ := exists_weyl_foldl_coreflection P b e
    (d4LeafParabolicReflectionWord k) (d4LeafParabolicCoweights P b e k)
  refine ⟨θ, hθ, fun j => ?_⟩
  rw [h, ← d4CorootCoordinates_dotProduct_simple P b hspan e hD j,
    d4CorootCoordinates_simple, d4CorootCoordinates_foldl_coreflection P b hspan e hD,
    d4CorootCoordinates_leafParabolicCoweights]
  exact d4LeafParabolicReflectionWord_pairing k (e j)

end BasedRootDatum

end Langlands.LinearAlgebra
