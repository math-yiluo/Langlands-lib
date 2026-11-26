import Langlands.LinearAlgebra.GMFamilyGramVolume

/-! # Weights for vertices cut out by affine inequalities -/

noncomputable section

open scoped RealInnerProductSpace
open Classical Submodule Module
open Langlands.GMFamily

namespace Langlands.LinearAlgebra.AffineVertexWeights

variable {ι V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] (v : ι → V)

/-- A subset of the normals that forms a basis. -/
abbrev BasisIndex := {s : Finset ι // LinearIndependent ℝ (fun j : s => v j) ∧
  s.card = finrank ℝ V}

variable {v}

/-- The basis indexed by a subset of the normals. -/
def BasisIndex.basis (J : BasisIndex v) : Basis J.val ℝ V :=
  Basis.mk J.prop.1 (J.prop.1.span_eq_top_of_card_eq_finrank' (by simpa using J.prop.2)).ge

@[simp]
theorem BasisIndex.basis_apply (J : BasisIndex v) (j : J.val) : J.basis j = v j := by
  simp [BasisIndex.basis]

/-- Extend the offsets on the basis to a linear function on the space of normals. -/
def BasisIndex.interpolate (J : BasisIndex v) (h : ι → ℝ) : Module.Dual ℝ V :=
  J.basis.constr ℝ (fun i => h i)

@[simp]
theorem BasisIndex.interpolate_apply_of_mem (J : BasisIndex v) (h : ι → ℝ) {i : ι}
    (hi : i ∈ J.val) : J.interpolate h (v i) = h i := by
  simpa only [BasisIndex.interpolate, BasisIndex.basis_apply] using
    (J.basis.constr_basis (S := ℝ) (fun j : J.val => h j) ⟨i, hi⟩)

/-- Evaluate the affine inequality at the point determined by the equations for `J`. -/
def BasisIndex.slack (J : BasisIndex v) (j : ι) : Module.Dual ℝ (ι → ℝ) :=
  LinearMap.proj j - ∑ i : J.val, J.basis.coord i (v j) • LinearMap.proj (i : ι)

theorem BasisIndex.slack_apply (J : BasisIndex v) (j : ι) (h : ι → ℝ) :
    J.slack j h = h j - J.interpolate h (v j) := by
  simp [BasisIndex.slack, BasisIndex.interpolate, Basis.constr_apply_fintype, Basis.coord_apply,
    LinearMap.sum_apply, mul_comm]

@[simp]
theorem BasisIndex.slack_apply_of_mem (J : BasisIndex v) {i : ι} (hi : i ∈ J.val) (h : ι → ℝ) :
    J.slack i h = 0 := by rw [J.slack_apply, J.interpolate_apply_of_mem h hi, sub_self]

theorem BasisIndex.slack_single_of_notMem (J : BasisIndex v) (j i : ι) (hi : i ∉ J.val) :
    J.slack j (Pi.single i 1) = if j = i then 1 else 0 := by
  have he : J.interpolate (Pi.single i 1) = 0 := by
    apply J.basis.ext
    intro k
    rw [J.basis_apply, J.interpolate_apply_of_mem _ k.prop, LinearMap.zero_apply,
      Pi.single_eq_of_ne]
    exact fun h => hi (h ▸ k.prop)
  rw [J.slack_apply, he, LinearMap.zero_apply, sub_zero, Pi.single_apply]

variable (v)

/-- An external inequality at a candidate vertex. -/
abbrev WallIndex := Σ J : BasisIndex v, {j : ι // j ∉ J.val}

/-- The offset hyperplane on which an external inequality becomes an equality. -/
def wallForm (A : WallIndex v) : Module.Dual ℝ (ι → ℝ) := A.1.slack A.2

theorem wallForm_ne_zero (A : WallIndex v) : wallForm v A ≠ 0 := by
  intro h
  have he := congrArg (fun f : Module.Dual ℝ (ι → ℝ) => f (Pi.single (A.2 : ι) 1)) h
  simp only [wallForm, BasisIndex.slack_single_of_notMem _ _ _ A.2.prop, ite_true,
    LinearMap.zero_apply, one_ne_zero] at he

/-- The real normalizing volume divided by the product of the evaluations on the basis. -/
def weight (param : V →ₗ[ℝ] ℂ) (J : BasisIndex v) : ℂ :=
  (gramVolume (fun i : J.val => v i) : ℂ) / ∏ i ∈ J.val, param (v i)

/-- Sum of the weights of the strictly feasible basis intersections. -/
def vertexSum [Fintype ι] (param : V →ₗ[ℝ] ℂ) (h : ι → ℝ) : ℂ :=
  ∑ J : BasisIndex v, if ∀ j ∉ J.val, 0 < J.slack j h then weight v param J else 0

variable {v}

/-- The offsets on a zero normal are constant across candidate intersections. -/
theorem slack_of_normal_eq_zero (J : BasisIndex v) {j : ι} (hj : v j = 0) (h : ι → ℝ) :
    J.slack j h = h j := by rw [J.slack_apply, hj, map_zero, sub_zero]

/-- The single new index together with the basis supporting the intersection. -/
def wallSupport (A : WallIndex v) : Finset ι := insert (A.2 : ι) A.1.val

omit [FiniteDimensional ℝ V] in
@[simp]
theorem erase_wallSupport (A : WallIndex v) : (wallSupport A).erase (A.2 : ι) = A.1.val := by
  simp [wallSupport, A.2.prop]

omit [FiniteDimensional ℝ V] in
theorem eq_of_support_eq_of_index_eq {A B : WallIndex v}
    (h : wallSupport A = wallSupport B) (hi : (A.2 : ι) = (B.2 : ι)) : A = B := by
  have h₁ : A.1 = B.1 := Subtype.ext (by
    rw [← erase_wallSupport A, ← erase_wallSupport B, h, hi])
  cases A
  cases B
  cases h₁
  exact congrArg (Sigma.mk _) (Subtype.ext hi)

/-- The dependency with coefficient one at the external normal, obtained by expanding it in
    the basis of the wall index. -/
def circuitCoeff (A : WallIndex v) (i : ι) : ℝ :=
  if i = (A.2 : ι) then 1 else
    if hi : i ∈ A.1.val then -A.1.basis.coord ⟨i, hi⟩ (v A.2) else 0

theorem sum_circuitCoeff_smul (A : WallIndex v) :
    ∑ i ∈ wallSupport A, circuitCoeff A i • v i = 0 := by
  rw [wallSupport, Finset.sum_insert A.2.prop]
  simp only [circuitCoeff, ite_true, one_smul]
  rw [← Finset.sum_coe_sort]
  have h (i : A.1.val) : (i : ι) ≠ (A.2 : ι) := fun he => A.2.prop (he ▸ i.prop)
  simp only [h, ite_false, dite_eq_left, Subtype.prop, neg_smul,
    Finset.sum_neg_distrib]
  have hr := A.1.basis.sum_repr (v A.2)
  simp only [BasisIndex.basis_apply, Basis.coord_apply] at hr ⊢
  rw [hr, add_neg_cancel]

theorem sum_circuitCoeff_mul (A : WallIndex v) (h : ι → ℝ) :
    ∑ i ∈ wallSupport A, circuitCoeff A i * h i = wallForm v A h := by
  rw [wallSupport, Finset.sum_insert A.2.prop, wallForm, A.1.slack_apply, ← Finset.sum_coe_sort]
  have hi (i : A.1.val) : (i : ι) ≠ (A.2 : ι) := fun he => A.2.prop (he ▸ i.prop)
  simp only [circuitCoeff, hi, ite_true, ite_false, dite_eq_left, Subtype.prop, one_mul, neg_mul,
    Finset.sum_neg_distrib, BasisIndex.interpolate, Basis.constr_apply_fintype, Basis.coord_apply,
    Basis.equivFun_apply, smul_eq_mul, sub_eq_add_neg]

/-- A deletion from the same set of normals has its missing slack related by the circuit
    coefficient of the deleted normal. -/
theorem mul_wallForm_eq_of_support_eq {A B : WallIndex v} (h : wallSupport A = wallSupport B)
    (x : ι → ℝ) : circuitCoeff A B.2 * wallForm v B x = wallForm v A x := by
  have hB : (B.2 : ι) ∈ wallSupport A := h ▸ Finset.mem_insert_self _ _
  have heval : ∑ i ∈ wallSupport A, circuitCoeff A i * B.1.interpolate x (v i) = 0 := by
    simpa only [map_sum, map_smul, smul_eq_mul, map_zero] using
      congrArg (B.1.interpolate x) (sum_circuitCoeff_smul A)
  calc
    circuitCoeff A B.2 * wallForm v B x = ∑ i ∈ wallSupport A, circuitCoeff A i * B.1.slack i x := by
      symm
      rw [Finset.sum_eq_single (B.2 : ι)]
      · rfl
      · intro i hi hiB
        rw [h] at hi
        have hiB' : i ∈ B.1.val := (Finset.mem_insert.mp hi).resolve_left hiB
        rw [B.1.slack_apply_of_mem hiB', mul_zero]
      · exact fun hn => (hn hB).elim
    _ = ∑ i ∈ wallSupport A, circuitCoeff A i * x i := by
      simp only [BasisIndex.slack_apply, mul_sub, Finset.sum_sub_distrib, heval, sub_zero]
    _ = wallForm v A x := sum_circuitCoeff_mul A x

theorem circuitCoeff_ne_zero_of_support_eq {A B : WallIndex v} (h : wallSupport A = wallSupport B) :
    circuitCoeff A B.2 ≠ 0 := by
  intro hc
  apply wallForm_ne_zero v A
  apply LinearMap.ext
  intro x
  simpa [hc] using (mul_wallForm_eq_of_support_eq h x).symm

private def replaceIndex (A : WallIndex v) (i : A.1.val) :
    A.1.val ≃ (wallSupport A).erase (i : ι) :=
  (Equiv.swap (i : ι) (A.2 : ι)).subtypeEquiv fun j => by
    have hi : (i : ι) ≠ (A.2 : ι) := fun he => A.2.prop (he ▸ i.prop)
    by_cases hji : j = (i : ι)
    · subst j
      simp [wallSupport, i.prop, hi.symm]
    by_cases hjA : j = (A.2 : ι)
    · subst j
      simp [A.2.prop]
    simp [Equiv.swap_apply_of_ne_of_ne hji hjA, wallSupport, hji, hjA]

/-- The volume of a deletion is the original basis volume times the absolute circuit
    coefficient of the omitted index. -/
theorem gramVolume_erase_wallSupport (A : WallIndex v) {i : ι} (hi : i ∈ wallSupport A) :
    gramVolume (fun j : (wallSupport A).erase i => v j) =
      |circuitCoeff A i| * gramVolume (fun j : A.1.val => v j) := by
  rcases Finset.mem_insert.mp hi with rfl | hi
  · have he : (wallSupport A).erase (A.2 : ι) = A.1.val := erase_wallSupport A
    have hvol : gramVolume (fun j : (wallSupport A).erase (A.2 : ι) => v j) =
        gramVolume (fun j : A.1.val => v j) := by
      let e : A.1.val ≃ (wallSupport A).erase (A.2 : ι) :=
        Equiv.subtypeEquivRight (fun x => by rw [he])
      exact (gramVolume_reindex e (fun j => v j)).symm
    rw [hvol]
    simp [circuitCoeff]
  · let j : A.1.val := ⟨i, hi⟩
    let e := replaceIndex A j
    have he : (fun x : (wallSupport A).erase i => v x) ∘ e =
        Function.update (fun x => A.1.basis x) j (v A.2) := by
      funext x
      by_cases hxj : x = j
      · subst x
        simp [e, replaceIndex, Function.comp_apply]
      have hxi : (x : ι) ≠ (j : ι) := fun h => hxj (Subtype.ext h)
      have hxA : (x : ι) ≠ (A.2 : ι) := fun h => A.2.prop (h ▸ x.prop)
      simp [e, replaceIndex, Function.comp_apply, Equiv.swap_apply_of_ne_of_ne hxi hxA, hxj]
    rw [← gramVolume_reindex e, he]
    have hvol := gramVolume_update_basis A.1.basis j (v A.2)
    have hc : |circuitCoeff A i| = |A.1.basis.coord j (v A.2)| := by
      simp only [circuitCoeff, show i ≠ (A.2 : ι) from fun h => A.2.prop (h ▸ hi),
        ite_false, dite_eq_left hi, abs_neg, j]
    rw [hc]
    have hup :
        Function.update (fun x => A.1.basis x) j (v A.2) =
          @Function.update A.1.val (fun _ => V) (Classical.decEq A.1.val)
            (fun x => A.1.basis x) j (v A.2) :=
      congrArg (fun dec => @Function.update A.1.val (fun _ => V) dec
        (fun x => A.1.basis x) j (v A.2)) (Subsingleton.elim _ _)
    rw [hup]
    simpa only [BasisIndex.basis_apply] using hvol

/-- Each nonzero circuit coefficient specifies a basis deletion of the same wall support. -/
theorem exists_wallIndex_of_circuitCoeff_ne_zero (A : WallIndex v)
    {i : ι} (hi : i ∈ wallSupport A) (hc : circuitCoeff A i ≠ 0) :
    ∃ B : WallIndex v, wallSupport B = wallSupport A ∧ (B.2 : ι) = i := by
  have hpos : 0 < gramVolume (fun j : (wallSupport A).erase i => v j) := by
    rw [gramVolume_erase_wallSupport A hi]
    exact mul_pos (abs_pos.mpr hc) ((gramVolume_pos_iff _).mpr A.1.prop.1)
  have hcard : ((wallSupport A).erase i).card = finrank ℝ V := by
    rw [Finset.card_erase_of_mem hi, wallSupport, Finset.card_insert_of_notMem A.2.prop, A.1.prop.2]
    omega
  let B : WallIndex v :=
    ⟨⟨(wallSupport A).erase i, (gramVolume_pos_iff _).mp hpos, hcard⟩, i, Finset.notMem_erase _ _⟩
  exact ⟨B, Finset.insert_erase hi, rfl⟩

/-- The basis weight on a deletion in terms of the original volume and the full support product. -/
theorem weight_eq_of_support_eq (param : V →ₗ[ℝ] ℂ) {A B : WallIndex v}
    (h : wallSupport A = wallSupport B) (hn : ∀ i ∈ wallSupport A, param (v i) ≠ 0) :
    weight v param B.1 =
      (gramVolume (fun j : A.1.val => v j) : ℂ) / (∏ j ∈ wallSupport A, param (v j)) *
        (↑|circuitCoeff A B.2| : ℂ) * param (v B.2) := by
  have hB : (B.2 : ι) ∈ wallSupport A := h ▸ Finset.mem_insert_self _ _
  have hvol := gramVolume_erase_wallSupport A hB
  rw [h, erase_wallSupport] at hvol
  unfold weight
  rw [hvol, Complex.ofReal_mul, h, wallSupport, Finset.prod_insert B.2.prop]
  have hp : ∏ j ∈ B.1.val, param (v j) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun i hi => hn i (h.symm ▸ Finset.mem_insert_of_mem hi)
  field_simp [hn _ hB]

end Langlands.LinearAlgebra.AffineVertexWeights
