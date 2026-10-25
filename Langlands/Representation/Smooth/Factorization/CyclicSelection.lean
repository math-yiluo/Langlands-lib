import Langlands.Representation.CyclicTransport
import Langlands.Representation.RestrictedTensor.Action
import Langlands.Representation.Smooth.Admissibility.EquivalenceProof
import Mathlib.Basic.Complex.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank

/-! # Simultaneous selection of cyclic local factors -/

noncomputable section

namespace Langlands.FlathSelection

universe uI uG uV

variable {ι : Type uI} {G : ι → Type uG} [∀ i, Group (G i)]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]

section LocalSelection

variable [∀ i, TopologicalSpace (G i)]

/-- The two properties of a local cyclic representation retained by refinement. -/
def GoodCyclic (σ : Representation ℂ (G i) V) (v : V) : Prop :=
  IsAdmissible (Cyclic.orbitSpan σ v).toRepresentation ∧
    (Cyclic.orbitSpan σ v).toRepresentation.IsIrreducible

/-- A nonzero refinement by a distinct commuting action preserves a good cyclic factor. -/
theorem goodCyclic_of_commuting_refinement
    {i j : ι} (σ : ∀ i, Representation ℂ (G i) V)
    (hcomm : ∀ g h x, σ i h (σ j g x) = σ j g (σ i h x))
    {v w : V} (hv : GoodCyclic (σ j) v)
    (hw : w ∈ Cyclic.orbitSpan (σ i) v) (hw0 : w ≠ 0) :
    GoodCyclic (σ j) w := by
  let := hv.2
  obtain ⟨e, _⟩ := Cyclic.exists_equiv_of_mem_commuting_orbitSpan
    (σ j) v (σ i) hcomm hw hw0
  refine ⟨isAdmissible_of_equiv e hv.1, ?_⟩
  rw [Representation.irreducible_iff_isSimpleModule_asModule]
  exact (LinearMap.isSimpleModule_iff_of_bijective
    (Representation.IntertwiningMap.equivLinearMapAsModule _ _ e.toIntertwiningMap)
    e.bijective).mp
    ((Representation.irreducible_iff_isSimpleModule_asModule _).mp hv.2)

/-- Finitely many cyclic refinements can be made simultaneously inside a
subspace invariant under the refining coordinates. -/
theorem finite_selection
    (σ : ∀ i, Representation ℂ (G i) V)
    (hcomm : ∀ i j, i ≠ j → ∀ g h x, σ i h (σ j g x) = σ j g (σ i h x))
    (E : Finset ι) (P : Submodule ℂ V)
    (hP : ∀ i ∈ E, ∀ g x, x ∈ P → σ i g x ∈ P)
    (hrefine : ∀ i ∈ E, ∀ x ∈ P, x ≠ 0 →
      ∃ y : V, y ∈ Cyclic.orbitSpan (σ i) x ∧ y ≠ 0 ∧ GoodCyclic (σ i) y)
    {v : V} (hv : v ∈ P) (hv0 : v ≠ 0) :
    ∃ w : V, w ∈ P ∧ w ≠ 0 ∧ ∀ i ∈ E, GoodCyclic (σ i) w := by
  classical
  induction E using Finset.induction_on with
  | empty => exact ⟨v, hv, hv0, by simp⟩
  | @insert i S hi ih =>
    obtain ⟨x, hx, hx0, hgood⟩ := ih
      (fun j hj => hP j (Finset.mem_insert_of_mem hj))
      (fun j hj => hrefine j (Finset.mem_insert_of_mem hj))
    obtain ⟨w, hw, hw0, hwi⟩ := hrefine i (Finset.mem_insert_self i S) x hx hx0
    let Q : Subrepresentation (σ i) :=
      { toSubmodule := P
        apply_mem_toSubmodule := fun g x hx => hP i (Finset.mem_insert_self i S) g x hx }
    have hwP : w ∈ P := Cyclic.orbitSpan_le (σ i) x (P := Q) hx hw
    refine ⟨w, hwP, hw0, ?_⟩
    intro j hj
    rcases Finset.mem_insert.mp hj with rfl | hj
    · exact hwi
    · exact goodCyclic_of_commuting_refinement σ
        (hcomm i j (fun hij => hi (hij ▸ hj))) (hgood j hj) hw hw0

end LocalSelection

open RestrictedTensor

variable (H : ∀ i, Subgroup (G i))
  (π : Representation ℂ (RestrictedGroup G H) V)

/-- The vectors fixed by the entire reference tail outside `E`. -/
def tailFixedSubmodule (E : Finset ι) : Submodule ℂ V where
  carrier := {v | ∀ g : RestrictedGroup G H,
    (∀ i ∈ E, g i = 1) → (∀ i ∉ E, g i ∈ H i) → π g v = v}
  zero_mem' := by
    intro g _ _
    exact map_zero (π g)
  add_mem' := by
    intro x y hx hy g hg hgH
    rw [map_add, hx g hg hgH, hy g hg hgH]
  smul_mem' := by
    intro c x hx g hg hgH
    rw [map_smul, hx g hg hgH]

theorem mem_tailFixedSubmodule (E : Finset ι) (v : V) :
    v ∈ tailFixedSubmodule H π E ↔
      ∀ g : RestrictedGroup G H,
        (∀ i ∈ E, g i = 1) → (∀ i ∉ E, g i ∈ H i) → π g v = v :=
  Iff.rfl

/-- Enlarging the exceptional set weakens the fixed-vector condition. -/
theorem tailFixedSubmodule_mono {E F : Finset ι} (hEF : E ⊆ F) :
    tailFixedSubmodule H π E ≤ tailFixedSubmodule H π F := by
  intro v hv g hg hgH
  apply hv g (fun i hi => hg i (hEF hi))
  intro i _
  by_cases hiF : i ∈ F
  · rw [hg i hiF]
    exact (H i).one_mem
  · exact hgH i hiF

/-- A singleton coordinate commutes with every element trivial at that coordinate. -/
theorem single_mul_eq_mul_single [DecidableEq ι] (i : ι) (a : G i)
    (g : RestrictedGroup G H) (hg : g i = 1) :
    RestrictedProduct.mulSingleMonoidHom H i a * g =
      g * RestrictedProduct.mulSingleMonoidHom H i a := by
  ext j
  by_cases hji : j = i
  · subst j
    simp [hg, RestrictedProduct.mulSingleMonoidHom]
  · simp [RestrictedProduct.mulSingleMonoidHom, hji]

/-- Distinct singleton restrictions of an actual restricted-product action commute. -/
theorem single_actions_commute [DecidableEq ι] (i j : ι) (hij : i ≠ j)
    (a : G i) (b : G j) (x : V) :
    π.comp (RestrictedProduct.mulSingleMonoidHom H i) a
        (π.comp (RestrictedProduct.mulSingleMonoidHom H j) b x) =
      π.comp (RestrictedProduct.mulSingleMonoidHom H j) b
        (π.comp (RestrictedProduct.mulSingleMonoidHom H i) a x) := by
  change π _ (π _ x) = π _ (π _ x)
  rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
  rw [single_mul_eq_mul_single H i a _ (by
    exact RestrictedProduct.mulSingle_eq_of_ne H b hij)]

/-- Refinement at an exceptional coordinate preserves full-tail fixedness. -/
theorem single_mem_tailFixedSubmodule [DecidableEq ι] {E : Finset ι}
    {i : ι} (hi : i ∈ E) (a : G i) {x : V}
    (hx : x ∈ tailFixedSubmodule H π E) :
    π.comp (RestrictedProduct.mulSingleMonoidHom H i) a x ∈
      tailFixedSubmodule H π E := by
  intro g hg hgH
  change π g (π _ x) = π _ x
  calc
    π g (π (RestrictedProduct.mulSingleMonoidHom H i a) x) =
        π (RestrictedProduct.mulSingleMonoidHom H i a) (π g x) := by
      rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
      rw [single_mul_eq_mul_single H i a g (hg i hi)]
    _ = _ := congrArg (π (RestrictedProduct.mulSingleMonoidHom H i a)) (hx g hg hgH)

/-- Full-tail invariance implies local reference-subgroup invariance off `E`. -/
theorem mem_fixedVectors_of_mem_tailFixedSubmodule [DecidableEq ι]
    {E : Finset ι} {x : V} (hx : x ∈ tailFixedSubmodule H π E)
    {i : ι} (hi : i ∉ E) :
    x ∈ fixedVectors (π.comp (RestrictedProduct.mulSingleMonoidHom H i)) (H i) := by
  intro a
  apply hx (RestrictedProduct.mulSingleMonoidHom H i (a : G i))
  · intro j hj
    exact RestrictedProduct.mulSingle_eq_of_ne H (a : G i) (by
      intro hji
      exact hi (hji ▸ hj))
  · intro j _
    by_cases hji : j = i
    · subst j
      simpa only [RestrictedProduct.mulSingleMonoidHom_apply,
        RestrictedProduct.mulSingle_eq_same] using a.property
    · change RestrictedProduct.mulSingle H i (a : G i) j ∈ H j
      rw [RestrictedProduct.mulSingle_eq_of_ne H _ hji]
      exact (H j).one_mem

variable [∀ i, TopologicalSpace (G i)]

/-- Conditional assembly of a common cyclic vector from prescribed-vector
refinement and almost-everywhere spherical extraction. -/
theorem select_of_extraction [DecidableEq ι]
    (E₀ : Finset ι) (v : V) (hv0 : v ≠ 0)
    (hv : v ∈ tailFixedSubmodule H π E₀)
    (hrefine : ∀ i x, x ≠ 0 →
      ∃ y : V, y ∈ Cyclic.orbitSpan
          (π.comp (RestrictedProduct.mulSingleMonoidHom H i)) x ∧
        y ≠ 0 ∧ GoodCyclic (π.comp (RestrictedProduct.mulSingleMonoidHom H i)) y)
    (hspherical : ∀ᶠ i in Filter.cofinite, ∀ x : V, x ≠ 0 →
      x ∈ fixedVectors (π.comp (RestrictedProduct.mulSingleMonoidHom H i)) (H i) →
      GoodCyclic (π.comp (RestrictedProduct.mulSingleMonoidHom H i)) x ∧
        Module.finrank ℂ (fixedVectors
          (Cyclic.orbitSpan (π.comp (RestrictedProduct.mulSingleMonoidHom H i)) x).toRepresentation (H i)) = 1) :
    ∃ (E : Finset ι) (w : V), E₀ ⊆ E ∧ w ≠ 0 ∧
      w ∈ tailFixedSubmodule H π E ∧
      (∀ i, GoodCyclic (π.comp (RestrictedProduct.mulSingleMonoidHom H i)) w) ∧
      (∀ i ∉ E,
        w ∈ fixedVectors (π.comp (RestrictedProduct.mulSingleMonoidHom H i)) (H i) ∧
        Module.finrank ℂ (fixedVectors
          (Cyclic.orbitSpan (π.comp (RestrictedProduct.mulSingleMonoidHom H i)) w).toRepresentation (H i)) = 1) := by
  classical
  let P : ι → Prop := fun i => ∀ x : V, x ≠ 0 →
    x ∈ fixedVectors (π.comp (RestrictedProduct.mulSingleMonoidHom H i)) (H i) →
    GoodCyclic (π.comp (RestrictedProduct.mulSingleMonoidHom H i)) x ∧
      Module.finrank ℂ (fixedVectors
        (Cyclic.orbitSpan (π.comp (RestrictedProduct.mulSingleMonoidHom H i)) x).toRepresentation (H i)) = 1
  have hbad : {i | ¬ P i}.Finite := Filter.eventually_cofinite.mp hspherical
  let E := E₀ ∪ hbad.toFinset
  have hE : E₀ ⊆ E := Finset.subset_union_left
  have houtside : ∀ i ∉ E, P i := by
    intro i hi
    by_contra h
    apply hi
    exact Finset.mem_union_right E₀ (by
      simpa only [Set.Finite.mem_toFinset, Set.mem_ofPred_eq] using h)
  obtain ⟨w, hw, hw0, hgood⟩ := finite_selection
    (fun i => π.comp (RestrictedProduct.mulSingleMonoidHom H i))
    (fun i j hij g h x => single_actions_commute H π i j hij h g x)
    E (tailFixedSubmodule H π E)
    (fun i hi g _ hx => single_mem_tailFixedSubmodule H π hi g hx)
    (fun i _ x _ hx0 => hrefine i x hx0)
    (tailFixedSubmodule_mono H π hE hv) hv0
  refine ⟨E, w, hE, hw0, hw, ?_, ?_⟩
  · intro i
    by_cases hi : i ∈ E
    · exact hgood i hi
    · exact (houtside i hi w hw0
        (mem_fixedVectors_of_mem_tailFixedSubmodule H π hw hi)).1
  · intro i hi
    have hfixed := mem_fixedVectors_of_mem_tailFixedSubmodule H π hw hi
    exact ⟨hfixed, (houtside i hi w hw0 hfixed).2⟩

end Langlands.FlathSelection
