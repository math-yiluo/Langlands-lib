import Langlands.Algebra.SandwichDimensionBoundStatement
import Langlands.Algebra.CommutingDimensionPrimary
import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.RingTheory.Adjoin.Basic
import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix

/-! Proof of the sandwich dimension bound using Burnside and the commuting dimension estimate. -/

noncomputable section

namespace Langlands.SandwichDimensionBound

universe uK uH uM

variable (K : Type uK) [Field K] [IsAlgClosed K]
  (H : Type uH) [Ring H] [Algebra K H]
  (M : Type uM) [AddCommGroup M] [Module K M] [Module H M]
  [IsScalarTower K H M] [IsSimpleModule H M] [FiniteDimensional K M]

/-- Every endomorphism of a finite-dimensional simple module is scalar. -/
theorem endomorphism_scalar (f : Module.End H M) :
    ∃ c : K, f = c • (1 : Module.End H M) := by
  have : Nontrivial M := IsSimpleModule.nontrivial H M
  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue (f.restrictScalars K)
  obtain ⟨v, hv⟩ := hc.exists_hasEigenvector
  refine ⟨c, sub_eq_zero.mp ?_⟩
  rcases (f - c • (1 : Module.End H M)).injective_or_eq_zero with hinj | hzero
  · exfalso
    apply hv.2
    apply hinj
    simpa using sub_eq_zero.mpr hv.apply_eq_smul
  · exact hzero

/-- Burnside surjectivity, obtained from Schur and Jacobson density. -/
theorem action_surjective :
    Function.Surjective (Module.toModuleEnd K (S := H) M) := by
  classical
  intro f
  let g : Module.End (Module.End H M) M :=
    { toFun := f
      map_add' := f.map_add
      map_smul' := by
        intro a v
        obtain ⟨c, rfl⟩ := endomorphism_scalar K H M a
        change f (c • v) = c • f v
        exact f.map_smul c v }
  let b := Module.finBasis K M
  obtain ⟨r, hr⟩ := jacobson_density g (Finset.univ.image b)
  refine ⟨r, b.ext fun i => ?_⟩
  exact (hr (b i) (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)).symm

omit [IsAlgClosed K] in
/-- Counting a spanning family obtained by sandwiching a finite basis. -/
theorem finrank_le_sandwich (E : Type*) [Ring E] [Algebra K E]
    (C : Subalgebra K E) [FiniteDimensional K C] (q : ℕ) (x : Fin q → E)
    (hspan : Submodule.span K
      {y : E | ∃ i j, ∃ c ∈ C, y = x i * c * x j} = ⊤) :
    Module.finrank K E ≤ q ^ 2 * Module.finrank K C := by
  classical
  let b := Module.finBasis K C
  let v : Fin q × Fin q × Fin (Module.finrank K C) → E :=
    fun t => x t.1 * (b t.2.2 : E) * x t.2.1
  have hv : Submodule.span K (Set.range v) = ⊤ := by
    apply top_unique
    rw [← hspan]
    refine Submodule.span_le.mpr ?_
    rintro y ⟨i, j, c, hc, rfl⟩
    let L : C →ₗ[K] E := (LinearMap.mulLeftRight K (x i, x j)).comp C.val.toLinearMap
    change L ⟨c, hc⟩ ∈ Submodule.span K (Set.range v)
    rw [← b.sum_repr ⟨c, hc⟩, map_sum]
    apply Submodule.sum_mem
    intro k _
    rw [map_smul]
    apply Submodule.smul_mem
    exact Submodule.subset_span ⟨(i, j, k), rfl⟩
  have h := finrank_le_of_span_eq_top hv
  simpa only [Fintype.card_prod, Fintype.card_fin, pow_two, mul_assoc] using h

omit [IsAlgClosed K] in
/-- A surjective algebra map transports a sandwich spanning condition. -/
theorem sandwich_span_map (E : Type*) [Ring E] [Algebra K E]
    (f : H →ₐ[K] E) (hf : Function.Surjective f)
    (C : Subalgebra K H) (q : ℕ) (x : Fin q → H)
    (hspan : Submodule.span K
      {y : H | ∃ i j, ∃ c ∈ C, y = x i * c * x j} = ⊤) :
    Submodule.span K
      {y : E | ∃ i j, ∃ c ∈ C.map f, y = f (x i) * c * f (x j)} = ⊤ := by
  apply top_unique
  have htop : (Submodule.span K
      {y : H | ∃ i j, ∃ c ∈ C, y = x i * c * x j}).map f.toLinearMap = ⊤ := by
    rw [hspan, Submodule.map_top, LinearMap.range_eq_top.mpr hf]
  rw [← htop]
  apply (Submodule.map_span_le _ _ _).mpr
  rintro y ⟨i, j, c, hc, rfl⟩
  apply Submodule.subset_span
  exact ⟨i, j, f c, Subalgebra.mem_map.mpr ⟨c, hc, rfl⟩, by simp⟩

/-- The action ring homomorphism as an algebra homomorphism. -/
def actionAlgHom : H →ₐ[K] Module.End K M :=
  { Module.toModuleEnd K (S := H) M with
    commutes' := by
      intro c
      ext v
      exact IsScalarTower.algebraMap_smul H c v }

/-- Burnside and the sandwich count bound the dimension squared. -/
theorem dimension_square_le (C : Subalgebra K H) (q : ℕ) (x : Fin q → H)
    (hspan : Submodule.span K
      {y : H | ∃ i j, ∃ c ∈ C, y = x i * c * x j} = ⊤) :
    Module.finrank K M ^ 2 ≤
      q ^ 2 * Module.finrank K (C.map (actionAlgHom K H M)) := by
  let f := actionAlgHom K H M
  have hf : Function.Surjective f := action_surjective K H M
  have hs := sandwich_span_map K H (Module.End K M) f hf C q x hspan
  have hd := finrank_le_sandwich K (Module.End K M) (C.map f) q (fun i => f (x i)) hs
  simpa only [Module.finrank_linearMap, pow_two] using hd

/-- Clear powers and cancel a positive dimension factor. -/
theorem nat_dimension_bound (m q D l : ℕ) (hm : 0 < m)
    (hs : m ^ 2 ≤ q ^ 2 * D)
    (hD : D ^ (2 ^ l) ≤ m ^ (2 ^ (l + 1) - 2)) :
    m ≤ q ^ (2 ^ l) := by
  have he : 2 ≤ 2 ^ (l + 1) := by
    rw [pow_succ]
    have : 1 ≤ 2 ^ l := Nat.one_le_two_pow
    omega
  have hp : m ^ 2 * m ^ (2 ^ (l + 1) - 2) ≤
      (q ^ (2 ^ l)) ^ 2 * m ^ (2 ^ (l + 1) - 2) := calc
    _ = (m ^ 2) ^ (2 ^ l) := by
      rw [← pow_add, ← pow_mul, pow_succ]
      congr 1
      omega
    _ ≤ (q ^ 2 * D) ^ (2 ^ l) := Nat.pow_le_pow_left hs _
    _ = (q ^ (2 ^ l)) ^ 2 * D ^ (2 ^ l) := by
      rw [mul_pow, ← pow_mul, ← pow_mul, Nat.mul_comm 2 (2 ^ l)]
    _ ≤ _ := Nat.mul_le_mul_left _ hD
  have hsquare := Nat.le_of_mul_le_mul_right hp (Nat.pow_pos hm)
  exact (Nat.pow_le_pow_iff_left (by decide : 2 ≠ 0)).mp hsquare

/-- Assemble the sandwich bound from a commuting-endomorphism estimate. -/
theorem bound_of_commuting_estimate
    (hestimate : ∀ (l : ℕ) (a : Fin l → Module.End K M),
      (∀ i j, Commute (a i) (a j)) →
      Module.finrank K (Algebra.adjoin K (Set.range a)) ^ (2 ^ l) ≤
        Module.finrank K M ^ (2 ^ (l + 1) - 2))
    (q l : ℕ) (x : Fin q → H) (a : Fin l → H)
    (hcomm : ∀ i j, Commute (a i) (a j))
    (hspan : Submodule.span K
      {y : H | ∃ i j, ∃ c ∈ Algebra.adjoin K (Set.range a), y = x i * c * x j} = ⊤) :
    Module.finrank K M ≤ q ^ (2 ^ l) := by
  have : Nontrivial M := IsSimpleModule.nontrivial H M
  let f := actionAlgHom K H M
  have hD := hestimate l (fun i => f (a i)) (fun i j => (hcomm i j).map f)
  have hs := dimension_square_le K H M (Algebra.adjoin K (Set.range a)) q x hspan
  rw [AlgHom.map_adjoin, ← Set.range_comp] at hs
  exact nat_dimension_bound (Module.finrank K M) q
    (Module.finrank K (Algebra.adjoin K (Set.range (fun i => f (a i))))) l
    (Module.finrank_pos (R := K) (M := M)) hs hD

end Langlands.SandwichDimensionBound

namespace Langlands

/-- The published sandwich bound, with all quantifiers unchanged. -/
theorem sandwichSimpleModuleDimensionBound.{uH,uM} :
    SandwichSimpleModuleDimensionBoundStatement.{uH,uM} := by
  intro H _ _ q l x a hc hs M _ _ _ _ hsimple hfinite
  let := hsimple
  let := hfinite
  exact SandwichDimensionBound.bound_of_commuting_estimate ℂ H M
    (fun l a hc => CommutingDimension.commuting_dimension_nat ℂ M l a hc)
    q l x a hc hs

end Langlands
