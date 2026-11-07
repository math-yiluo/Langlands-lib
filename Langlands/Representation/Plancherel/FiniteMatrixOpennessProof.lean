import Langlands.Representation.Plancherel.FiniteMatrixOpennessStatement
import Langlands.Algebra.SandwichDimensionBoundProof
import Mathlib.Algebra.FreeAlgebra
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Matrix.Normed

noncomputable section

namespace Langlands.Plancherel.FiniteMatrixOpenness

open Filter Topology

universe uX uJ uE

variable {X : Type uX} [TopologicalSpace X] {J : Type uJ}
  {E : Type uE} [NormedRing E] [NormedAlgebra ℂ E] [FiniteDimensional ℂ E]

omit [FiniteDimensional ℂ E] in
/-- A fixed noncommutative polynomial in continuous generators is continuous. -/
theorem continuous_lift (A : X → J → E)
    (hA : ∀ j, Continuous (fun x => A x j)) (p : FreeAlgebra ℂ J) :
    Continuous (fun x => FreeAlgebra.lift ℂ (A x) p) := by
  induction p using FreeAlgebra.induction with
  | grade0 c => simpa only [AlgHom.commutes] using
      (continuous_const : Continuous (fun _ : X => algebraMap ℂ E c))
  | grade1 j => simpa only [FreeAlgebra.lift_ι_apply] using hA j
  | add p q hp hq =>
      simp_rw [map_add]
      exact continuous_add.comp (hp.prodMk hq)
  | mul p q hp hq =>
      simp_rw [map_mul]
      exact continuous_mul.comp (hp.prodMk hq)

/-- Generating a finite-dimensional algebra is an open condition. -/
theorem isOpen_adjoin_eq_top (A : X → J → E)
    (hA : ∀ j, Continuous (fun x => A x j)) :
    IsOpen {x | Algebra.adjoin ℂ (Set.range (A x)) = ⊤} := by
  classical
  apply isOpen_iff_mem_nhds.mpr
  intro x₀ hx₀
  have hs : Function.Surjective (FreeAlgebra.lift ℂ (A x₀)) := by
    apply (AlgHom.range_eq_top _).mp
    rwa [← Algebra.adjoin_range_eq_range_freeAlgebra_lift]
  let b := Module.finBasis ℂ E
  choose p hp using fun i => hs (b i)
  let B : X → Fin (Module.finrank ℂ E) → E :=
    fun x i => FreeAlgebra.lift ℂ (A x) (p i)
  have hB : Continuous B := continuous_pi fun i => continuous_lift A hA (p i)
  have h₀ : LinearIndependent ℂ (B x₀) := by
    have heq : B x₀ = b := funext hp
    rw [heq]
    exact b.linearIndependent
  filter_upwards [(hB.tendsto x₀).eventually h₀.eventually] with x hx
  have hspan : Submodule.span ℂ (Set.range (B x)) = ⊤ :=
    hx.span_eq_top_of_card_eq_finrank' (Fintype.card_fin _)
  apply top_unique
  intro y _
  have hy : y ∈ Submodule.span ℂ (Set.range (B x)) := hspan ▸ Submodule.mem_top
  apply (Submodule.span_le.mpr ?_ : Submodule.span ℂ (Set.range (B x)) ≤
    (Algebra.adjoin ℂ (Set.range (A x))).toSubmodule) hy
  rintro z ⟨i, rfl⟩
  rw [Algebra.adjoin_range_eq_range_freeAlgebra_lift]
  exact ⟨p i, rfl⟩

section Endomorphisms

variable {V : Type*} [AddCommGroup V] [Module ℂ V]
  [FiniteDimensional ℂ V] [Nontrivial V]

/-- Burnside identifies irreducibility with generation of the full endomorphism
algebra. -/
theorem adjoin_eq_top_of_irreducible (a : J → Module.End ℂ V)
    (ha : ∀ U : Submodule ℂ V,
      (∀ j v, v ∈ U → a j v ∈ U) → U = ⊥ ∨ U = ⊤) :
    Algebra.adjoin ℂ (Set.range a) = ⊤ := by
  let S := Algebra.adjoin ℂ (Set.range a)
  have : IsSimpleModule S V := by
    refine { eq_bot_or_eq_top := ?_ }
    intro U
    have hU := ha (U.restrictScalars ℂ) (fun j v hv =>
      U.smul_mem (⟨a j, Algebra.subset_adjoin (Set.mem_range_self j)⟩ : S) hv)
    rcases hU with hU | hU
    · left
      exact Submodule.restrictScalars_injective ℂ S V (by simpa using hU)
    · right
      exact Submodule.restrictScalars_injective ℂ S V (by simpa using hU)
  apply top_unique
  intro f _
  obtain ⟨s, hs⟩ := SandwichDimensionBound.action_surjective ℂ S V f
  have heq : (s : Module.End ℂ V) = f := by
    ext v
    exact congrArg (fun g : Module.End ℂ V => g v) hs
  exact heq ▸ s.2

omit [FiniteDimensional ℂ V] [Nontrivial V] in
/-- A subspace invariant under the generators is invariant under their algebra. -/
theorem invariant_adjoin (a : J → Module.End ℂ V) (U : Submodule ℂ V)
    (hU : ∀ j v, v ∈ U → a j v ∈ U) {f : Module.End ℂ V}
    (hf : f ∈ Algebra.adjoin ℂ (Set.range a)) :
    ∀ v ∈ U, f v ∈ U := by
  induction hf using Algebra.adjoin_induction with
  | mem f hf =>
      obtain ⟨j, rfl⟩ := hf
      exact hU j
  | algebraMap c =>
      intro v hv
      exact U.smul_mem c hv
  | add f g hf hg hif hig =>
      intro v hv
      exact U.add_mem (hif v hv) (hig v hv)
  | mul f g hf hg hif hig =>
      intro v hv
      exact hif (g v) (hig v hv)

omit [FiniteDimensional ℂ V] in
/-- Full endomorphism generation forces irreducibility. -/
theorem irreducible_of_adjoin_eq_top (a : J → Module.End ℂ V)
    (ha : Algebra.adjoin ℂ (Set.range a) = ⊤)
    (U : Submodule ℂ V) (hU : ∀ j v, v ∈ U → a j v ∈ U) :
    U = ⊥ ∨ U = ⊤ := by
  let W : Submodule (Module.End ℂ V) V :=
    { U with
      smul_mem' := fun f v hv => invariant_adjoin a U hU (ha ▸ trivial) v hv }
  rcases eq_bot_or_eq_top W with h | h
  · left
    exact Submodule.ext fun v => SetLike.ext_iff.mp h v
  · right
    exact Submodule.ext fun v => SetLike.ext_iff.mp h v

end Endomorphisms

section Matrices

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The published invariant-subspace predicate is exactly full matrix-algebra
generation, including the zero-dimensional case. -/
theorem matrix_irreducible_iff_adjoin_eq_top (A : J → Matrix n n ℂ) :
    UnitarizabilityContinuation.IsIrreducibleFamily A ↔
      Algebra.adjoin ℂ (Set.range A) = ⊤ := by
  classical
  cases isEmpty_or_nonempty n with
  | inl hn =>
      constructor
      · intro _
        exact Subsingleton.elim _ _
      · intro _ U _
        exact Or.inl (Subsingleton.elim _ _)
  | inr hn =>
      let e : Matrix n n ℂ ≃ₐ[ℂ] Module.End ℂ (n → ℂ) := Matrix.toLinAlgEquiv'
      let a : J → Module.End ℂ (n → ℂ) := fun j => e (A j)
      have hm : (Algebra.adjoin ℂ (Set.range A)).map e.toAlgHom =
          Algebra.adjoin ℂ (Set.range a) := by
        rw [AlgHom.map_adjoin, ← Set.range_comp]
        rfl
      have ht : (⊤ : Subalgebra ℂ (Matrix n n ℂ)).map e.toAlgHom = ⊤ := by
        rw [Algebra.map_top, (AlgHom.range_eq_top _).mpr e.surjective]
      constructor
      · intro hA
        have ha : Algebra.adjoin ℂ (Set.range a) = ⊤ :=
          adjoin_eq_top_of_irreducible a
            (by simpa [a, e, UnitarizabilityContinuation.IsIrreducibleFamily] using hA)
        apply Subalgebra.map_injective (f := e.toAlgHom) e.injective
        rw [hm, ht, ha]
      · intro hA
        have ha : Algebra.adjoin ℂ (Set.range a) = ⊤ := by rw [← hm, hA, ht]
        intro U hU
        exact irreducible_of_adjoin_eq_top a ha U (by simpa [a, e] using hU)

end Matrices

end Langlands.Plancherel.FiniteMatrixOpenness

namespace Langlands.Plancherel

open scoped Matrix.Norms.Operator

/-- The exact finite matrix openness proposition. -/
theorem finiteMatrixIrreducibilityOpenness.{uX,uJ,un} :
    FiniteMatrixIrreducibilityOpennessStatement.{uX,uJ,un} := by
  classical
  intro X _ J n _ A hA
  simp_rw [FiniteMatrixOpenness.matrix_irreducible_iff_adjoin_eq_top]
  exact FiniteMatrixOpenness.isOpen_adjoin_eq_top A (fun j => continuous_matrix (hA j))

end Langlands.Plancherel
