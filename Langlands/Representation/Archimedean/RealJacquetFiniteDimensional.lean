import Langlands.Representation.Archimedean.RealJacquetReduction

/-!
# Finite generation over `U(𝔫)` and the two halves of Casselman's algebraic theorem

For a `(𝔤𝔩_n(ℝ), O(n))`-module `(ρ, π)` on `V`, let `𝔫` be the strictly upper triangular real
matrices and `𝔫V = realJacquetSubspace n π`. The Library's `RealJacquetModuleFiniteStatement`
asks, for irreducible admissible modules, that `V/𝔫V` be finite-dimensional and nonzero
(Wallach 1979, 4.14–4.16). This file splits it into

* `RealJacquetFiniteGenerationStatement`: `V` is finitely generated over `U(𝔫)`, in the form
  "there is a finite-dimensional subspace `F` such that the only subspace containing `F` and
  stable under every `π(1 ⊗ X)`, `X ∈ 𝔫`, is `V`";
* `RealJacquetFiniteDimensionalStatement`: `V/𝔫V` is finite-dimensional;
* `RealJacquetNonvanishingStatement`: `𝔫V ≠ V`;

and proves that finite generation gives finite-dimensionality
(`realJacquetFiniteDimensional_of_finiteGeneration`) and that finite-dimensionality and
nonvanishing together give `RealJacquetModuleFiniteStatement`
(`realJacquetModuleFinite_of_finiteDimensional_of_nonvanishing`).
-/

noncomputable section

open scoped TensorProduct Matrix

set_option autoImplicit false

namespace Langlands.Archimedean

attribute [local instance 100] LieRing.ofAssociativeRing

universe uV

/-- Finite generation of an irreducible admissible `(𝔤𝔩_n(ℝ), O(n))`-module over `U(𝔫)`,
`𝔫` the strictly upper triangular matrices: there is a finite-dimensional subspace `F` of `V`
such that every subspace `S ⊇ F` stable under `π(1 ⊗ X)` for all strictly upper triangular
real `X` is all of `V`. Equivalently `V = U(𝔫) F`. -/
def RealJacquetFiniteGenerationStatement : Prop :=
  ∀ (n : ℕ) (V : Type uV) [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (Matrix.unitaryGroup (Fin n) ℝ) V)
    (π : (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ) →ₗ⁅ℂ⁆ Module.End ℂ V),
    IsRealGKModule n ρ π → IsIrreducibleGKModule ρ π → IsAdmissibleGKModule ρ →
      ∃ F : Submodule ℂ V, FiniteDimensional ℂ F ∧
        ∀ S : Submodule ℂ V, F ≤ S →
          (∀ X : Matrix (Fin n) (Fin n) ℝ, (∀ i j : Fin n, (j : ℕ) ≤ i → X i j = 0) →
            ∀ v ∈ S, π (1 ⊗ₜ X) v ∈ S) →
          S = ⊤

/-- Finite-dimensionality of the real Jacquet module (Wallach 1979, 4.14 (2) and 4.15, for the
upper triangular Borel subalgebra of `𝔤𝔩_n(ℝ)`): for an irreducible admissible
`(𝔤𝔩_n(ℝ), O(n))`-module, `V/𝔫V` is finite-dimensional. -/
def RealJacquetFiniteDimensionalStatement : Prop :=
  ∀ (n : ℕ) (V : Type uV) [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (Matrix.unitaryGroup (Fin n) ℝ) V)
    (π : (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ) →ₗ⁅ℂ⁆ Module.End ℂ V),
    IsRealGKModule n ρ π → IsIrreducibleGKModule ρ π → IsAdmissibleGKModule ρ →
      FiniteDimensional ℂ (V ⧸ realJacquetSubspace n π)

/-- Nonvanishing of the real Jacquet module (Wallach 1979, 4.14 (1), for the upper triangular
Borel subalgebra of `𝔤𝔩_n(ℝ)`): for an irreducible admissible `(𝔤𝔩_n(ℝ), O(n))`-module,
`𝔫V ≠ V`. -/
def RealJacquetNonvanishingStatement : Prop :=
  ∀ (n : ℕ) (V : Type uV) [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (Matrix.unitaryGroup (Fin n) ℝ) V)
    (π : (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ) →ₗ⁅ℂ⁆ Module.End ℂ V),
    IsRealGKModule n ρ π → IsIrreducibleGKModule ρ π → IsAdmissibleGKModule ρ →
      realJacquetSubspace n π ≠ ⊤

/-- If `F` is finite-dimensional and the only `𝔫`-stable subspace containing `F` is `V`, then
`V/𝔫V` is finite-dimensional: `F + 𝔫V` is `𝔫`-stable, hence equal to `V`, so `F` maps onto
`V/𝔫V`. -/
theorem finiteDimensional_quotient_realJacquetSubspace {n : ℕ} {V : Type uV} [AddCommGroup V]
    [Module ℂ V] (π : (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ) →ₗ⁅ℂ⁆ Module.End ℂ V)
    (F : Submodule ℂ V) [FiniteDimensional ℂ F]
    (hF : ∀ S : Submodule ℂ V, F ≤ S →
      (∀ X : Matrix (Fin n) (Fin n) ℝ, (∀ i j : Fin n, (j : ℕ) ≤ i → X i j = 0) →
        ∀ v ∈ S, π (1 ⊗ₜ X) v ∈ S) →
      S = ⊤) :
    FiniteDimensional ℂ (V ⧸ realJacquetSubspace n π) := by
  set N := realJacquetSubspace n π
  have htop : F ⊔ N = ⊤ := hF (F ⊔ N) le_sup_left fun X hX v _ =>
    Submodule.mem_sup_right (mem_realJacquetSubspace (π := π) hX v)
  have hsurj : Function.Surjective (N.mkQ ∘ₗ F.subtype) := by
    intro q
    obtain ⟨v, rfl⟩ := N.mkQ_surjective q
    have hv : v ∈ F ⊔ N := htop ▸ Submodule.mem_top
    obtain ⟨f, hf, m, hm, rfl⟩ := Submodule.mem_sup.1 hv
    refine ⟨⟨f, hf⟩, ?_⟩
    simp [(Submodule.Quotient.mk_eq_zero N).2 hm]
  exact Module.Finite.of_surjective _ hsurj

/-- Finite generation over `U(𝔫)` implies finite-dimensionality of `V/𝔫V`. -/
theorem realJacquetFiniteDimensional_of_finiteGeneration :
    RealJacquetFiniteGenerationStatement.{uV} → RealJacquetFiniteDimensionalStatement.{uV} := by
  intro hfg n V _ _ ρ π hgk hirr hadm
  obtain ⟨F, hFfin, hF⟩ := hfg n V ρ π hgk hirr hadm
  exact finiteDimensional_quotient_realJacquetSubspace π F hF

/-- Finite-dimensionality and nonvanishing of `V/𝔫V` together are the Library's
`RealJacquetModuleFiniteStatement`. -/
theorem realJacquetModuleFinite_of_finiteDimensional_of_nonvanishing :
    RealJacquetFiniteDimensionalStatement.{uV} → RealJacquetNonvanishingStatement.{uV} →
      RealJacquetModuleFiniteStatement.{uV} := by
  intro hfd hnv n V _ _ ρ π hgk hirr hadm
  exact ⟨hfd n V ρ π hgk hirr hadm, hnv n V ρ π hgk hirr hadm⟩

end Langlands.Archimedean
