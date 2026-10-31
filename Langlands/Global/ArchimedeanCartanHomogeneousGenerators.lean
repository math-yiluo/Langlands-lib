import Langlands.Global.ArchimedeanCartanHomogeneousCovariants
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-! # Finite homogeneous generators of actual compact covariants -/

noncomputable section
universe u
set_option autoImplicit false

namespace Langlands.Global.ArchimedeanGL

variable (K : Type u) [Field K] (n : ℕ)

local instance (τ : ContinuousCompactRep K n) :
    SMul (lieSymmetricGroupInvariants K n) (cartanSymmetricCovariants K n τ) :=
  (cartanSymmetricCovariants_groupInvariantModule K n τ).toSMul

/-- A finite homogeneous generating family for the actual full-group coefficient action. -/
structure HomogeneousCartanCovariantGenerators (τ : ContinuousCompactRep K n) where
  size : ℕ
  degree : Fin size → ℕ
  generator : Fin size → cartanSymmetricCovariants K n τ
  homogeneous : ∀ i, IsHomogeneousCartanCovariant K n τ (degree i) (generator i)
  span_eq_top : Submodule.span (lieSymmetricGroupInvariants K n) (Set.range generator) = ⊤

variable {K n}

/-- Projection selects coefficients in the exact complementary degrees. -/
theorem HomogeneousCartanCovariantGenerators.exists_homogeneous_coefficients
    {τ : ContinuousCompactRep K n} (G : HomogeneousCartanCovariantGenerators K n τ)
    (d : ℕ) (x : cartanSymmetricCovariants K n τ)
    (hx : IsHomogeneousCartanCovariant K n τ d x) :
    ∃ c : Fin G.size → lieSymmetricGroupInvariants K n,
      (∀ i, lieSymmetricComponent K n (d - G.degree i) (c i).val = (c i).val) ∧
      (∀ i, d < G.degree i → c i = 0) ∧
      ∑ i, c i • G.generator i = x := by
  classical
  have hmem : x ∈ Submodule.span (lieSymmetricGroupInvariants K n)
      (Set.range G.generator) := by rw [G.span_eq_top]; trivial
  obtain ⟨a, ha⟩ :=
    (Submodule.mem_span_range_iff_exists_fun (lieSymmetricGroupInvariants K n)).mp hmem
  let c : Fin G.size → lieSymmetricGroupInvariants K n := fun i =>
    if G.degree i ≤ d then lieSymmetricGroupInvariantComponent K n (d - G.degree i) (a i)
    else 0
  refine ⟨c, ?_, ?_, ?_⟩
  · intro i
    dsimp only [c]
    split_ifs
    · exact lieSymmetricGroupInvariantComponent_homogeneous K n _ _
    · exact map_zero _
  · intro i hi
    simp only [c, show ¬ G.degree i ≤ d by omega, ↓reduceIte]
  · have hdx : cartanSymmetricCovariantComponent K n τ d x = x := Subtype.ext hx
    calc
      ∑ i, c i • G.generator i =
          ∑ i, cartanSymmetricCovariantComponent K n τ d (a i • G.generator i) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [cartanSymmetricCovariantComponent_smul_of_homogeneous K n τ d (a i)
          (G.homogeneous i)]
        dsimp only [c]
        split_ifs <;> simp only [zero_smul]
      _ = cartanSymmetricCovariantComponent K n τ d (∑ i, a i • G.generator i) :=
        (map_sum _ _ _).symm
      _ = x := by rw [ha, hdx]

variable (K n)
variable [NumberField K]

/-- Splitting finite generators into their canonical components gives homogeneous generators. -/
theorem nonempty_homogeneousCartanCovariantGenerators (τ : ContinuousCompactRep K n) :
    Nonempty (HomogeneousCartanCovariantGenerators K n τ) := by
  classical
  let := cartanSymmetricCovariants_groupInvariant_moduleFinite K n τ
  obtain ⟨m, g, hg⟩ := Module.Finite.exists_fin
    (R := lieSymmetricGroupInvariants K n) (M := cartanSymmetricCovariants K n τ)
  choose D hz hs using fun i => exists_cartanSymmetricCovariantComponent_bound K n τ (g i)
  let α := (i : Fin m) × Fin (D i + 1)
  let h : α → cartanSymmetricCovariants K n τ := fun a =>
    cartanSymmetricCovariantComponent K n τ a.2.val (g a.1)
  have hspan : Submodule.span (lieSymmetricGroupInvariants K n) (Set.range h) = ⊤ := by
    apply top_unique
    rw [← hg]
    apply Submodule.span_le.mpr
    rintro y ⟨i, rfl⟩
    rw [← hs i]
    apply Submodule.sum_mem
    intro d hd
    exact Submodule.subset_span
      ⟨⟨i, ⟨d, Finset.mem_range.mp hd⟩⟩, rfl⟩
  let e : Fin (Fintype.card α) ≃ α := (Fintype.equivFin α).symm
  refine ⟨⟨Fintype.card α, fun i => (e i).2.val, fun i => h (e i), ?_, ?_⟩⟩
  · intro i
    exact cartanSymmetricCovariantComponent_homogeneous K n τ _ _
  · have hr : Set.range (fun i => h (e i)) = Set.range h := by
      ext y
      constructor
      · rintro ⟨i, rfl⟩
        exact ⟨e i, rfl⟩
      · rintro ⟨a, rfl⟩
        obtain ⟨i, rfl⟩ := e.surjective a
        exact ⟨i, rfl⟩
    rw [hr]
    exact hspan

/-- A choice of actual finite homogeneous generators, with no basis or independence claim. -/
def homogeneousCartanCovariantGenerators (τ : ContinuousCompactRep K n) :
    HomogeneousCartanCovariantGenerators K n τ :=
  Classical.choice (nonempty_homogeneousCartanCovariantGenerators K n τ)

end Langlands.Global.ArchimedeanGL
