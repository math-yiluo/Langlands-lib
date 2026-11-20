import Langlands.Algebra.ReducedCharpolyRootSplitting
import Langlands.Global.Adelic
import Langlands.Global.Arithmetic.PolynomialRootNeighborhood
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace

/-! # Coefficient neighborhoods of local reduced characteristic polynomials -/

noncomputable section

open Polynomial IntermediateField NumberField
open scoped TensorProduct

universe u

namespace Langlands.Brauer

variable {K : Type u} [Field K] {A : CSA.{u, u} K}

/-- Scalar extension of a split algebra is split. -/
theorem IsSplit.baseChange (h : IsSplit A) (E : Type u) [Field E] [Algebra K E] :
    IsSplit (baseChange E A) := by
  apply (classOf_eq_zero_iff _).mp
  rw [← scalarExtension_classOf, (classOf_eq_zero_iff _).mpr h, map_zero]

/-- A central simple algebra over an algebraically closed field is split. -/
theorem isSplit_of_isAlgClosed [IsAlgClosed K] (A : CSA.{u, u} K) : IsSplit A := by
  obtain ⟨e⟩ := CentralSimple.exists_matrix_chart_reducedDegree K A K
  exact ⟨CentralSimple.reducedDegree K A, CentralSimple.reducedDegree_pos K A,
    ⟨(Algebra.TensorProduct.lid K A).symm.trans e⟩⟩

end Langlands.Brauer

namespace Langlands.CentralSimple

open Langlands.Global.FieldRealization

/-- Monic polynomials of the same degree sufficiently close to `f` are separable, and
every algebraic extension containing any root of such a polynomial splits `A`. -/
def ReducedCharpolySplitNeighborhood {K : Type u} [NormedField K]
    (A : CSA.{u, u} K) (f : K[X]) : Prop :=
  ∃ ε > 0, ∀ (g : K[X]), g.Monic → g.natDegree = f.natDegree →
    (∀ i, ‖g.coeff i - f.coeff i‖ < ε) →
    g.Separable ∧ ∀ (E : Type u) [Field E] [Algebra K E] [Algebra.IsAlgebraic K E]
      (r : E), aeval r g = 0 → Brauer.IsSplit (Brauer.baseChange E A)

section Nonarchimedean

variable {K : Type u} [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K]

/-- Over a complete nonarchimedean field, Krasner root containment gives the
splitting neighborhood for a separable reduced characteristic polynomial. -/
theorem reducedCharpolySplitNeighborhood_nonarchimedean (A : CSA.{u, u} K) (a : A)
    (hs : (reducedCharpoly K A a).Separable) :
    ReducedCharpolySplitNeighborhood A (reducedCharpoly K A a) := by
  let f := reducedCharpoly K A a
  let M := AlgebraicClosure K
  let : NontriviallyNormedField M := spectralNorm.nontriviallyNormedField K M
  let : NormedAlgebra K M := spectralNorm.normedAlgebra K M
  have hd : 0 < f.natDegree := (reducedCharpoly_natDegree K A a).symm ▸ reducedDegree_pos K A
  obtain ⟨ε, hε, h⟩ := exists_coeff_neighborhood_adjoin_le f
    (L := M) (reducedCharpoly_monic K A a) hd hs (IsAlgClosed.splits _)
  refine ⟨ε, hε, fun g hg hdeg hcoeff => ?_⟩
  obtain ⟨hsep, hroot⟩ := h g hg hdeg hcoeff (IsAlgClosed.splits _)
  refine ⟨hsep, fun E _ _ _ r hr => ?_⟩
  let j : E →ₐ[K] M := IsAlgClosed.lift
  have hb : aeval (j r) g = 0 := by rw [aeval_algHom_apply, hr, map_zero]
  obtain ⟨b, hb, hmem⟩ := hroot (j r) hb
  have hh : K⟮j r⟯ ≤ j.fieldRange :=
    IntermediateField.adjoin_simple_le_iff.mpr (AlgHom.mem_fieldRange.mpr ⟨r, rfl⟩)
  obtain ⟨s, rfl⟩ := AlgHom.mem_fieldRange.mp (hh hmem)
  apply isSplit_baseChange_of_isRoot A E a hs s
  change ((f.map (algebraMap K E)).eval s) = 0
  rw [Polynomial.eval_map, ← Polynomial.aeval_def]
  have h : j (aeval s f) = j 0 := by rw [← aeval_algHom_apply j, hb, map_zero]
  exact j.injective h

end Nonarchimedean

/-- The splitting neighborhood at a finite completion uses its actual adic norm. -/
theorem reducedCharpolySplitNeighborhood_finite {F : Type u} [Field F] [NumberField F]
    (v : Langlands.Global.FinitePlace F) (A : CSA.{u, u} (v.adicCompletion F)) (a : A)
    (hs : (reducedCharpoly (v.adicCompletion F) A a).Separable) :
    ReducedCharpolySplitNeighborhood (K := v.adicCompletion F) A
      (reducedCharpoly (v.adicCompletion F) A a) := by
  let K := v.adicCompletion F
  let : NontriviallyNormedField K := Valued.toNontriviallyNormedField K (WithZero (Multiplicative ℤ))
  let : IsUltrametricDist K := IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm
    (Valued.isNonarchimedean_norm K (WithZero (Multiplicative ℤ)))
  exact reducedCharpolySplitNeighborhood_nonarchimedean A a hs

section Infinite

variable {F : Type u} [Field F] (v : InfinitePlace F)

open NumberField.InfinitePlace.Completion

local instance : NormedAlgebra v.Completion ℂ where
  toAlgebra := (extensionEmbedding v).toAlgebra
  norm_smul_le := by
    intro x z
    change ‖extensionEmbedding v x * z‖ ≤ ‖x‖ * ‖z‖
    rw [norm_mul, (isometry_extensionEmbedding v).norm_map_of_map_zero (map_zero _) x]

private theorem surjective_of_value_outside_completion (E : Type u) [Field E]
    [Algebra v.Completion E] (j : E →ₐ[v.Completion] ℂ) (r : E)
    (hr : j r ∉ Set.range (algebraMap v.Completion ℂ)) : Function.Surjective j := by
  have hv : v.IsReal := by
    rw [← InfinitePlace.not_isComplex_iff_isReal]
    exact fun hv => hr (surjective_extensionEmbedding_of_isComplex hv (j r))
  have hK : Set.range (algebraMap v.Completion ℂ) = (Complex.ofRealHom.fieldRange : Set ℂ) := by
    ext z
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨extensionEmbeddingOfIsReal hv x, extensionEmbeddingOfIsReal_apply hv x⟩
    · rintro ⟨x, rfl⟩
      obtain ⟨y, hy⟩ := surjective_extensionEmbeddingOfIsReal hv x
      exact ⟨y, (extensionEmbeddingOfIsReal_apply hv y).symm.trans (congrArg Complex.ofReal hy)⟩
  have hreal (x : ℝ) : algebraMap ℝ ℂ x ∈ j.toRingHom.fieldRange := by
    obtain ⟨y, hy⟩ := hK.symm ▸ (show algebraMap ℝ ℂ x ∈
      (Complex.ofRealHom.fieldRange : Set ℂ) from ⟨x, rfl⟩)
    exact ⟨algebraMap v.Completion E y, (j.commutes y).trans hy⟩
  let S := j.toRingHom.fieldRange.toIntermediateField hreal
  have hclosed : IsClosed (j.toRingHom.fieldRange : Set ℂ) :=
    Submodule.closed_of_finiteDimensional S.toSubalgebra.toSubmodule
  have hne : j.toRingHom.fieldRange ≠ Complex.ofRealHom.fieldRange := by
    intro h
    apply hr
    rw [hK, ← h]
    exact ⟨r, rfl⟩
  exact RingHom.fieldRange_eq_top_iff.mp ((Complex.subfield_eq_of_closed hclosed).resolve_left hne)

/-- At an infinite completion, close polynomials are separable, and in the nonsplit
case their roots stay outside the closed image of the completion in the complex field. -/
theorem reducedCharpolySplitNeighborhood_infinite (A : CSA.{u, u} v.Completion) (a : A)
    (hs : (reducedCharpoly v.Completion A a).Separable) :
    ReducedCharpolySplitNeighborhood A (reducedCharpoly v.Completion A a) := by
  classical
  let K := v.Completion
  let f := reducedCharpoly K A a
  let R := Set.range (algebraMap K ℂ)
  let δ := fun z : ℂ => if z ∈ R then 1 else Metric.infDist z R
  have hR : IsClosed R := isClosed_image_extensionEmbedding v
  have hδ (z : ℂ) : 0 < δ z := by
    dsimp [δ]
    split_ifs with hz
    · exact zero_lt_one
    · exact (hR.notMem_iff_infDist_pos (Set.range_nonempty _)).mp hz
  have hd : 0 < f.natDegree := (reducedCharpoly_natDegree K A a).symm ▸ reducedDegree_pos K A
  obtain ⟨ε, hε, h⟩ := exists_coeff_neighborhood_of_separable f
    (reducedCharpoly_monic K A a) hd hs (IsAlgClosed.splits _) δ (fun z _ => hδ z)
  refine ⟨ε, hε, fun g hg hdeg hcoeff => ?_⟩
  obtain ⟨hsep, hnear⟩ := h g hg hdeg hcoeff (IsAlgClosed.splits _)
  refine ⟨hsep, fun E _ _ _ r hr => ?_⟩
  by_cases hA : Brauer.IsSplit A
  · exact hA.baseChange E
  let j : E →ₐ[K] ℂ := IsAlgClosed.lift
  have hb : aeval (j r) g = 0 := by rw [aeval_algHom_apply, hr, map_zero]
  obtain ⟨b, hb, hdist⟩ := hnear (j r) hb
  have hbR : b ∉ R := by
    rintro ⟨x, rfl⟩
    rw [aeval_algebraMap_apply] at hb
    have hx : IsRoot f x := (algebraMap K ℂ).injective
      (by simpa only [map_zero, Polynomial.aeval_def, Algebra.algebraMap_self, eval₂_id] using hb)
    exact hA (isSplit_of_simple_root A a x
      (le_antisymm (rootMultiplicity_le_one_of_separable hs x)
        ((rootMultiplicity_pos hs.ne_zero).mpr hx)))
  have hjr : j r ∉ R := by
    intro hjr
    have hδb : δ b = Metric.infDist b R := by simp [δ, hbR]
    rw [hδb, ← dist_eq_norm] at hdist
    exact (Metric.infDist_le_dist_of_mem hjr).not_gt hdist
  let e := RingEquiv.ofBijective j.toRingHom
    ⟨j.injective, surjective_of_value_outside_completion v E j r hjr⟩
  let : IsAlgClosed E := ⟨fun p => Polynomial.Splits.of_splits_map
    e.toRingHom (IsAlgClosed.splits _) (fun z _ => e.surjective z)⟩
  exact Brauer.isSplit_of_isAlgClosed (Brauer.baseChange E A)

end Infinite

end Langlands.CentralSimple
