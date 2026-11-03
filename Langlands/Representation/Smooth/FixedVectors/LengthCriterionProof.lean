import Langlands.Representation.Smooth.FixedVectors.LengthCriterionStatement
import Langlands.Representation.Filtration.LengthCriterionProof
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.RingTheory.Finiteness.Basic

/-! Elementary generator and strict-chain proofs for fixed-vector length reduction. -/

set_option autoImplicit false

noncomputable section

namespace Langlands

universe uR uG uV

section Generators

variable {R : Type uR} [CommRing R] {G : Type uG} [Group G]
  {V : Type uV} [AddCommGroup V] [Module R V]

/-- A generating family contained in the fixed vectors forces generation by
those fixed vectors. -/
theorem eq_top_of_fixedVectors_le_of_generators
    (ρ : Representation R G V) (L : Subgroup G)
    {n : ℕ} (v : Fin n → V)
    (hgen : Submodule.span (MonoidAlgebra R G)
      (Set.range (fun i => ρ.asModuleEquiv.symm (v i))) = ⊤)
    (hfix : ∀ i, v i ∈ fixedVectors ρ L)
    (S : Subrepresentation ρ) (hS : fixedVectors ρ L ≤ S.toSubmodule) :
    S = ⊤ := by
  have hspan : Submodule.span (MonoidAlgebra R G)
      (Set.range (fun i => ρ.asModuleEquiv.symm (v i))) ≤ S.asSubmodule := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact hS (hfix i)
  rw [hgen] at hspan
  apply Subrepresentation.subrepresentationSubmoduleOrderIso.injective
  exact top_unique hspan

/-- Smooth generators have a common open stabilizer, and remain fixed after
passing to any smaller subgroup. -/
theorem commonFixedGenerators : CommonFixedGeneratorsStatement.{uR, uG, uV} := by
  classical
  intro R _ G _ _ V _ _ ρ hρ hfin
  let := hfin
  obtain ⟨n, w, hw⟩ :=
    Module.Finite.exists_fin (R := MonoidAlgebra R G) (M := ρ.asModule)
  let v : Fin n → V := fun i => ρ.asModuleEquiv (w i)
  choose U hU using fun i => hρ (v i)
  let K : OpenSubgroup G := Finset.univ.inf U
  have hKU (i : Fin n) : K ≤ U i := Finset.inf_le (Finset.mem_univ i)
  have hfix (L : Subgroup G) (hL : L ≤ K.toSubgroup) (i : Fin n) :
      v i ∈ fixedVectors ρ L := by
    intro g
    exact hU i ⟨g, hKU i (hL g.property)⟩
  have hgen : Submodule.span (MonoidAlgebra R G)
      (Set.range (fun i => ρ.asModuleEquiv.symm (v i))) = ⊤ := hw
  refine ⟨n, v, K, hgen, hfix K.toSubgroup le_rfl, ?_⟩
  intro L hL S hS
  exact eq_top_of_fixedVectors_le_of_generators ρ L v hgen (hfix L hL) S hS

end Generators

/-- Fixed-vector detection makes the dimensions of intersections strictly
increase, bounding every finite strict chain of invariant subspaces. -/
theorem fixedVectorsStrictInclusionLength :
    FixedVectorsStrictInclusionLengthStatement.{uR, uG, uV} := by
  intro R _ G _ V _ _ ρ K _ hdetect
  let U : Subrepresentation ρ → Submodule R (fixedVectors ρ K) :=
    fun S => S.toSubmodule.comap (fixedVectors ρ K).subtype
  have hU : StrictMono U := by
    intro S T hST
    refine lt_of_le_not_ge (Submodule.comap_mono hST.le) ?_
    intro hTS
    obtain ⟨v, hvT, hvK, hvS⟩ := hdetect S T hST
    exact hvS (hTS (show (⟨v, hvK⟩ : fixedVectors ρ K) ∈ U T from hvT))
  let measure : Subrepresentation ρ → ℕ := fun S => Module.finrank R (U S)
  have hmeasure : StrictMono measure := Submodule.finrank_strictMono.comp hU
  have hbound (S : Subrepresentation ρ) :
      measure S ≤ Module.finrank R (fixedVectors ρ K) := Submodule.finrank_le _
  have hchain (m : ℕ) (c : Fin (m + 1) → Subrepresentation ρ)
      (hc : StrictMono c) : m ≤ Module.finrank R (fixedVectors ρ K) := by
    let q := LTSeries.mk m (fun i => measure (c i)) (hmeasure.comp hc)
    have h := q.head_add_length_le_nat
    have hb := hbound (c (Fin.last m))
    change measure (c 0) + m ≤ measure (c (Fin.last m)) at h
    omega
  have hcomp := LengthCriterionProof.hasCompositionLengthAtMost_of_bound
    (A := Rep.of ρ) hchain
  exact ⟨hcomp, (objectCompositionLengthCriterion R G (Rep.of ρ)
    (Module.finrank R (fixedVectors ρ K))).2 hcomp⟩

/-- The two elementary reductions used before the reductive-group detection
step in Howe's implication. -/
theorem fixedVectorLengthReduction :
    FixedVectorLengthReductionStatement.{uR, uG, uV} :=
  ⟨commonFixedGenerators, fixedVectorsStrictInclusionLength⟩

end Langlands
