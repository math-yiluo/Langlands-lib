import Langlands.GroupScheme.Torus.CentralRigidityLocal
import Langlands.GroupScheme.Torus.CentralRigidityReduction
import Langlands.GroupScheme.HomEqualityOpenLocus
import Langlands.GroupScheme.Torus.MultiplicativeTypeCentralRigidityNoetherianReductionProof
import Langlands.GroupScheme.Torus.MultiplicativeTypeTrivialLocusClosedProof

/-! # Rigidity of central homomorphisms from groups of multiplicative type (SGA 3, IX, 5.1–5.3) -/

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

open RelativeMultiplicativeType CentralRigidityLocal

/-- SGA 3, IX, Théorème 5.1 and Corollaires 5.2–5.3. -/
theorem multiplicativeTypeCentralRigidity : MultiplicativeTypeCentralRigidityStatement.{u} := by
  have hA : ∀ (S : Scheme.{u}) (H G : GroupScheme S), IsLocallyNoetherian S →
      IsMultiplicativeType H → ∀ (u v : H ⟶ G) (s : S),
        (GroupScheme.baseChange (S.fromSpecResidueField s)).map u =
            (GroupScheme.baseChange (S.fromSpecResidueField s)).map v →
        IsCentral ((GroupScheme.baseChange (S.fromSpecResidueField s)).map u) →
        ∃ U : S.Opens, s ∈ U ∧
          (GroupScheme.baseChange U.ι).map u = (GroupScheme.baseChange U.ι).map v :=
    fun S H G hS hH u v s hs hc =>
      exists_open_eq_of_locallyNoetherian S H G hH u v s hs hc
  intro S H G hH hcase
  have h51 : CentralRigidity.LocalCentralEquality H G := by
    intro u v s hs hc
    rcases hcase with hS | ⟨h1, h2, h3⟩
    · exact hA S H G hS hH u v s hs hc
    · exact multiplicativeTypeCentralRigidityNoetherianReduction hA S H G hH h1 h2 h3 u v s hs hc
  have h52 := CentralRigidity.local_triviality_of_local_central_equality h51
  refine ⟨h51, h52, ?_⟩
  intro hsep u
  have hloc : ∀ s : S,
      (GroupScheme.baseChange (S.fromSpecResidueField s)).map u =
          (GroupScheme.baseChange (S.fromSpecResidueField s)).map 0 →
      ∃ W : S.Opens, s ∈ W ∧
        (GroupScheme.baseChange W.ι).map u = (GroupScheme.baseChange W.ι).map 0 := by
    intro s hs
    rw [CentralRigidity.baseChange_map_zero] at hs
    obtain ⟨W, hW, hWu⟩ :=
      h52 u s ((CentralRigidity.hom_eq_one_iff_eq_zero _).2 hs)
    refine ⟨W, hW, ?_⟩
    rw [CentralRigidity.baseChange_map_zero]
    exact (CentralRigidity.hom_eq_one_iff_eq_zero _).1 hWu
  obtain ⟨U, hUmem, hUeq⟩ := HomEqualityOpenLocus.exists_open_fibre_eq_locus u 0 hloc
  have hmem : ∀ s : S, s ∈ U ↔
      ((GroupScheme.baseChange (S.fromSpecResidueField s)).map u).hom.hom = 1 := by
    intro s
    rw [hUmem s, CentralRigidity.hom_eq_one_iff_eq_zero, CentralRigidity.baseChange_map_zero]
  refine ⟨U, ?_, hmem, ?_⟩
  · have hcl := multiplicativeTypeTrivialLocusClosed S H G hH hsep u
    have hset : (U : Set S) =
        {s : S | ((GroupScheme.baseChange (S.fromSpecResidueField s)).map u).hom.hom = 1} := by
      ext s
      exact hmem s
    rw [hset]
    exact hcl
  · rw [CentralRigidity.hom_eq_one_iff_eq_zero, hUeq, CentralRigidity.baseChange_map_zero]

end Langlands.GroupScheme
