import Langlands.Representation.CuspidalSupport.CuspidalTensorJacquetQuotientStatement
import Langlands.Representation.CuspidalSupport.QuasicuspidalEmbeddingProof
import Langlands.Representation.CuspidalSupport.QuasicuspidalLeviAdmissibilityProof
import Langlands.Representation.CuspidalSupport.LeviTensorFactorizationProof

/-! Actual tensor realization by retaining an irreducible Jacquet quotient. -/

noncomputable section

namespace Langlands.CuspidalSupport

open GeneralLinear QuasicuspidalEmbedding

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

/-- Actual external supercuspidal tensor quotients exist without analytic
hypotheses on the irreducible smooth input. -/
theorem cuspidalTensorJacquetQuotientExistence :
    CuspidalTensorJacquetQuotientExistence.{uF, uV} F T := by
  classical
  let := T.topology
  intro n hn π hπ
  let := T.generalLinearTopologicalGroup n
  have hπne : Nontrivial π :=
    QuasicuspidalEmbedding.nontrivial_of_isIrreducible π.representation hπ
  obtain ⟨B, hJne, hJq⟩ := minimalNonzeroJacquet p F T n π hπne
  let J := (T.normalizedJacquetFunctor B).obj π
  have : CompactSpace (Induction.LeftQuotient (B.parabolic F.Carrier)) :=
    Parabolic.parabolicQuotientCompact F T B
  obtain ⟨v₀, hv₀⟩ := exists_ne (0 : π)
  obtain ⟨s, hs⟩ := exists_finset_generating T B π.isSmooth v₀
    (mem_span_orbit π.representation hπ hv₀)
  have : Nontrivial J := hJne
  obtain ⟨S, hS⟩ := exists_isCoatom_subrepresentation J.representation s hs
  let σ := SmoothRep.quotient J S
  let q : J.representation.IntertwiningMap σ.representation :=
    SmoothRep.hom (SmoothRep.mkQ J S)
  have hq : Function.Surjective q := SmoothRep.mkQ_surjective J S
  have hqker : ∀ x, q x = 0 ↔ x ∈ S := fun x => Submodule.Quotient.mk_eq_zero _
  have hσ : σ.IsIrreducible := isIrreducible_of_isCoatom q hq S hS hqker
  have hσq : IsLeviQuasicuspidal B σ.representation := fun R hR =>
    coinvariants_subsingleton_of_surjective q hq _ (hJq R hR)
  have hσa : σ.IsAdmissible :=
    LeviAdmissibility.irreducibleQuasicuspidalLeviAdmissibility F T B σ hσ hσq
  obtain ⟨C, ⟨e⟩⟩ := padicLeviCuspidalFactorization.{uF, max uF uV, max uF uV}
    p F T n hn B σ hσ ⟨hσa, hσq⟩
  refine ⟨B, C, SmoothRep.ofHom (e.toIntertwiningMap.comp q), ?_⟩
  exact e.surjective.comp hq

end Langlands.CuspidalSupport
