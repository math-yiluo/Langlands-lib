import Langlands.Representation.CuspidalSupport.ConstituentFiniteTypes
import Langlands.Representation.CuspidalSupport.ConstituentComplement
import Langlands.Representation.CompactCoefficient.SelectedAssembly
import Langlands.Representation.CompactCoefficient.AdmissibleComplement
import Langlands.Representation.Category.FiniteIndexRestriction
import Langlands.Representation.Filtration.CoarseJacquetFactorization
import Langlands.Representation.Smooth.Schur.Proof
import Langlands.Representation.Smooth.Admissibility.EmbeddingProof
import Langlands.Topology.CompactOpen.NeighborhoodBasis
import Mathlib.Topology.Algebra.Nonarchimedean.TotallyDisconnected
import Mathlib.MeasureTheory.Measure.Haar.Basic

/-! # Realization of a constituent with compact restriction to an open normal subgroup

Generic form of the argument of Renard VI.3.6: let `H` be an open normal subgroup
of a locally profinite group `G` whose join with the centre has finite index. An
irreducible actual subquotient of an admissible representation whose restriction
to `H` has compactly supported smooth-dual coefficients is both a
subrepresentation and a quotient.
-/

noncomputable section

namespace Langlands.CuspidalSupport

open SmoothRep CompactCoefficientClass

universe uG uV

variable {G : Type uG} [Group G] [TopologicalSpace G] [NonarchimedeanGroup G]
  [T2Space G] [LocallyCompactSpace G]

omit [T2Space G] in
/-- Compact open subgroups are cofinal among open subgroups. -/
theorem exists_compact_openSubgroup_le (U : OpenSubgroup G) :
    ∃ K : OpenSubgroup G, IsCompact (K : Set G) ∧ K ≤ U := by
  obtain ⟨K, hK, hKU⟩ := compactOpenSubgroupBasis G (U : Set G) U.mem_nhds_one
  exact ⟨K, hK, fun _ hg => hKU hg⟩

/-- An irreducible actual subquotient of an admissible representation, whose
restriction to an open normal subgroup `H` with `H ⊔ center G` of finite index
has compactly supported smooth-dual coefficients, is both an actual
subrepresentation and an actual quotient. -/
theorem constituent_of_compactRestriction
    (H : OpenSubgroup G) [H.toSubgroup.Normal]
    [(H.toSubgroup ⊔ Subgroup.center G).FiniteIndex]
    (A D : SmoothRep.{0, uG, uV} ℂ G) (hAa : A.IsAdmissible) (hDi : D.IsIrreducible)
    (hDc : HasCompactSmoothDualCoefficients
      (SmoothRep.restrictSubgroup H.toSubgroup D).representation)
    (hDA : IsSubquotient D A) :
    IsSubrepresentation D A ∧ IsQuotient D A := by
  let N := H.toSubgroup
  have hDa : D.IsAdmissible :=
    isAdmissible_of_subquotient_of_compactOpenCofinal exists_compact_openSubgroup_le hAa hDA
  obtain ⟨χ, ⟨_, hχ⟩, _⟩ := admissibleSchur_centralCharacter D.representation hDa hDi
  obtain ⟨_, m, V, hV, hspan⟩ :=
    FiniteIndexRestriction.finite_irreducible_restriction D.representation N hDi
      (fun z => ⟨χ z, hχ z⟩)
  let : LocallyCompactSpace N := H.isOpen.locallyCompactSpace
  let : MeasurableSpace N := borel N
  let : BorelSpace N := ⟨rfl⟩
  let μ : MeasureTheory.Measure N := MeasureTheory.Measure.haar
  have hcof : ∀ K : OpenSubgroup N, ∃ L : OpenSubgroup N,
      IsCompact (L : Set N) ∧ L ≤ K := by
    intro K
    obtain ⟨L, hLK, hL, _⟩ := Hecke.TestFunction.commonCompactOpenBiInvariance N ∅ K
    exact ⟨L, hL, hLK⟩
  have hsplit :
      ∀ (c : CompactCoefficientClass.{uG, uV} N) (X : SmoothRep.{0, uG, uV} ℂ N),
        IsCompl (isotypicSubrepresentation c X).toSubmodule
          (annihilatorSubrepresentation c X).toSubmodule :=
    CompactSplitting.isCompl_isotypicSubrepresentation_annihilatorSubrepresentation μ hcof
  obtain ⟨_, S, Q, hSQ, hS, htypes, hQ⟩ :=
    finiteFamilyBlockIsolation_of_isCompl N μ hsplit A D hDi hDc V hV hspan
  have hDS := irreducibleSubquotient_of_isCompl S Q hSQ hDi hDA hQ
  have hSa : (subrepresentation A S).IsAdmissible :=
    isAdmissible_of_injective (hom (subtype A S)) (subtype_injective A S) hAa
  have hVne (i : Fin m) : V i ≠ ⊥ := by
    let := hV i
    let : Nontrivial (V i).toSubmodule :=
      IsSimpleModule.nontrivial (MonoidAlgebra ℂ N) (V i).toRepresentation.asModule
    obtain ⟨v, hv⟩ := exists_ne (0 : (V i).toSubmodule)
    intro heq
    have hz : (v : D) ∈ (⊥ : Subrepresentation (D.representation.comp N.subtype)) :=
      heq ▸ v.property
    exact hv (Subtype.ext hz)
  have hSD : IsSubrepresentation D (subrepresentation A S) ∧
      IsQuotient D (subrepresentation A S) := by
    apply constituent_of_finite_types H (subrepresentation A S) D hSa hS hDa hDi V hVne
    · intro W hW
      obtain ⟨i, ⟨e⟩⟩ := htypes W
        (FiniteIndexRestriction.isIrreducible_toRepresentation_of_isAtom W hW)
      exact ⟨i, ⟨e.symm⟩⟩
    · exact hDS
  exact constituent_of_isCompl S Q hSQ hSD

end Langlands.CuspidalSupport
