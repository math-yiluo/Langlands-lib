import Langlands.Representation.CompactCoefficient.NormalSubgroupDecomposition
import Langlands.Representation.CompactCoefficient.Subquotients
import Langlands.Representation.Category.ComplementaryCoproduct
import Langlands.Representation.CuspidalSupport.RationalWholeCuspidalOrthogonality

/-!
# Conditional category decomposition by compact restriction

The factors test arbitrary actual subquotients. The analytic complement and
fixed-stratum hypotheses remain explicit in this intermediate construction.
-/

noncomputable section

namespace Langlands

universe uG uV

namespace SmoothRep

variable {G : Type uG} [Group G] [TopologicalSpace G]

/-- The all/no arbitrary-subquotient factors for compact coefficients on the
actual subgroup restriction. The all-subquotient factor is indexed by `true`. -/
def compactRestrictionSubquotientProperties (N : Subgroup G) :
    Bool → CategoryTheory.ObjectProperty (SmoothRep.{0, uG, uV} ℂ G) :=
  subquotientProperties (compactRestrictionProperty N)

/-- The actual nonzero-image argument applies to compact restriction without
any analytic splitting or compact-open hypothesis. -/
theorem compactRestrictionSubquotientProperties_offDiagonalHomsZero
    (N : Subgroup G) :
    Renard.OffDiagonalHomsZero
      (compactRestrictionSubquotientProperties.{uG, uV} N) :=
  subquotientProperties_offDiagonalHomsZero _

end SmoothRep

namespace CompactCoefficientClass

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (N : Subgroup G) [N.Normal]
  [NonarchimedeanGroup N] [WeaklyLocallyCompactSpace N]
  (hsplit : ∀ (c : CompactCoefficientClass.{uG, uV} N)
    (D : SmoothRep.{0, uG, uV} ℂ N),
    IsCompl (isotypicSubrepresentation c D).toSubmodule
      (annihilatorSubrepresentation c D).toSubmodule)
  (hstrata : ∀ K : OpenSubgroup N, IsCompact (K : Set N) →
    (fixedStratum.{uG, uV} K.toSubgroup).Finite)

include hsplit hstrata in
/-- The conditional normal-subgroup splitting gives the actual A.IX category
decomposition for the all/no arbitrary-subquotient compact-restriction factors.
All four analytic inputs of the underlying splitting remain explicit. -/
theorem categoryDecomposition_of_normalSubgroup_compactCoefficients
    (hcompact : ∀ D : SmoothRep.{0, uG, uV} ℂ N,
      HasCompactSmoothDualCoefficients
        (totalIsotypicSubrepresentation.{uG, uV} D).toRepresentation)
    (hexhaust : ∀ D : SmoothRep.{0, uG, uV} ℂ N,
      HasCompactSmoothDualCoefficients D.representation →
        totalIsotypicSubrepresentation.{uG, uV} D = ⊤) :
    Renard.IsCategoryDecomposition
      (SmoothRep.compactRestrictionSubquotientProperties.{uG, uV} N) := by
  have hcof : ∀ K : OpenSubgroup N,
      ∃ L : OpenSubgroup N, IsCompact (L : Set N) ∧ L ≤ K := by
    intro K
    exact compactOpenSubgroupBasis N K
      (K.isOpen.mem_nhds (K.one_mem))
  refine ⟨?_, SmoothRep.compactRestrictionSubquotientProperties_offDiagonalHomsZero N⟩
  intro A
  obtain ⟨S, Q, hSQ, hS, hQ⟩ :=
    decomposition_of_normalSubgroup_compactCoefficients
      N hsplit hstrata hcompact hexhaust A
  apply SmoothRep.isCoproductOfComponents_of_isCompl _ A S Q hSQ
  · intro D hDS
    exact SmoothRep.compactRestrictionProperty_of_isSubquotient N hcof hS hDS
  · intro D hD hDQ hcompactD
    exact (not_nontrivial_iff_subsingleton.mpr (hQ D hDQ hcompactD)) hD

include hsplit hstrata in
/-- Published total compactness and exhaustion discharge the corresponding
two analytic inputs under their actual topological and left-Haar hypotheses.
Intrinsic complements and fixed-stratum finiteness are still inputs. -/
theorem categoryDecomposition_of_normalSubgroup_totalCompactness
    [T2Space N] [LocallyCompactSpace N] [TotallyDisconnectedSpace N]
    [MeasurableSpace N] [BorelSpace N]
    (μ : MeasureTheory.Measure N) [μ.IsHaarMeasure] :
    Renard.IsCategoryDecomposition
      (SmoothRep.compactRestrictionSubquotientProperties.{uG, uV} N) := by
  have hcof : ∀ K : OpenSubgroup N,
      ∃ L : OpenSubgroup N, IsCompact (L : Set N) ∧ L ≤ K := by
    intro K
    exact compactOpenSubgroupBasis N K
      (K.isOpen.mem_nhds (K.one_mem))
  exact categoryDecomposition_of_normalSubgroup_compactCoefficients
    N hsplit hstrata
    (fun D => totalIsotypicSubrepresentation_hasCompactSmoothDualCoefficients hcof D)
    (fun D hD => totalIsotypicSubrepresentation_eq_top_of_compactCoefficients μ D hD)

end CompactCoefficientClass
end Langlands
