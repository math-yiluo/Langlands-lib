import Langlands.Cohomology.SupercuspidalExtCharZero.Statement
import Langlands.Cohomology.SupercuspidalExtCharZero.InjectiveProjectiveProof
import Langlands.Cohomology.SupercuspidalExt.ReciprocityProof
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.Topology.Algebra.OpenSubgroup
import Mathlib.Topology.Compactness.SigmaCompact

/-!
# Higher Ext vanishing from compact induction

The open-subgroup topology and measure lemmas discharge all geometric
hypotheses needed to apply compact-coefficient injectivity on an open subgroup.
The conditional theorem combines finite biproducts of injectives with
Ext reciprocity. The final theorem discharges its premise using
`compactCoefficientInjectiveProjective`.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits MeasureTheory

namespace Langlands.Cohomology.SupercuspidalExtCharZero

open Langlands.Cohomology.SupercuspidalExt (restriction compactInduction)

universe u

section OpenSubgroup

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

omit [IsTopologicalGroup G] in
/-- An open subgroup of a locally compact group is locally compact in the
induced topology. -/
theorem openSubgroup_locallyCompactSpace [LocallyCompactSpace G]
    (H : Subgroup G) (hH : IsOpen (H : Set G)) : LocallyCompactSpace H :=
  hH.locallyCompactSpace

/-- An open subgroup is closed, so inherits sigma compactness. -/
theorem openSubgroup_sigmaCompactSpace [SigmaCompactSpace G]
    (H : Subgroup G) (hH : IsOpen (H : Set G)) : SigmaCompactSpace H :=
  (H.isClosed_of_isOpen hH).sigmaCompactSpace

variable [MeasurableSpace G] [BorelSpace G]

/-- Pulling Haar measure back along an open subgroup inclusion is Haar measure. -/
theorem openSubgroup_isHaarMeasure (μ : Measure G) [μ.IsHaarMeasure]
    (H : Subgroup G) (hH : IsOpen (H : Set G)) :
    (μ.comap H.subtype).IsHaarMeasure :=
  Measure.IsHaarMeasure.comap (mH := inferInstance) μ hH.isOpenEmbedding_subtypeVal

omit [IsTopologicalGroup G] in
/-- Regularity passes to the measure on an open subgroup. -/
theorem openSubgroup_regular (μ : Measure G) [μ.Regular]
    (H : Subgroup G) (hH : IsOpen (H : Set G)) :
    (μ.comap H.subtype).Regular :=
  Measure.Regular.comap' μ hH.isOpenEmbedding_subtypeVal

/-- Right invariance passes to the measure on an open subgroup. -/
theorem openSubgroup_isMulRightInvariant (μ : Measure G) [μ.IsMulRightInvariant]
    (H : Subgroup G) (hH : IsOpen (H : Set G)) :
    (μ.comap H.subtype).IsMulRightInvariant :=
  Measure.IsMulRightInvariant.comap μ hH.isOpenEmbedding_subtypeVal.measurableEmbedding

end OpenSubgroup

attribute [local instance] Abelian.hasFiniteBiproducts

/-- Compact-coefficient injectivity on each open subgroup implies higher Ext
vanishing from compact induction. The subgroup uses its induced topology and
the pullback of the ambient two-sided regular Haar measure. -/
theorem compactInductionSupercuspidalExtVanishing_of_openSubgroup
    (k : Type u) [Field k] [CharZero k]
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G]
    [SigmaCompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsHaarMeasure] [μ.Regular] [μ.IsMulRightInvariant]
    (hcompact : ∀ (H : Subgroup G) (hH : IsOpen (H : Set G)),
      letI : LocallyCompactSpace H := openSubgroup_locallyCompactSpace H hH
      letI : SigmaCompactSpace H := openSubgroup_sigmaCompactSpace H hH
      letI : (μ.comap H.subtype).IsHaarMeasure := openSubgroup_isHaarMeasure μ H hH
      letI : (μ.comap H.subtype).Regular := openSubgroup_regular μ H hH
      letI : (μ.comap H.subtype).IsMulRightInvariant :=
        openSubgroup_isMulRightInvariant μ H hH
      CompactCoefficientInjectiveProjectiveStatement k H (μ.comap H.subtype)) :
    CompactInductionSupercuspidalExtVanishingStatement k G μ := by
  intro H hH π ι _ σ hirr hcoeff hiso V n
  have : LocallyCompactSpace H := openSubgroup_locallyCompactSpace H hH
  have : SigmaCompactSpace H := openSubgroup_sigmaCompactSpace H hH
  have : (μ.comap H.subtype).IsHaarMeasure := openSubgroup_isHaarMeasure μ H hH
  have : (μ.comap H.subtype).Regular := openSubgroup_regular μ H hH
  have : (μ.comap H.subtype).IsMulRightInvariant :=
    openSubgroup_isMulRightInvariant μ H hH
  have : ∀ i, Injective (σ i) :=
    fun i => (hcompact H hH (σ i) (hirr i) (hcoeff i)).1
  obtain ⟨e⟩ := hiso
  have : Injective ((restriction k G H).obj π) :=
    Injective.of_iso e.symm inferInstance
  obtain ⟨reciprocity⟩ :=
    SupercuspidalExt.compactInductionExtReciprocity k G H hH V (n + 1)
  exact (SmoothExt.isZero_ext_succ_of_injective k H V
    ((restriction k G H).obj π) n).of_iso (reciprocity.app π)

/-- Higher Ext from compact induction vanishes when the restricted target is a
finite biproduct of irreducible representations with compact coefficients over
a field of characteristic zero. -/
theorem compactInductionSupercuspidalExtVanishing
    (k : Type u) [Field k] [CharZero k]
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G]
    [SigmaCompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsHaarMeasure] [μ.Regular] [μ.IsMulRightInvariant] :
    CompactInductionSupercuspidalExtVanishingStatement k G μ := by
  apply compactInductionSupercuspidalExtVanishing_of_openSubgroup k G μ
  intro H hH
  have : LocallyCompactSpace H := openSubgroup_locallyCompactSpace H hH
  have : SigmaCompactSpace H := openSubgroup_sigmaCompactSpace H hH
  have : (μ.comap H.subtype).IsHaarMeasure := openSubgroup_isHaarMeasure μ H hH
  have : (μ.comap H.subtype).Regular := openSubgroup_regular μ H hH
  have : (μ.comap H.subtype).IsMulRightInvariant :=
    openSubgroup_isMulRightInvariant μ H hH
  exact compactCoefficientInjectiveProjective k H (μ.comap H.subtype)

end Langlands.Cohomology.SupercuspidalExtCharZero
