import Langlands.Geometry.Analytic.RationalSpectrumAtlas
import Langlands.Geometry.Analytic.AffinoidSpectrumAtlas
import Langlands.Geometry.Analytic.AtlasReindexing
import Langlands.Geometry.Analytic.GeneralizedAffinoid.DomainBaseTransport

/-! # Full strong comparison of rational and singleton spectrum atlases -/

noncomputable section

universe u

namespace Langlands.Analytic.RationalSpectrumAtlas

open CategoryTheory Set Topology
open PresentedAffinoidAlgebra AffinoidAtlasPresentation

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

/-- The actual rational atlas, bundled on the original spectrum. -/
def presentation (A : PresentedAffinoidAlgebra K) :
    AffinoidAtlasPresentation.{u, u, u} K where
  space := TopCat.of (BanachSpectrum A)
  atlas := atlas A

/-- Move the singleton's index universe while keeping its unique chart. -/
def singletonIndexEquiv (A : PresentedAffinoidAlgebra K) :
    PUnit.{u+1} ≃ (PresentedAffinoidSpace.atlasPresentation (Opposite.op A)).atlas.Index where
  toFun _ := PUnit.unit
  invFun _ := PUnit.unit
  left_inv _ := Subsingleton.elim _ _
  right_inv i := @Subsingleton.elim PUnit.{1} inferInstance _ i

/-- The published singleton presentation reindexed into the rational atlas's
index universe. Points, algebras and restrictions are unchanged. -/
def singletonPresentation (A : PresentedAffinoidAlgebra K) :
    AffinoidAtlasPresentation.{u, u, u} K :=
  (PresentedAffinoidSpace.atlasPresentation (Opposite.op A)).reindex
    (singletonIndexEquiv A)

/-- Every admissible pair uses the original rational quotient's base map. -/
def toSingleton (A : PresentedAffinoidAlgebra K) :
    StrongHom (presentation A) (singletonPresentation A) where
  baseMap := ContinuousMap.id _
  target_exists i := ⟨PUnit.unit, by
    change _ ⊆ Set.range (_root_.id : BanachSpectrum A → BanachSpectrum A)
    rw [Set.range_id]
    exact Set.subset_univ _⟩
  pullback i _ _ := i.presentation.baseMap
  chart_comm _ _ _ _ := rfl
  restriction_comm i i' _ _ hi _ _ _ := by
    change Index K A at i i'
    change Set.range (chart i) ⊆ Set.range (chart i') at hi
    change (restriction i i' hi).comp i'.presentation.baseMap =
      i.presentation.baseMap.comp (BoundedAlgHom.id K A)
    rw [restriction_comp_baseMap, BoundedAlgHom.comp_id]

@[simp]
theorem toSingleton_baseMap (A : PresentedAffinoidAlgebra K) :
    (toSingleton A).baseMap = ContinuousMap.id (BanachSpectrum A) := rfl

@[simp]
theorem toSingleton_pullback (A : PresentedAffinoidAlgebra K) (i : Index K A)
    (j : PUnit.{u+1})
    (h : (toSingleton A).baseMap '' Set.range ((presentation A).atlas.chart i) ⊆
      Set.range ((singletonPresentation A).atlas.chart j)) :
    (toSingleton A).pullback i j h = i.presentation.baseMap := rfl

@[simp]
theorem toSingleton_chartImageLocus (A : PresentedAffinoidAlgebra K)
    (i : Index K A) (j : PUnit.{u+1}) :
    (toSingleton A).chartImageLocus i j = i.val := by
  change _root_.id ⁻¹' (_root_.id '' Set.range (chart i)) = i.val
  simpa only [Set.image_id, Set.preimage_id] using range_chart i

/-- Each full rational representation proves the required local domain
condition, including every admissible target index. -/
theorem isQuasiIso_toSingleton (A : PresentedAffinoidAlgebra K) :
    (toSingleton A).IsQuasiIso := by
  refine ⟨IsHomeomorph.id, ?_⟩
  intro i j h
  change Index K A at i
  change PUnit.{u+1} at j
  change Represents K i.presentation.baseMap ((toSingleton A).chartImageLocus i j)
  rw [toSingleton_chartImageLocus]
  rw [← i.locus_presentation]
  exact i.presentation.represents

/-- An admissible target of the singleton chart has the whole literal locus. -/
theorem singleton_admissible_locus (A : PresentedAffinoidAlgebra K)
    (i : PUnit.{u+1}) (j : Index K A)
    (h : (ContinuousMap.id (BanachSpectrum A)) ''
      Set.range ((singletonPresentation A).atlas.chart i) ⊆
      Set.range ((presentation A).atlas.chart j)) :
    j.val = Set.univ := by
  apply Set.Subset.antisymm (Set.subset_univ _)
  change _root_.id '' Set.range (_root_.id : BanachSpectrum A → BanachSpectrum A) ⊆
    Set.range (chart j) at h
  simpa only [Set.range_id, Set.image_id, range_chart] using h

/-- Full representation constructs a bounded equivalence from the actual
base to any chosen rational quotient whose literal locus is the whole space. -/
def fullChartEquiv {A : PresentedAffinoidAlgebra K} (j : Index K A)
    (h : j.val = Set.univ) : BoundedAlgEquiv K A j.presentation.algebra :=
  Domain.boundedEquivOfLocusEq (Domain.whole K A) j.presentation.toDomain
    (j.locus_presentation.trans h).symm

theorem fullChartEquiv_toBoundedAlgHom {A : PresentedAffinoidAlgebra K}
    (j : Index K A) (h : j.val = Set.univ) :
    (fullChartEquiv j h).toBoundedAlgHom = j.presentation.baseMap := by
  have he := Domain.boundedEquivOfLocusEq_comp_baseMap
    (Domain.whole K A) j.presentation.toDomain (j.locus_presentation.trans h).symm
  exact (BoundedAlgHom.comp_id _).symm.trans he

theorem fullChartEquiv_symm_comp_baseMap {A : PresentedAffinoidAlgebra K}
    (j : Index K A) (h : j.val = Set.univ) :
    (fullChartEquiv j h).symm.toBoundedAlgHom.comp j.presentation.baseMap =
      BoundedAlgHom.id K A :=
  Domain.boundedEquivOfLocusEq_symm_comp_baseMap
    (Domain.whole K A) j.presentation.toDomain (j.locus_presentation.trans h).symm

/-- The other inverse equation holds on the entire rational quotient. -/
theorem baseMap_comp_fullChartEquiv_symm {A : PresentedAffinoidAlgebra K}
    (j : Index K A) (h : j.val = Set.univ) :
    j.presentation.baseMap.comp (fullChartEquiv j h).symm.toBoundedAlgHom =
      BoundedAlgHom.id K j.presentation.algebra := by
  rw [← fullChartEquiv_toBoundedAlgHom j h]
  apply BoundedAlgHom.ext
  intro a
  exact (fullChartEquiv j h).apply_symm_apply a

/-- The reverse map uses the actual inverse bounded equivalence at every
admissible whole-locus target, rather than just at a selected chart. -/
def fromSingleton (A : PresentedAffinoidAlgebra K) :
    StrongHom (singletonPresentation A) (presentation A) where
  baseMap := ContinuousMap.id _
  target_exists _ := ⟨Index.whole, by
    change _ ⊆ Set.range ((atlas A).chart Index.whole)
    rw [atlas_whole_range]
    exact Set.subset_univ _⟩
  pullback i j h :=
    (fullChartEquiv j (singleton_admissible_locus A i j h)).symm.toBoundedAlgHom
  chart_comm i j h x := by
    apply BanachSpectrum.ext
    intro a
    exact congrArg (fun φ : BoundedAlgHom K A A => x (φ a))
      (fullChartEquiv_symm_comp_baseMap j (singleton_admissible_locus A i j h))
  restriction_comm i i' j j' _ hj h h' := by
    change Index K A at j j'
    change Set.range (chart j) ⊆ Set.range (chart j') at hj
    change (BoundedAlgHom.id K A).comp
      (fullChartEquiv j' (singleton_admissible_locus A i' j' h')).symm.toBoundedAlgHom =
      ((fullChartEquiv j (singleton_admissible_locus A i j h)).symm.toBoundedAlgHom).comp
        (restriction j j' hj)
    rw [BoundedAlgHom.id_comp]
    apply RationalPresentation.hom_ext_base K A j'.presentation.radii
      j'.presentation.denominator j'.presentation.numerators A j'.presentation.generates
    change
      ((fullChartEquiv j' (singleton_admissible_locus A i' j' h')).symm.toBoundedAlgHom).comp
        j'.presentation.baseMap =
      (((fullChartEquiv j (singleton_admissible_locus A i j h)).symm.toBoundedAlgHom).comp
        (restriction j j' hj)).comp j'.presentation.baseMap
    rw [BoundedAlgHom.comp_assoc, restriction_comp_baseMap,
      fullChartEquiv_symm_comp_baseMap, fullChartEquiv_symm_comp_baseMap]

@[simp]
theorem fromSingleton_baseMap (A : PresentedAffinoidAlgebra K) :
    (fromSingleton A).baseMap = ContinuousMap.id (BanachSpectrum A) := rfl

@[simp]
theorem fromSingleton_pullback (A : PresentedAffinoidAlgebra K) (i : PUnit.{u+1})
    (j : Index K A)
    (h : (fromSingleton A).baseMap '' Set.range ((singletonPresentation A).atlas.chart i) ⊆
      Set.range ((presentation A).atlas.chart j)) :
    (fromSingleton A).pullback i j h =
      (fullChartEquiv j (singleton_admissible_locus A i j h)).symm.toBoundedAlgHom := rfl

@[simp]
theorem fromSingleton_chartImageLocus (A : PresentedAffinoidAlgebra K)
    (i : PUnit.{u+1}) (j : Index K A) :
    (fromSingleton A).chartImageLocus i j = Set.univ := by
  change chart j ⁻¹' (_root_.id ''
    Set.range (_root_.id : BanachSpectrum A → BanachSpectrum A)) = Set.univ
  simp only [Set.range_id, Set.image_id, Set.preimage_univ]

/-- Transport of the full identity representation along the actual bounded
equivalence proves every reverse local pullback represents the whole chart. -/
theorem isQuasiIso_fromSingleton (A : PresentedAffinoidAlgebra K) :
    (fromSingleton A).IsQuasiIso := by
  refine ⟨IsHomeomorph.id, ?_⟩
  intro i j h
  change PUnit.{u+1} at i
  change Index K A at j
  have he := (represents_id A).precomp_equiv
    (fullChartEquiv j (singleton_admissible_locus A i j h))
  change Represents K
    (fullChartEquiv j (singleton_admissible_locus A i j h)).symm.toBoundedAlgHom
    ((fromSingleton A).chartImageLocus i j)
  rw [fromSingleton_chartImageLocus]
  change Represents K
    ((BoundedAlgHom.id K A).comp
      (fullChartEquiv j (singleton_admissible_locus A i j h)).symm.toBoundedAlgHom)
    ((fullChartEquiv j (singleton_admissible_locus A i j h)).spectrumHomeomorph ⁻¹'
      Set.univ)
  exact he

end Langlands.Analytic.RationalSpectrumAtlas
