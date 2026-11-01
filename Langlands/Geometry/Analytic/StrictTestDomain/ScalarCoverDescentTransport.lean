import Langlands.Geometry.Analytic.StrictTestDomain.ScalarCoverDescent
import Langlands.Geometry.Analytic.StrictTestDomain.StandardRationalLaurentReduction
import Mathlib.Logic.Equiv.Basic
import Mathlib.Data.Fin.SuccPred

/-! # Transport of scalar sections and descent on actual rational quotients -/

noncomputable section

universe u v w

namespace Langlands.Analytic.StrictTestDomain

open CategoryTheory RationalData

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {P : PresentedStrictAffinoidAlgebra K}

namespace RationalData

@[simp]
theorem equalLocusEquiv_comp_baseMap (d e : RationalData K P)
    (h : d.locus = e.locus) :
    (StandardRationalLaurentReduction.locusEquiv h).toBoundedAlgHom.comp d.baseMap = e.baseMap :=
  (show e ⟶ d from ⟨h.ge⟩).restriction_comp_baseMap

@[simp]
theorem equalLocusEquiv_symm_comp_baseMap (d e : RationalData K P)
    (h : d.locus = e.locus) :
    (StandardRationalLaurentReduction.locusEquiv h).symm.toBoundedAlgHom.comp e.baseMap = d.baseMap :=
  (show d ⟶ e from ⟨h.le⟩).restriction_comp_baseMap

end RationalData

/-- Transport an actual scalar family by the bounded equivalences of equal loci. -/
def scalarSectionsLocusEquiv {I : Type v} (D E : I → RationalData K P)
    (h : ∀ i, (D i).locus = (E i).locus) :
    (∀ i, (D i).algebra) ≃ (∀ i, (E i).algebra) :=
  Equiv.piCongrRight (fun i => (StandardRationalLaurentReduction.locusEquiv (h i)).toAlgEquiv.toEquiv)

@[simp]
theorem scalarSectionsLocusEquiv_apply {I : Type v} (D E : I → RationalData K P)
    (h : ∀ i, (D i).locus = (E i).locus) (s : ∀ i, (D i).algebra) (i : I) :
    scalarSectionsLocusEquiv D E h s i = StandardRationalLaurentReduction.locusEquiv (h i) (s i) :=
  rfl

/-- Reindex an actual scalar family along an equivalence of its index types. -/
def scalarSectionsReindex {I : Type v} {J : Type w} (D : I → RationalData K P)
    (e : J ≃ I) :
    (∀ i, (D i).algebra) ≃ (∀ j, (D (e j)).algebra) :=
  (Equiv.piCongrLeft (fun i => (D i).algebra) e).symm

@[simp]
theorem scalarSectionsReindex_apply {I : Type v} {J : Type w}
    (D : I → RationalData K P) (e : J ≃ I) (s : ∀ i, (D i).algebra) (j : J) :
    scalarSectionsReindex D e s j = s (e j) :=
  Equiv.piCongrLeft_symm_apply _ _ _ _

namespace CompatibleScalarSections

/-- Bounded maps over the same base preserve actual ordered-pair compatibility. -/
theorem map {I : Type v} {D E : I → RationalData K P}
    {s : ∀ i, (D i).algebra} (hs : CompatibleScalarSections D s)
    (r : ∀ i, BoundedAlgHom K (D i).algebra (E i).algebra)
    (hr : ∀ i, (r i).comp (D i).baseMap = (E i).baseMap) :
    CompatibleScalarSections E (fun i => r i (s i)) := by
  intro i j
  exact compatible_sections_apply (s i) (s j) (hs i j)
    ((interLeft (E i) (E j)).restriction.comp (r i))
    ((interRight (E i) (E j)).restriction.comp (r j))
    (by rw [BoundedAlgHom.comp_assoc, hr i, Inclusion.restriction_comp_baseMap,
      BoundedAlgHom.comp_assoc, hr j, Inclusion.restriction_comp_baseMap])

theorem reindex {I : Type v} {J : Type w} {D : I → RationalData K P}
    {s : ∀ i, (D i).algebra} (hs : CompatibleScalarSections D s) (e : J ≃ I) :
    CompatibleScalarSections (fun j => D (e j)) (scalarSectionsReindex D e s) :=
  fun i j => hs (e i) (e j)

theorem locusEquiv {I : Type v} {D E : I → RationalData K P}
    (h : ∀ i, (D i).locus = (E i).locus)
    {s : ∀ i, (D i).algebra} (hs : CompatibleScalarSections D s) :
    CompatibleScalarSections E (scalarSectionsLocusEquiv D E h s) :=
  hs.map (fun i => (StandardRationalLaurentReduction.locusEquiv (h i)).toBoundedAlgHom)
    (fun _ => equalLocusEquiv_comp_baseMap _ _ _)

end CompatibleScalarSections

omit [CompleteSpace K] in
/-- Reindexing a finite tuple preserves the absence of a common spectrum zero. -/
theorem tuple_no_common_zero_reindex {n m : ℕ} (f : Fin n → P)
    (hf : ∀ x : BanachSpectrum P, ∃ i, x (f i) ≠ 0) (e : Fin m ≃ Fin n) :
    ∀ x : BanachSpectrum P, ∃ j, x (f (e j)) ≠ 0 := by
  intro x
  obtain ⟨i, hi⟩ := hf x
  exact ⟨e.symm i, by simpa using hi⟩

omit [CompleteSpace K] in
/-- Reindexing all entries does not change the locus selected by an entry. -/
theorem standardRational_locus_reindex {n m : ℕ} (f : Fin n → P)
    (hf : ∀ x : BanachSpectrum P, ∃ i, x (f i) ≠ 0) (e : Fin m ≃ Fin n)
    (he : ∀ x : BanachSpectrum P, ∃ j, x (f (e j)) ≠ 0) (j : Fin m) :
    (standardRational (fun i => f (e i)) he j).locus =
      (standardRational f hf (e j)).locus := by
  ext x
  simp only [mem_standardRational_locus]
  constructor
  · intro hx i
    obtain ⟨k, rfl⟩ := e.surjective i
    exact hx k
  · intro hx i
    exact hx (e i)

namespace ScalarCoverDescent

/-- Descent is preserved under equivalences of arbitrary index types. -/
theorem reindex {I : Type v} {J : Type w} {D : I → RationalData K P}
    (hD : ScalarCoverDescent D) (e : J ≃ I) :
    ScalarCoverDescent (fun j => D (e j)) := by
  intro s hs
  let t := (scalarSectionsReindex D e).symm s
  have ht : CompatibleScalarSections D t := by
    intro i k
    obtain ⟨j, rfl⟩ := e.surjective i
    obtain ⟨l, rfl⟩ := e.surjective k
    simpa [t, scalarSectionsReindex] using hs j l
  obtain ⟨a, ha, hu⟩ := hD t ht
  refine ⟨a, fun j => ?_, fun b hb => hu b ?_⟩
  · simpa [t, scalarSectionsReindex] using ha (e j)
  · intro i
    obtain ⟨j, rfl⟩ := e.surjective i
    simpa [t, scalarSectionsReindex] using hb j

theorem reindex_iff {I : Type v} {J : Type w} (D : I → RationalData K P)
    (e : J ≃ I) :
    ScalarCoverDescent (fun j => D (e j)) ↔ ScalarCoverDescent D := by
  refine ⟨fun h => ?_, fun h => h.reindex e⟩
  simpa only [Equiv.apply_symm_apply] using h.reindex e.symm

/-- Equal actual loci allow replacement of every chosen quotient presentation. -/
theorem of_locus_eq {I : Type v} {D E : I → RationalData K P}
    (hD : ScalarCoverDescent D) (h : ∀ i, (D i).locus = (E i).locus) :
    ScalarCoverDescent E := by
  intro s hs
  let r (i : I) := StandardRationalLaurentReduction.locusEquiv (h i)
  let t (i : I) : (D i).algebra := (r i).symm (s i)
  have ht : CompatibleScalarSections D t :=
    hs.map (fun i => (r i).symm.toBoundedAlgHom)
      (fun i => equalLocusEquiv_symm_comp_baseMap _ _ _)
  obtain ⟨a, ha, hu⟩ := hD t ht
  refine ⟨a, fun i => ?_, fun b hb => hu b ?_⟩
  · have he := congrArg (r i) (ha i)
    change (r i).toBoundedAlgHom.comp (D i).baseMap a = (r i) ((r i).symm (s i)) at he
    simpa [r] using he
  · intro i
    have he := congrArg (r i).symm (hb i)
    change (r i).symm.toBoundedAlgHom.comp (E i).baseMap b = t i at he
    simpa [r] using he

theorem locus_eq_iff {I : Type v} (D E : I → RationalData K P)
    (h : ∀ i, (D i).locus = (E i).locus) :
    ScalarCoverDescent D ↔ ScalarCoverDescent E :=
  ⟨fun hD => hD.of_locus_eq h, fun hE => hE.of_locus_eq (fun i => (h i).symm)⟩

/-- Replace a reindexed descending family by any presentations of the same loci. -/
theorem of_reindex_locus_eq {I : Type v} {J : Type w}
    {D : I → RationalData K P} (hD : ScalarCoverDescent D)
    (E : J → RationalData K P) (e : J ≃ I)
    (h : ∀ j, (D (e j)).locus = (E j).locus) : ScalarCoverDescent E :=
  (hD.reindex e).of_locus_eq h

/-- Adjoin a final quotient with one element to an already descending family. -/
theorem of_castSucc {n : ℕ} (D : Fin (n + 1) → RationalData K P)
    [Subsingleton (D (Fin.last n)).algebra]
    (hD : ScalarCoverDescent (fun i : Fin n => D i.castSucc)) :
    ScalarCoverDescent D := by
  intro s hs
  obtain ⟨a, ha, hu⟩ := hD (fun i => s i.castSucc) (fun i j => hs i.castSucc j.castSucc)
  exact ⟨a, fun i => Fin.lastCases (Subsingleton.elim _ _) ha i,
    fun b hb => hu b (fun i => hb i.castSucc)⟩

/-- The same extension when the last actual rational locus is empty. -/
theorem of_castSucc_locus_empty {n : ℕ} (D : Fin (n + 1) → RationalData K P)
    (he : (D (Fin.last n)).locus = ∅)
    (hD : ScalarCoverDescent (fun i : Fin n => D i.castSucc)) :
    ScalarCoverDescent D := by
  let := subsingleton_algebra_of_locus_empty (D (Fin.last n)) he
  exact of_castSucc D hD

/-- Standard-cover descent is invariant under permutations of the whole tuple,
including the change in each numerator presentation. -/
theorem standard_reindex_iff {n m : ℕ} (f : Fin n → P)
    (hf : ∀ x : BanachSpectrum P, ∃ i, x (f i) ≠ 0) (e : Fin m ≃ Fin n)
    (he : ∀ x : BanachSpectrum P, ∃ j, x (f (e j)) ≠ 0) :
    ScalarCoverDescent (standardRational (fun i => f (e i)) he) ↔
      ScalarCoverDescent (standardRational f hf) :=
  (locus_eq_iff _ _ (standardRational_locus_reindex f hf e he)).trans
    (reindex_iff _ e)

end ScalarCoverDescent

namespace UniversalScalarCoverDescent

theorem reindex {I : Type v} {J : Type w} {D : I → RationalData K P}
    (hD : UniversalScalarCoverDescent D) (e : J ≃ I) :
    UniversalScalarCoverDescent (fun j => D (e j)) :=
  fun Q φ => (hD Q φ).reindex e

theorem of_locus_eq {I : Type v} {D E : I → RationalData K P}
    (hD : UniversalScalarCoverDescent D)
    (h : ∀ i, (D i).locus = (E i).locus) :
    UniversalScalarCoverDescent E := by
  intro Q φ
  exact (hD Q φ).of_locus_eq (fun i => by rw [locus_pullback, locus_pullback, h i])

end UniversalScalarCoverDescent

end Langlands.Analytic.StrictTestDomain
