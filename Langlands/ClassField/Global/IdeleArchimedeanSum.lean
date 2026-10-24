import Langlands.ClassField.Global.IdeleArchimedeanRestriction

/-! # The canonical archimedean invariant sum and its tower laws -/

noncomputable section

namespace Langlands.ClassField.Global

open NumberField CategoryTheory Reciprocity
open scoped NumberField Classical
open Langlands.Global.AdelicFunctoriality Langlands.ClassFieldTheory.Local

universe u

section Sum

variable {F E : Type u} [Field F] [Field E] [NumberField F] [NumberField E]
  [Algebra F E] [IsGalois F E]

/-- The sum of the canonical archimedean idele invariants over all base places. -/
def canonicalArchimedeanIdeleInvariantSum :
    relativeIdeleCohomology F E 2 →+ RationalModIntegers :=
  ∑ v, archimedeanIdeleInvariantAt v

@[simp] theorem canonicalArchimedeanIdeleInvariantSum_apply
    (x : relativeIdeleCohomology F E 2) :
    canonicalArchimedeanIdeleInvariantSum x = ∑ v, archimedeanIdeleInvariantAt v x := by
  simp only [canonicalArchimedeanIdeleInvariantSum, AddMonoidHom.finsetSum_apply]

/-- The canonical sum agrees with the sum made using any chosen upper places. -/
theorem canonicalArchimedeanIdeleInvariantSum_eq
    (wi : ∀ v : InfinitePlace F, InfinitePlacesAbove E v) :
    canonicalArchimedeanIdeleInvariantSum = archimedeanIdeleInvariantSum wi := by
  ext x
  simp only [canonicalArchimedeanIdeleInvariantSum_apply, archimedeanIdeleInvariantSum_apply]
  apply Finset.sum_congr rfl
  intro v _
  let := (wi v).2
  rw [archimedeanIdeleInvariantAt_eq v (wi v).1 (InfinitePlace.LiesOver.comap_eq _ _)]

end Sum

section Restriction

variable {F K E : Type u} [Field F] [Field K] [Field E]
  [NumberField F] [NumberField K] [NumberField E]
  [Algebra F K] [Algebra K E] [Algebra F E] [IsScalarTower F K E] [IsGalois F E]

/-- Summing over all infinite places of an extension can be done one base place at a time. -/
theorem sum_infinitePlaces_eq_sum_placesOver {A : Type*} [AddCommMonoid A]
    (f : InfinitePlace K → A) :
    ∑ w, f w = ∑ v : InfinitePlace F, ∑ w ∈ v.placesOver K, f w := by
  classical
  have hf (v : InfinitePlace F) :
      Finset.univ.filter (fun w : InfinitePlace K => w.comap (algebraMap F K) = v) =
        (v.placesOver K).toFinset := by
    ext w
    rw [Finset.mem_filter, Set.mem_toFinset]
    change (w ∈ Finset.univ ∧ w.comap (algebraMap F K) = v) ↔ w.LiesOver v
    simp only [Finset.mem_univ, true_and]
    constructor
    · intro h
      exact ⟨by rw [← h]; rfl⟩
    · intro h
      let := h
      exact InfinitePlace.LiesOver.comap_eq w v
  simpa only [hf] using
    (Finset.sum_fiberwise Finset.univ (fun w : InfinitePlace K =>
      w.comap (algebraMap F K)) f).symm

/-- Restriction multiplies the complete archimedean sum by the global base degree. -/
theorem canonicalArchimedeanIdeleInvariantSum_relativeIdeleRestriction
    (x : relativeIdeleCohomology F E 2) :
    haveI := IsGalois.tower_top_of_isGalois F K E
    canonicalArchimedeanIdeleInvariantSum (relativeIdeleRestriction F K E 2 x) =
      Module.finrank F K • canonicalArchimedeanIdeleInvariantSum x := by
  classical
  have := IsGalois.tower_top_of_isGalois F K E
  simp only [canonicalArchimedeanIdeleInvariantSum_apply]
  rw [sum_infinitePlaces_eq_sum_placesOver (F := F), Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro v _
  calc
    ∑ w ∈ v.placesOver K, archimedeanIdeleInvariantAt w
        (relativeIdeleRestriction F K E 2 x) =
        ∑ w ∈ v.placesOver K, v.inertiaDeg w • archimedeanIdeleInvariantAt v x := by
      apply Finset.sum_congr rfl
      intro w hw
      have : w.LiesOver v := (Set.mem_toFinset.mp hw : w ∈ v.placesOver K)
      exact archimedeanIdeleInvariantVector_relativeIdeleRestriction v w x
    _ = (∑ w ∈ v.placesOver K, v.inertiaDeg w) • archimedeanIdeleInvariantAt v x :=
      Finset.sum_smul.symm
    _ = Module.finrank F K • archimedeanIdeleInvariantAt v x := by
      rw [InfinitePlace.sum_inertiaDeg_eq_finrank F K v]

/-- The archimedean restriction formula holds for arbitrary choices of upper places. -/
theorem archimedeanIdeleInvariantSum_relativeIdeleRestriction
    (wi : ∀ v : InfinitePlace F, InfinitePlacesAbove E v)
    (wi' : ∀ w : InfinitePlace K, InfinitePlacesAbove E w)
    (x : relativeIdeleCohomology F E 2) :
    archimedeanIdeleInvariantSum wi' (relativeIdeleRestriction F K E 2 x) =
      Module.finrank F K • archimedeanIdeleInvariantSum wi x := by
  have := IsGalois.tower_top_of_isGalois F K E
  rw [← canonicalArchimedeanIdeleInvariantSum_eq wi,
    ← canonicalArchimedeanIdeleInvariantSum_eq wi']
  exact canonicalArchimedeanIdeleInvariantSum_relativeIdeleRestriction x

end Restriction

section Inflation

variable {F E L : Type u} [Field F] [Field E] [Field L]
  [NumberField F] [NumberField E] [NumberField L]
  [Algebra F E] [Algebra E L] [Algebra F L] [IsScalarTower F E L]
  [IsGalois F E] [IsGalois F L]

/-- Inflation preserves the invariant indexed by a base infinite place. -/
theorem archimedeanIdeleInvariantAt_relativeIdeleInflation (v : InfinitePlace F)
    (x : relativeIdeleCohomology F E 2) :
    archimedeanIdeleInvariantAt v (relativeIdeleInflation F E L 2 x) =
      archimedeanIdeleInvariantAt v x := by
  obtain ⟨q, hq⟩ := InfinitePlace.comap_surjective (k := F) (K := L) v
  have : q.LiesOver v := ⟨by rw [← hq]; rfl⟩
  have := liesOver_comap (E := E) q v
  rw [archimedeanIdeleInvariantAt_eq v q hq,
    archimedeanIdeleInvariant_relativeIdeleInflation,
    archimedeanIdeleInvariantAt_eq v (q.comap (algebraMap E L))
      (InfinitePlace.LiesOver.comap_eq _ _)]

/-- Inflation preserves the canonical archimedean sum. -/
theorem canonicalArchimedeanIdeleInvariantSum_relativeIdeleInflation
    (x : relativeIdeleCohomology F E 2) :
    canonicalArchimedeanIdeleInvariantSum (relativeIdeleInflation F E L 2 x) =
      canonicalArchimedeanIdeleInvariantSum x := by
  simp only [canonicalArchimedeanIdeleInvariantSum_apply,
    archimedeanIdeleInvariantAt_relativeIdeleInflation]

/-- Inflation preserves archimedean sums without a compatibility condition on the chosen places. -/
theorem archimedeanIdeleInvariantSum_relativeIdeleInflation_of_arbitrary_choices
    (wi : ∀ v : InfinitePlace F, InfinitePlacesAbove E v)
    (wi' : ∀ v : InfinitePlace F, InfinitePlacesAbove L v)
    (x : relativeIdeleCohomology F E 2) :
    archimedeanIdeleInvariantSum wi' (relativeIdeleInflation F E L 2 x) =
      archimedeanIdeleInvariantSum wi x := by
  rw [← canonicalArchimedeanIdeleInvariantSum_eq wi,
    ← canonicalArchimedeanIdeleInvariantSum_eq wi']
  exact canonicalArchimedeanIdeleInvariantSum_relativeIdeleInflation x

end Inflation

end Langlands.ClassField.Global
