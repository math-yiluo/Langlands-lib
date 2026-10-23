import Langlands.ClassField.Global.IdeleArchimedeanChoice
import Mathlib.NumberTheory.NumberField.Completion.Ramification

/-! # Archimedean idele invariants under restriction -/

noncomputable section

namespace Langlands.ClassField.Global

open NumberField CategoryTheory Reciprocity
open scoped NumberField
open Langlands.Global.AdelicFunctoriality Langlands.ClassFieldTheory.Local

universe u

section Values

variable {F E : Type u} [Field F] [Field E] [NumberField E] [Algebra F E]

/-- The archimedean idele invariant is killed by two. -/
theorem two_nsmul_archimedeanIdeleInvariant (q : InfinitePlace E)
    (x : relativeIdeleCohomology F E 2) :
    2 • archimedeanIdeleInvariant F q x = 0 := by
  obtain ⟨f, rfl⟩ := H2π_surjective x
  rw [archimedeanIdeleInvariant_H2π]
  unfold archimedeanIdeleCocycleHom
  split_ifs
  · change 2 • signClass _ = 0
    unfold signClass
    split_ifs
    · exact (two_nsmul _).trans rationalClass_half_add_half
    · exact nsmul_zero _
  · exact nsmul_zero _

/-- The archimedean idele invariant vanishes at an unramified infinite place. -/
theorem archimedeanIdeleInvariant_eq_zero_of_isUnramified (q : InfinitePlace E)
    (hq : q.IsUnramified F) (x : relativeIdeleCohomology F E 2) :
    archimedeanIdeleInvariant F q x = 0 := by
  obtain ⟨f, rfl⟩ := H2π_surjective x
  rw [archimedeanIdeleInvariant_H2π]
  exact archimedeanIdeleCocycleHom_apply_of_stabilizer_eq_bot hq.stabilizer_eq_bot f

end Values

section Restriction

variable {F K E : Type u} [Field F] [Field K] [Field E] [NumberField E]
  [Algebra F K] [Algebra K E] [Algebra F E] [IsScalarTower F K E]

/-- Restriction retains the conjugation value at the same field automorphism. -/
theorem ideleConjugationValue_restriction (c : E ≃ₐ[K] E)
    (f : groupCohomology.cocycles₂ (relativeIdeleRepresentation F E)) :
    ideleConjugationValue c
      (groupCohomology.mapCocycles₂ (AlgEquiv.restrictScalarsHom F)
        (ideleRestrictionCoefficients F K E) f) =
      ideleConjugationValue (c.restrictScalars F) f := rfl

variable [IsGalois F E]

/-- If the upper infinite place remains ramified over the intermediate base,
restriction preserves its archimedean idele invariant. -/
theorem archimedeanIdeleInvariant_relativeIdeleRestriction_of_isRamified
    (q : InfinitePlace E) (hq : q.IsRamified K)
    (x : relativeIdeleCohomology F E 2) :
    archimedeanIdeleInvariant K q (relativeIdeleRestriction F K E 2 x) =
      archimedeanIdeleInvariant F q x := by
  have := IsGalois.tower_top_of_isGalois F K E
  obtain ⟨c, hc⟩ := InfinitePlace.exists_isConj_of_isRamified
    (show (InfinitePlace.mk q.embedding).IsRamified K by rwa [InfinitePlace.mk_embedding])
  have hc1 : c ≠ 1 := by
    intro h
    have hr := ComplexEmbedding.isConj_one_iff.1 (h ▸ hc)
    exact (InfinitePlace.not_isReal_iff_isComplex.2 hq.isComplex)
      (InfinitePlace.isReal_iff.2 hr)
  have hcS : c ∈ MulAction.stabilizer (E ≃ₐ[K] E) q := by
    simpa only [InfinitePlace.mk_embedding] using
      (InfinitePlace.mem_stabilizer_mk_iff q.embedding c).2 (Or.inr hc)
  have hcF : ComplexEmbedding.IsConj q.embedding (c.restrictScalars F) := hc
  have hcFS : c.restrictScalars F ∈ MulAction.stabilizer (E ≃ₐ[F] E) q := by
    simpa only [InfinitePlace.mk_embedding] using
      (InfinitePlace.mem_stabilizer_mk_iff q.embedding (c.restrictScalars F)).2 (Or.inr hcF)
  have hcF1 : c.restrictScalars F ≠ 1 := by
    intro h
    apply hc1
    ext a
    exact AlgEquiv.congr_fun h a
  obtain ⟨f, rfl⟩ := H2π_surjective x
  rw [groupCohomology.H2π_comp_map_apply,
    archimedeanIdeleInvariant_H2π, archimedeanIdeleInvariant_H2π,
    archimedeanIdeleCocycleHom_apply_of_mem hcS hc1,
    archimedeanIdeleCocycleHom_apply_of_mem hcFS hcF1,
    ideleConjugationValue_restriction]

/-- Restriction multiplies an archimedean idele invariant by the completed base degree. -/
theorem archimedeanIdeleInvariant_relativeIdeleRestriction
    (v : InfinitePlace F) (w : InfinitePlace K) (q : InfinitePlace E)
    [w.LiesOver v] [q.LiesOver w] [q.LiesOver v]
    (x : relativeIdeleCohomology F E 2) :
    archimedeanIdeleInvariant K q (relativeIdeleRestriction F K E 2 x) =
      v.inertiaDeg w • archimedeanIdeleInvariant F q x := by
  by_cases hqK : q.IsUnramified K
  · rw [archimedeanIdeleInvariant_eq_zero_of_isUnramified q hqK]
    by_cases hqF : q.IsUnramified F
    · rw [archimedeanIdeleInvariant_eq_zero_of_isUnramified q hqF, smul_zero]
    · have hrF : q.IsRamified F := hqF
      have hw : w.IsRamified F := by
        rw [InfinitePlace.isRamified_iff, InfinitePlace.LiesOver.comap_eq w v]
        refine ⟨?_, InfinitePlace.IsRamified.liesOver_isReal_under q v hrF⟩
        by_contra hwc
        have hwr := InfinitePlace.not_isComplex_iff_isReal.1 hwc
        exact (InfinitePlace.not_isReal_iff_isComplex.2 hrF.isComplex)
          (InfinitePlace.IsUnramified.liesOver_isReal_over q w hqK hwr)
      rw [InfinitePlace.inertiaDeg_eq_two ⟨inferInstance, hw⟩,
        two_nsmul_archimedeanIdeleInvariant]
  · have hrK : q.IsRamified K := hqK
    have hwr : w.IsReal := InfinitePlace.IsRamified.liesOver_isReal_under q w hrK
    rw [InfinitePlace.inertiaDeg_eq_one ⟨inferInstance, hwr.isUnramified F⟩, one_smul]
    exact archimedeanIdeleInvariant_relativeIdeleRestriction_of_isRamified q hqK x

end Restriction

section Vector

variable {F E : Type u} [Field F] [Field E] [NumberField E] [Algebra F E] [IsGalois F E]

/-- The archimedean idele invariants indexed canonically by the base places. -/
def archimedeanIdeleInvariantVector :
    relativeIdeleCohomology F E 2 →+ (InfinitePlace F → RationalModIntegers) where
  toFun x v := archimedeanIdeleInvariantAt v x
  map_zero' := by ext v; exact map_zero _
  map_add' x y := by ext v; exact map_add _ x y

@[simp] theorem archimedeanIdeleInvariantVector_apply
    (x : relativeIdeleCohomology F E 2) (v : InfinitePlace F) :
    archimedeanIdeleInvariantVector x v = archimedeanIdeleInvariantAt v x := rfl

variable {K : Type u} [Field K] [Algebra F K] [Algebra K E] [IsScalarTower F K E]

/-- The canonical archimedean vector satisfies the local restriction formula. -/
theorem archimedeanIdeleInvariantVector_relativeIdeleRestriction
    (v : InfinitePlace F) (w : InfinitePlace K) [w.LiesOver v]
    (x : relativeIdeleCohomology F E 2) :
    haveI := IsGalois.tower_top_of_isGalois F K E
    archimedeanIdeleInvariantVector (relativeIdeleRestriction F K E 2 x) w =
      v.inertiaDeg w • archimedeanIdeleInvariantVector x v := by
  have := IsGalois.tower_top_of_isGalois F K E
  obtain ⟨q, hq⟩ := InfinitePlace.comap_surjective (k := K) (K := E) w
  have : q.LiesOver w := ⟨by rw [← hq]; rfl⟩
  have : q.LiesOver v := liesOver_of_comap_eq hq v
  simp only [archimedeanIdeleInvariantVector_apply,
    archimedeanIdeleInvariantAt_eq w q hq,
    archimedeanIdeleInvariantAt_eq v q (InfinitePlace.LiesOver.comap_eq q v)]
  exact archimedeanIdeleInvariant_relativeIdeleRestriction v w q x

end Vector

end Langlands.ClassField.Global
