import Langlands.ClassFieldTheory.Global.CompletionTower
import Langlands.ClassFieldTheory.Local.FiniteArtinTransferReduction
import Langlands.ClassFieldTheory.Local.LocalInvariantFamilyArithmeticProof
import Langlands.GaloisCohomology.Global.BrauerSequence.Existence

/-! # Totally positive elements with prescribed quadratic local norm cosets -/

noncomputable section

namespace Langlands.ClassFieldTheory.Global

open NumberField _root_.Algebra Langlands.Global.AdelicFunctoriality
open Langlands.Global (FiniteCompletion)
open Langlands.Global.CompletionPadic Langlands.ClassFieldTheory.Local
open FundamentalClass Reciprocity LocalSymbolIdentity
open scoped FiniteExtension

universe u

variable {F L : Type u} [Field F] [NumberField F] [Field L] [NumberField L]
  [Algebra F L] [IsQuadraticExtension F L]

attribute [local instance] isGalois_adicCompletion FiniteExtension.local_finite

private theorem quadraticAut_card : Nat.card (L ≃ₐ[F] L) = 2 := by
  rw [IsGalois.card_aut_eq_finrank, IsQuadraticExtension.finrank_eq_two]

private def quadraticCoordinate : (L ≃ₐ[F] L) ≃* Multiplicative (ZMod 2) := by
  classical
  let χ := Langlands.GaloisCohomology.signCharacter (quadraticAut_card (F := F) (L := L))
  letI := Fintype.ofFinite (L ≃ₐ[F] L)
  refine MulEquiv.ofBijective χ ((Fintype.bijective_iff_injective_and_card χ).2 ⟨
    Langlands.GaloisCohomology.signCharacter_injective _, ?_⟩)
  rw [← Nat.card_eq_fintype_card, quadraticAut_card]
  decide

private theorem quadraticCoordinate_of_ne_one {c : L ≃ₐ[F] L} (hc : c ≠ 1) :
    (quadraticCoordinate.toMonoidHom c).toAdd = 1 := by
  change (Langlands.GaloisCohomology.signCharacter quadraticAut_card c).toAdd = 1
  rw [Langlands.GaloisCohomology.signCharacter_apply_of_ne_one _ hc]
  rfl

omit [NumberField L] in
private theorem exists_isConj_of_isReal_comap (w : InfinitePlace L)
    (hw : (w.comap (algebraMap F L)).IsReal) :
    ∃ c : L ≃ₐ[F] L, ComplexEmbedding.IsConj w.embedding c := by
  rw [← InfinitePlace.mk_embedding w, InfinitePlace.comap_mk, InfinitePlace.isReal_mk_iff] at hw
  have h := ComplexEmbedding.isReal_iff.mp hw
  have hc : w.embedding.comp (algebraMap F L) =
      (ComplexEmbedding.conjugate w.embedding).comp (algebraMap F L) := by
    ext x
    exact (RingHom.congr_fun h x).symm
  obtain ⟨c, hc⟩ := ComplexEmbedding.exists_comp_symm_eq_of_comp_eq w.embedding
    (ComplexEmbedding.conjugate w.embedding) hc
  exact ⟨c.symm, hc.symm⟩

private theorem pos_of_archimedeanInvariant_eq_zero [IsTotallyComplex L] (a : Fˣ)
    (harch : ∀ w : InfinitePlace L,
      archimedeanInvariant w (cyclicClass F L quadraticCoordinate.toMonoidHom a) = 0)
    (v : InfinitePlace F) (hv : v.IsReal) : 0 < (v.embedding (a : F)).re := by
  obtain ⟨w, hw⟩ := InfinitePlace.comap_surjective (K := L) v
  have : w.LiesOver v := ⟨congrArg Subtype.val hw⟩
  obtain ⟨c, hc⟩ := exists_isConj_of_isReal_comap w (hw.symm ▸ hv)
  have hc1 : c ≠ 1 := by
    intro he
    subst c
    change ComplexEmbedding.conjugate w.embedding = w.embedding.comp (RingHom.id L) at hc
    rw [RingHom.comp_id] at hc
    have hr : ComplexEmbedding.IsReal w.embedding := ComplexEmbedding.isReal_iff.mpr hc
    exact (InfinitePlace.not_isReal_iff_isComplex.mpr (IsTotallyComplex.isComplex w))
      (InfinitePlace.isReal_iff.mpr hr)
  have h := harch w
  rw [CyclicReciprocity.archimedeanInvariant_cyclicClass_of_isConj quadraticCoordinate.toMonoidHom
    quadraticCoordinate.injective a w c hc, CyclicReciprocity.re_embedding_algebraMap w v,
    quadraticCoordinate_of_ne_one hc1] at h
  have hnonneg : 0 ≤ (v.embedding (a : F)).re := by
    by_contra! hneg
    rw [ite_eq_left hneg] at h
    exact rationalClass_half_ne_zero (by
      simpa [zmodClass_apply, ZMod.val_one_eq_one_mod] using h)
  have hne : (v.embedding (a : F)).re ≠ 0 := by
    let vReal := (InfinitePlace.isReal_iff.mp hv).embedding
    exact (map_ne_zero_iff vReal vReal.injective).2 a.ne_zero
  exact lt_of_le_of_ne hnonneg hne.symm

private theorem finiteLocalInvariant_eq_zero_iff (p : Langlands.Global.FinitePlace F)
    (a : Fˣ) (I : ∀ (p : ℕ) [Fact p.Prime], InvariantFamily.{u, u} p)
    (hI : ∀ (p : ℕ) [Fact p.Prime], (I p).RelativeImages) :
    finiteLocalInvariant p (placeAbove L p).val I
      (cyclicClass F L quadraticCoordinate.toMonoidHom a) = 0 ↔
    Units.map (algebraMap F (FiniteCompletion F p)).toMonoidHom a ∈
        Langlands.LocalClassField.normSubgroup (FiniteCompletion F p)
          (FiniteCompletion L (placeAbove L p).val) := by
  let q := (placeAbove L p).val
  change (I (residuePrime p)).relative (padicField p) (FiniteCompletion L q)
    ((unitsLocalMap p q 2).hom (cyclicClass F L quadraticCoordinate.toMonoidHom a)) = 0 ↔ _
  rw [← map_zero ((I (residuePrime p)).relative (padicField p) (FiniteCompletion L q)),
    (hI _ (padicField p) (FiniteCompletion L q)).1.eq_iff, CompletionTower.unitsLocalMap_cyclicClass]
  exact CyclicClassAlgebra.cyclicClass_eq_zero_iff_of_injective _
    (quadraticCoordinate.injective.comp (decompositionHom_injective p q)) _

/-- A field unit positive at every real place and locally a norm exactly outside `S`. -/
structure PositiveQuadraticNormProfile (F L : Type u) [Field F] [NumberField F]
    [Field L] [NumberField L] [Algebra F L] (S : Finset (Langlands.Global.FinitePlace F)) where
  unit : Fˣ
  positive : ∀ v : InfinitePlace F, v.IsReal → 0 < (v.embedding (unit : F)).re
  finiteNorm : ∀ p : Langlands.Global.FinitePlace F,
    Units.map (algebraMap F (FiniteCompletion F p)).toMonoidHom unit ∈
        Langlands.LocalClassField.normSubgroup (FiniteCompletion F p)
          (FiniteCompletion L (placeAbove L p).val) ↔ p ∉ S

/-- A quadratic extension to a totally complex field realizes each even finite set
of degree-two exceptions by a totally positive base-field unit. -/
def positiveQuadraticNormProfile [IsTotallyComplex L] (S : Finset (Langlands.Global.FinitePlace F))
    (hS : Even S.card)
    (hdeg : ∀ p ∈ S, Module.finrank (FiniteCompletion F p)
      (FiniteCompletion L (placeAbove L p).val) = 2) : PositiveQuadraticNormProfile F L S := by
  classical
  let I (p : ℕ) [Fact p.Prime] := localInvariantFamily unramifiedH2Exhaustion.{u} p
  have hCF (p : ℕ) [Fact p.Prime] :
      (I p).RelativeClassFormation ∧ (I p).ArithmeticNormalization :=
    ⟨FiniteArtinTransferReduction.canonicalClassFormation,
      localInvariantFamilyArithmetic unramifiedH2Exhaustion p⟩
  let a (p : Langlands.Global.FinitePlace F) : RationalModIntegers :=
    if p ∈ S then rationalClass (1 / 2) else 0
  have hhalf : (2 : ℕ) • rationalClass (1 / 2) = 0 := by
    rw [← map_nsmul]
    norm_num [rationalClass_eq_zero_iff]
  have ha (p) (hp : p ∈ S) : a p ∈ denominatorSubgroup
      (Module.finrank (FiniteCompletion F p) (FiniteCompletion L (placeAbove L p).val)) := by
    rw [hdeg p hp]
    change 2 • a p = 0
    simpa only [a, ite_eq_left hp] using hhalf
  have hsum : ∑ p ∈ S, a p = 0 := by
    obtain ⟨k, hk⟩ := hS
    simp only [a, Finset.sum_ite_mem, Finset.inter_self, Finset.sum_const]
    rw [hk, ← two_mul, mul_nsmul, hhalf, smul_zero]
  have hex : Nonempty (PositiveQuadraticNormProfile F L S) := by
    obtain ⟨x, hfin, harch⟩ := exists_relativeCohomology_of_finiteInvariants_archimedean I hCF
      S a (fun p hp => ite_eq_right hp) ha hsum
    obtain ⟨t, ht⟩ := CyclicClassAlgebra.exists_cyclicClass_eq quadraticCoordinate x
    refine ⟨t, pos_of_archimedeanInvariant_eq_zero (L := L) t (fun w => ?_), fun p => ?_⟩
    · rw [ht]
      exact harch w
    · rw [← finiteLocalInvariant_eq_zero_iff (L := L) p t I (fun p _ => (hCF p).1.2.1), ht, hfin]
      by_cases hp : p ∈ S
      · simp only [a, ite_eq_left hp, hp, not_true, iff_false]
        exact rationalClass_half_ne_zero
      · simp [a, hp]
  exact Classical.choice hex

end Langlands.ClassFieldTheory.Global
