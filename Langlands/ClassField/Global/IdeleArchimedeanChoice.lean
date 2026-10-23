import Langlands.ClassField.Global.IdeleArchimedeanTower
import Langlands.Cohomology.OrdinaryInnerConjugation

/-! # Independence of the infinite place chosen above a base place -/

noncomputable section

namespace Langlands.ClassField.Global

open NumberField CategoryTheory Reciprocity
open scoped NumberField
open Langlands.Global.AdelicFunctoriality Langlands.ClassFieldTheory.Local
open Langlands.OrdinaryCohomology

universe u

variable {F E : Type u} [Field F] [Field E] [NumberField E] [Algebra F E]

/-- The sign of an infinite coordinate is transported by the actual idele action. -/
theorem signClass_ideleInfiniteCoordinate_relativeIdeleAut (g : E ≃ₐ[F] E)
    (w : InfinitePlace E) (a : IdeleGroup (𝓞 E) E) :
    signClass (InfinitePlace.Completion.extensionEmbedding w
      (ideleInfiniteCoordinate w (relativeIdeleAut F E g a))) =
    signClass (InfinitePlace.Completion.extensionEmbedding
      (infinitePlaceEquiv g.toRingEquiv w)
      (ideleInfiniteCoordinate (infinitePlaceEquiv g.toRingEquiv w) a)) := by
  rw [ideleInfiniteCoordinate_relativeIdeleAut, infiniteCompletionEquiv_apply]
  exact signClass_infiniteCompletionMap g.toRingEquiv.toRingHom w _

omit [NumberField E] in
/-- Conjugating the stabilizer matches pullback of the infinite place. -/
theorem mem_stabilizer_infinitePlaceEquiv_iff (g c : E ≃ₐ[F] E) (w : InfinitePlace E) :
    g⁻¹ * c * g ∈ MulAction.stabilizer (E ≃ₐ[F] E)
      (infinitePlaceEquiv g.toRingEquiv w) ↔
      c ∈ MulAction.stabilizer (E ≃ₐ[F] E) w := by
  simp only [MulAction.mem_stabilizer_iff, infinitePlaceEquiv_eq_inv_smul,
    mul_smul, smul_inv_smul, smul_left_cancel_iff]

omit [NumberField E] in
/-- Nontrivial stabilizers exist at a place exactly when they exist at its pullback. -/
theorem exists_nontrivial_stabilizer_infinitePlaceEquiv_iff (g : E ≃ₐ[F] E)
    (w : InfinitePlace E) :
    (∃ c : E ≃ₐ[F] E, c ∈ MulAction.stabilizer (E ≃ₐ[F] E)
      (infinitePlaceEquiv g.toRingEquiv w) ∧ c ≠ 1) ↔
    ∃ c : E ≃ₐ[F] E, c ∈ MulAction.stabilizer (E ≃ₐ[F] E) w ∧ c ≠ 1 := by
  constructor
  · rintro ⟨c, hc, hc1⟩
    have heq : g⁻¹ * (g * c * g⁻¹) * g = c := by group
    refine ⟨g * c * g⁻¹, ?_, ?_⟩
    · apply (mem_stabilizer_infinitePlaceEquiv_iff g _ w).1
      rwa [heq]
    · intro h
      apply hc1
      calc
        c = g⁻¹ * (g * c * g⁻¹) * g := heq.symm
        _ = 1 := by rw [h]; group
  · rintro ⟨c, hc, hc1⟩
    refine ⟨g⁻¹ * c * g, (mem_stabilizer_infinitePlaceEquiv_iff g c w).2 hc, ?_⟩
    intro h
    apply hc1
    calc
      c = g * (g⁻¹ * c * g) * g⁻¹ := by group
      _ = 1 := by rw [h]; group

/-- Conjugation values of transformed cocycles are transformed values at the conjugated element. -/
theorem ideleConjugationValue_innerConjugation (g c : E ≃ₐ[F] E)
    (f : groupCohomology.cocycles₂ (relativeIdeleRepresentation F E)) :
    ideleConjugationValue c
      (groupCohomology.mapCocycles₂ (innerConjugation g⁻¹)
        (innerConjugationCoefficient (relativeIdeleRepresentation F E) g⁻¹) f) =
    relativeIdeleAut F E g (ideleConjugationValue (g⁻¹ * c * g) f) := by
  unfold ideleConjugationValue
  rw [groupCohomology.coe_mapCocycles₂]
  change @Additive.toMul (IdeleGroup (𝓞 E) E)
      ((relativeIdeleRepresentation F E).ρ (g⁻¹)⁻¹
          (f (g⁻¹ * c * (g⁻¹)⁻¹, g⁻¹ * c * (g⁻¹)⁻¹)) +
        (relativeIdeleRepresentation F E).ρ (g⁻¹)⁻¹
          (f (g⁻¹ * 1 * (g⁻¹)⁻¹, g⁻¹ * 1 * (g⁻¹)⁻¹))) = _
  simp only [inv_inv, mul_one, inv_mul_cancel, ← map_add]
  rfl

/-- The cocycle invariant at a place transforms to the invariant at its pullback. -/
theorem archimedeanIdeleCocycleHom_innerConjugation (g : E ≃ₐ[F] E)
    (w : InfinitePlace E)
    (f : groupCohomology.cocycles₂ (relativeIdeleRepresentation F E)) :
    archimedeanIdeleCocycleHom F w
      (groupCohomology.mapCocycles₂ (innerConjugation g⁻¹)
        (innerConjugationCoefficient (relativeIdeleRepresentation F E) g⁻¹) f) =
    archimedeanIdeleCocycleHom F (infinitePlaceEquiv g.toRingEquiv w) f := by
  by_cases h : ∃ c : E ≃ₐ[F] E, c ∈ MulAction.stabilizer (E ≃ₐ[F] E) w ∧ c ≠ 1
  · obtain ⟨c, hc, hc1⟩ := h
    have hc' := (mem_stabilizer_infinitePlaceEquiv_iff g c w).2 hc
    have hc1' : g⁻¹ * c * g ≠ 1 := by
      intro he
      apply hc1
      calc
        c = g * (g⁻¹ * c * g) * g⁻¹ := by group
        _ = 1 := by rw [he]; group
    rw [archimedeanIdeleCocycleHom_apply_of_mem hc hc1,
      archimedeanIdeleCocycleHom_apply_of_mem hc' hc1',
      ideleConjugationValue_innerConjugation,
      signClass_ideleInfiniteCoordinate_relativeIdeleAut]
  · rw [archimedeanIdeleCocycleHom_apply_of_not_exists h,
      archimedeanIdeleCocycleHom_apply_of_not_exists
        (fun h' => h ((exists_nontrivial_stabilizer_infinitePlaceEquiv_iff g w).1 h'))]

/-- The actual archimedean idele invariant has the same value at a conjugate infinite place. -/
theorem archimedeanIdeleInvariant_infinitePlaceEquiv (g : E ≃ₐ[F] E)
    (w : InfinitePlace E) (x : relativeIdeleCohomology F E 2) :
    archimedeanIdeleInvariant F (infinitePlaceEquiv g.toRingEquiv w) x =
      archimedeanIdeleInvariant F w x := by
  have h : archimedeanIdeleInvariant F w
      (innerConjugationMap (relativeIdeleRepresentation F E) g⁻¹ 2 x) =
      archimedeanIdeleInvariant F (infinitePlaceEquiv g.toRingEquiv w) x := by
    obtain ⟨f, rfl⟩ := H2π_surjective x
    rw [groupCohomology.H2π_comp_map_apply,
      archimedeanIdeleInvariant_H2π, archimedeanIdeleInvariant_H2π]
    exact archimedeanIdeleCocycleHom_innerConjugation g w f
  rw [innerConjugationMap_two_apply] at h
  exact h.symm

variable [IsGalois F E]

/-- Archimedean idele invariants agree at any two places over the same base place. -/
theorem archimedeanIdeleInvariant_eq_of_comap_eq {w w' : InfinitePlace E}
    (h : w.comap (algebraMap F E) = w'.comap (algebraMap F E))
    (x : relativeIdeleCohomology F E 2) :
    archimedeanIdeleInvariant F w x = archimedeanIdeleInvariant F w' x := by
  obtain ⟨g, rfl⟩ := InfinitePlace.exists_smul_eq_of_comap_eq h
  have heq : infinitePlaceEquiv (g⁻¹).toRingEquiv w = g • w := by
    rw [infinitePlaceEquiv_eq_inv_smul, inv_inv]
  rw [← heq, archimedeanIdeleInvariant_infinitePlaceEquiv]

/-- The archimedean idele invariant indexed by a base place, using any lift of that place. -/
def archimedeanIdeleInvariantAt (v : InfinitePlace F) :
    relativeIdeleCohomology F E 2 →+ RationalModIntegers :=
  archimedeanIdeleInvariant F
    ((InfinitePlace.comap_surjective (k := F) (K := E) v).choose)

/-- Evaluation at any infinite place above the given base place. -/
theorem archimedeanIdeleInvariantAt_eq (v : InfinitePlace F) (w : InfinitePlace E)
    (hw : w.comap (algebraMap F E) = v) :
    archimedeanIdeleInvariantAt (E := E) v = archimedeanIdeleInvariant F w := by
  ext x
  apply archimedeanIdeleInvariant_eq_of_comap_eq
  exact (InfinitePlace.comap_surjective (k := F) (K := E) v).choose_spec.trans hw.symm

variable [NumberField F]

/-- The sum of archimedean idele invariants is independent of all choices above base places. -/
theorem archimedeanIdeleInvariantSum_eq
    (wi wi' : ∀ v : InfinitePlace F, InfinitePlacesAbove E v) :
    archimedeanIdeleInvariantSum wi = archimedeanIdeleInvariantSum wi' := by
  ext x
  simp only [archimedeanIdeleInvariantSum_apply]
  apply Finset.sum_congr rfl
  intro v _
  let := (wi v).2
  let := (wi' v).2
  exact archimedeanIdeleInvariant_eq_of_comap_eq
    ((InfinitePlace.LiesOver.comap_eq (wi v).1 v).trans
      (InfinitePlace.LiesOver.comap_eq (wi' v).1 v).symm) x

end Langlands.ClassField.Global
