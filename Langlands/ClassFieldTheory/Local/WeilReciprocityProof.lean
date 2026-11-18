import Langlands.ClassFieldTheory.Local.WeilReciprocityExistenceProof
import Langlands.ClassFieldTheory.Local.FiniteArtinSystemUniquenessProof
import Langlands.ClassFieldTheory.Local.UnitFiltrationConductor

/-! # Actual Weil reciprocity and its character comparisons -/

noncomputable section

namespace Langlands.LocalClassField

open Weil.Local

universe u

private theorem weilReciprocityCompletion : WeilReciprocityCompletion.{u} := by
  intro p hp F T e he
  let := T.topology
  obtain ⟨c, hc, hunique⟩ :=
    (profiniteReciprocityCompletion p F T
      (candidateGaloisHom T (localResidueDegree F) e) he.2).2
  refine ⟨c, ContinuousMonoidHom.ext hc, ?_⟩
  intro c' hc'
  exact hunique c' (DFunLike.congr_fun hc')

private theorem weilReciprocityInertiaImage : WeilReciprocityInertiaImage.{u} := by
  intro p hp F T e he
  let := T.topology
  ext a
  obtain ⟨w, rfl⟩ := e.surjective a
  have hmem :
      e w ∈ (WeilQuotients.inertia (localResidueDegree F)).map e.toMonoidHom ↔
        w ∈ WeilQuotients.inertia (localResidueDegree F) :=
    Subgroup.mem_map_iff_mem (f := e.toMonoidHom) e.injective
  rw [hmem, T.mem_unitSubgroup_iff_orderHom]
  change WeilQuotients.degree (localResidueDegree F) w = 1 ↔ T.orderHom (e w) = 1
  rw [show T.orderHom (e w) = WeilQuotients.degree (localResidueDegree F) w from
    DFunLike.congr_fun he.1 w]

section Characters

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{u} p) (T : F.TopologicalData)
  (e : WeilReciprocityCandidate T (localResidueDegree F))

private theorem candidate_projection_surjective :
    Function.Surjective (fun w : localWeilGroup F =>
      e (WeilQuotients.projection (localResidueDegree F) w)) := by
  let := T.topology
  exact e.surjective.comp QuotientGroup.mk_surjective

private theorem order_on_candidate_projection (he : GeometricWeilReciprocityRelation F T e)
    (w : localWeilGroup F) :
    T.ord (e (WeilQuotients.projection (localResidueDegree F) w) : F.Carrier) =
      localDegreeInt F w := by
  have h : T.orderHom (e (WeilQuotients.projection (localResidueDegree F) w)) =
      localDegree F w :=
    DFunLike.congr_fun he.1 (WeilQuotients.projection (localResidueDegree F) w)
  exact congrArg Multiplicative.toAdd h

private theorem character_on_candidate_projection
    (χ : localWeilGroup F →ₜ* ℂˣ) (w : localWeilGroup F) :
    weilCandidateCharacterEquiv T (localResidueDegree F) e χ
      (e (WeilQuotients.projection (localResidueDegree F) w)) = χ w := by
  let := T.topology
  change abelianizationLift χ (e.symm (e (WeilQuotients.projection (localResidueDegree F) w))) = _
  rw [e.symm_apply_apply]
  rfl

end Characters

private theorem weilReciprocityUnramifiedCharacters : WeilReciprocityUnramifiedCharacters.{u} := by
  intro p hp F T e he
  refine ⟨?_, ?_⟩
  · intro χ
    let projection := WeilQuotients.projection (localResidueDegree F)
    let f := e.toMonoidHom.comp projection.toMonoidHom
    have himage : (localInertia F).map f = T.unitSubgroup := by
      simpa only [WeilQuotients.inertia_eq_image, Subgroup.map_map, f, projection, localInertia]
        using weilReciprocityInertiaImage p F T e he
    have hunit (a : F.Carrierˣ) :
        a ∈ T.unitSubgroup ↔ T.discreteValuation (a : F.Carrier) = 1 := by
      rw [← T.unitFiltration_zero, T.unitFiltration_eq_principalUnits, T.mem_principalUnits_zero]
    constructor
    · intro h a ha
      have hmem : a ∈ (localInertia F).map f := himage.symm ▸ (hunit a).mpr ha
      obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.mp hmem
      exact (character_on_candidate_projection F T e χ w).trans (h w hw)
    · intro h w hw
      have hmem : f w ∈ T.unitSubgroup := himage ▸ Subgroup.mem_map_of_mem f hw
      exact (character_on_candidate_projection F T e χ w).symm.trans (h _ ((hunit _).mp hmem))
  · intro z a
    obtain ⟨w, rfl⟩ := candidate_projection_surjective F T e a
    rw [character_on_candidate_projection, order_on_candidate_projection F T e he]
    rfl

private theorem weilReciprocityUnramifiedTwists : WeilReciprocityUnramifiedTwists.{u} := by
  intro p hp F T e he χ z a
  obtain ⟨w, rfl⟩ := candidate_projection_surjective F T e a
  rw [character_on_candidate_projection, character_on_candidate_projection,
    ContinuousMonoidHom.mul_apply, order_on_candidate_projection F T e he]
  rfl

private theorem weilReciprocityNormCharacter : WeilReciprocityNormCharacter.{u} := by
  intro p hp F T e he a
  obtain ⟨w, rfl⟩ := candidate_projection_surjective F T e a
  rw [character_on_candidate_projection, localNormCharacter_apply,
    T.normalizedAbs_of_ne_zero (Units.ne_zero _), order_on_candidate_projection F T e he,
    FiniteArtinSystemUniqueness.residueCardinality_eq_canonical F T,
    Complex.ofReal_zpow, Complex.ofReal_natCast]

/-- Actual geometric local Weil reciprocity, its unique completion comparison,
and transport of inertia, unramified characters, twists and the norm character. -/
theorem weilReciprocityTheorems : WeilReciprocityTheorems.{u} :=
  ⟨geometricWeilReciprocityExistenceUniqueness, weilReciprocityCompletion,
    weilReciprocityInertiaImage, weilReciprocityUnramifiedCharacters,
    weilReciprocityUnramifiedTwists, weilReciprocityNormCharacter⟩

end Langlands.LocalClassField
