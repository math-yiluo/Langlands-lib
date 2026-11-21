import Langlands.BaseChange.GlobalNormReciprocity
import Langlands.BaseChange.NormCharacterRestrictionMultiplicity
import Langlands.Global.AdelicFunctoriality.GaloisPlaceCount

/-! # Characters of the global norm quotient and their finite restrictions -/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

namespace Langlands.BaseChange

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open ClassField.Global ClassField.Global.FundamentalClass
open Global Global.AdelicFunctoriality
open scoped NumberField FiniteExtension

attribute [local instance] relativeGaloisTopology

variable {F E : Type u} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  [IsGalois F E]

/-- The index of the decomposition subgroup is the number of places over the lower place. -/
theorem decompositionHom_index_eq_card_placesAbove
    (v : Global.FinitePlace F) (w : FinitePlacesAbove E v) :
    (decompositionHom v w.1).range.index = Nat.card (FinitePlacesAbove E v) := by
  have hmul := (decompositionHom v w.1).range.index_mul_card
  have hcard := RelativeWeilGroup.card_range_decompositionHom v w.1
  change Nat.card (decompositionHom v w.1).range =
    Module.finrank (v.adicCompletion F) (w.1.adicCompletion E) at hcard
  have hdeg := card_mul_eq_finrank_of_forall (L := E) v
    (w.1.asIdeal.ramificationIdx (𝓞 F) * w.1.asIdeal.inertiaDeg (𝓞 F)) (fun q => by
      obtain ⟨τ, hτ⟩ := exists_finitePlaceEquiv_eq v w.1 q.1
      rw [← hτ, ramificationIdx_finitePlaceEquiv_algEquiv, inertiaDeg_finitePlaceEquiv_algEquiv])
  rw [hcard, IsGalois.card_aut_eq_finrank, localDegree_eq, ← hdeg, card_placesAbove,
    ← Nat.card_eq_fintype_card] at hmul
  have hpos : 0 < w.1.asIdeal.ramificationIdx (𝓞 F) * w.1.asIdeal.inertiaDeg (𝓞 F) := by
    rw [← localDegree_eq v w.1]
    exact Module.finrank_pos
  exact Nat.eq_of_mul_eq_mul_right hpos hmul

private def characterOfNormReciprocity (rec : IdeleClassGroup (𝓞 F) F →ₜ* (E ≃ₐ[F] E))
    (θ : (E ≃ₐ[F] E) →* ℂˣ) : HeckeCharacter F :=
  ⟨θ.comp rec.toMonoidHom, (continuous_of_discreteTopology (f := θ)).comp rec.continuous⟩

omit [IsGalois F E] in
private theorem normComp_eq_one_iff_exists_characterOfNormReciprocity
    (rec : IdeleClassGroup (𝓞 F) F →ₜ* (E ≃ₐ[F] E)) (hs : Function.Surjective rec)
    (hk : rec.toMonoidHom.ker = (ideleClassNorm (K := F) (L := E)).toMonoidHom.range)
    (χ : HeckeCharacter F) : χ.normComp (L := E) = 1 ↔ ∃ θ, characterOfNormReciprocity rec θ = χ := by
  constructor
  · intro hχ
    have hle : rec.toMonoidHom.ker ≤ χ.toMonoidHom.ker := by
      rw [hk]
      rintro _ ⟨a, rfl⟩
      exact DFunLike.congr_fun hχ a
    let θ := rec.toMonoidHom.liftOfSurjective hs ⟨χ.toMonoidHom, hle⟩
    refine ⟨θ, ContinuousMonoidHom.ext fun x => ?_⟩
    change θ (rec.toMonoidHom x) = χ.toMonoidHom x
    exact MonoidHom.liftOfRightInverse_comp_apply _ _ (Function.rightInverse_surjInv hs) _ x
  · rintro ⟨θ, rfl⟩
    apply ContinuousMonoidHom.ext
    intro a
    have ha : ideleClassNorm a ∈ rec.toMonoidHom.ker := hk.symm ▸ ⟨a, rfl⟩
    change θ (rec.toMonoidHom (ideleClassNorm a)) = 1
    rw [MonoidHom.mem_ker.mp ha, map_one]

/-- The characters of the global norm quotient form a family indexed by the character group of
`Gal(E/F)`. At every finite place their restrictions give all actual local norm characters,
with multiplicity the number of places above it. -/
def GlobalNormCharacterRestrictionStatement : Prop :=
  ∀ (F E : Type u) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    [IsGalois F E] [IsCyclic (E ≃ₐ[F] E)],
    ∃ χ : ((E ≃ₐ[F] E) →* ℂˣ) → HeckeCharacter F,
      Function.Injective χ ∧
      (∀ η : HeckeCharacter F, η.normComp (L := E) = 1 ↔ η ∈ Set.range χ) ∧
      Nat.card ((E ≃ₐ[F] E) →* ℂˣ) = Module.finrank F E ∧
      ∀ (v : Global.FinitePlace F) (w : FinitePlacesAbove E v)
        (κ : (v.adicCompletion F)ˣ →* ℂˣ),
        (IsNormTrivial (w.1.adicCompletion E) κ ↔
          ∃ θ, ((χ θ).finiteComponent v).toMonoidHom = κ) ∧
        (IsNormTrivial (w.1.adicCompletion E) κ →
          Nat.card {θ // ((χ θ).finiteComponent v).toMonoidHom = κ} =
            Nat.card (FinitePlacesAbove E v))

set_option maxHeartbeats 1000000 in
/-- Descend the finite Galois characters and apply finite abelian character duality to each
completion. -/
theorem globalNormCharacterRestriction : GlobalNormCharacterRestrictionStatement.{u} := by
  intro F E _ _ _ _ _ _ _
  obtain ⟨rec, hs, hk, hloc⟩ := globalNormReciprocity F E
  let : CommGroup (E ≃ₐ[F] E) := IsCyclic.commGroup
  let n := Monoid.exponent (E ≃ₐ[F] E)
  have hn : n ≠ 0 := Monoid.exponent_ne_zero_of_finite (G := E ≃ₐ[F] E)
  let : NeZero n := ⟨hn⟩
  let : HasEnoughRootsOfUnity ℂ n :=
    ⟨⟨_, Complex.isPrimitiveRoot_exp n hn⟩, rootsOfUnity.isCyclic ℂ n⟩
  refine ⟨characterOfNormReciprocity rec, ?_,
    normComp_eq_one_iff_exists_characterOfNormReciprocity rec hs hk, ?_, ?_⟩
  · intro θ θ' h
    apply MonoidHom.ext
    intro σ
    obtain ⟨x, rfl⟩ := hs σ
    exact DFunLike.congr_fun h x
  · exact (CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity (E ≃ₐ[F] E) ℂ).trans
      (IsGalois.card_aut_eq_finrank F E)
  · intro v w κ
    have hlocal : ∀ θ, ((characterOfNormReciprocity rec θ).finiteComponent v).toMonoidHom =
        θ.comp (GlobalNormReciprocity.finiteComponent rec v) := by
      intro θ
      rfl
    obtain ⟨hκ, hcard⟩ := normCharacterRestrictionMultiplicity
      (v.adicCompletion F) (w.1.adicCompletion E) (E ≃ₐ[F] E)
      (GlobalNormReciprocity.finiteComponent rec v) (hloc v w).1
    simp_rw [hlocal]
    refine ⟨hκ κ, fun h => (hcard κ h).trans ?_⟩
    rw [(hloc v w).2.1, decompositionHom_index_eq_card_placesAbove v w]

end Langlands.BaseChange
