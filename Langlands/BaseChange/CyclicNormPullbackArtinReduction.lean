import Langlands.BaseChange.CuspidalSigmaLiftConductorRankOne
import Langlands.LocalFactor.Ramification.CharacterConductorSum

/-!
# Artin-conductor reduction of the cyclic norm character identity

Simultaneous finite Artin presentations turn the norm-pullback comparison
into the sum of character conductors on an abelian Galois quotient.
-/

noncomputable section

namespace Langlands.BaseChange

open HarmonicAnalysis (Quasicharacter)
open Ramification
open scoped BigOperators Classical

universe u v uV uW

/-- Actual principal-unit conductor comparisons in a common finite Artin
presentation, with the two ramification identities needed for the tower. -/
structure CyclicNormPullbackArtinData {F : Type u} [Field F] [ValuativeRel F]
    [TopologicalSpace F] [IsNonarchimedeanLocalField F] {E : Type v} [Field E]
    [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
    (χ : Quasicharacter F) (η : Quasicharacter E) (f d : ℕ) (X : Finset (Fˣ →* ℂˣ)) where
  G : Type (max u v)
  R : Type (max u v)
  [commGroup : CommGroup G]
  [finiteGroup : Finite G]
  [commRing : CommRing R]
  [localRing : IsLocalRing R]
  [noetherianRing : IsNoetherianRing R]
  [action : MulSemiringAction G R]
  [faithfulAction : FaithfulSMul G R]
  H : Subgroup G
  character : G →* ℂˣ
  indices : X ≃ (CommGroup.subgroupOrderIsoSubgroupMonoidHom G ℂ H).ofDual
  twists : X → Quasicharacter F
  twistCharacter (κ : X) : (twists κ).toMonoidHom = κ.val * χ.toMonoidHom
  twistConductor (κ : X) : ((LocalFieldData.ofInstances F).multiplicativeConductor (twists κ) : ℚ) =
    artinConductor R G (characterRepresentation (character * (indices κ).val))
  restrictionConductor : ((LocalFieldData.ofInstances E).multiplicativeConductor η : ℚ) =
    artinConductor R H (characterRepresentation (character.comp H.subtype))
  residueDegree : (f : ℚ) =
    (H.index : ℚ) * Nat.card (lowerGroup R H 0) / Nat.card (lowerGroup R G 0)
  cutoff : ℕ
  cutoff_spec : ∀ i ≥ cutoff, lowerGroup R G i = ⊥
  differentOrderSum : (∑ i ∈ Finset.range cutoff,
      ((Nat.card (lowerGroup R G i) : ℚ) - Nat.card (lowerGroup R H i))) =
    (Nat.card (lowerGroup R H 0) : ℚ) * d

/-- The finite Artin presentation required for every local cyclic norm pullback. -/
def CyclicNormPullbackArtinDataStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] [CharZero F]
    (E : Type v) [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E] [Algebra F E] [IsModuleTopology F E]
    (σ : E ≃ₐ[F] E) (l : ℕ), IsCyclicAlgebra σ l →
    ∀ (χ : Quasicharacter F) (η : Quasicharacter E),
      η.toMonoidHom = χ.toMonoidHom.comp (Units.map (Algebra.norm F : E →* F)) →
    ∀ f d : ℕ, IsResidueDegree F E f → IsDifferentExponent F E d →
    ∀ X : Finset (Fˣ →* ℂˣ), (∀ κ, κ ∈ X ↔ IsNormTrivial E κ) →
      Nonempty (CyclicNormPullbackArtinData χ η f d X)

/-- The finite Artin presentation implies the local norm pullback formula. -/
theorem cyclicNormPullbackConductor_of_artinData
    (h : CyclicNormPullbackArtinDataStatement.{u, v}) : CyclicNormPullbackConductorStatement.{u, v} := by
  intro F _ _ _ _ _ E _ _ _ _ _ _ σ l hcyc χ η hnorm f d hf hd X hX
  obtain ⟨D⟩ := h F E σ l hcyc χ η hnorm f d hf hd X hX
  let := D.commGroup
  let := D.finiteGroup
  let := D.commRing
  let := D.localRing
  let := D.noetherianRing
  let := D.action
  let := D.faithfulAction
  let Q := (CommGroup.subgroupOrderIsoSubgroupMonoidHom D.G ℂ D.H).ofDual
  let : Fintype Q := Fintype.ofFinite Q
  let TF := LocalFieldData.ofInstances F
  let TE := LocalFieldData.ofInstances E
  let a (κ : Fˣ →* ℂˣ) : ℕ :=
    if hκ : κ ∈ X then TF.multiplicativeConductor (D.twists ⟨κ, hκ⟩) else 0
  refine ⟨a, fun κ hκ => ⟨D.twists ⟨κ, hκ⟩, D.twistCharacter ⟨κ, hκ⟩, ?_⟩, ?_⟩
  · simp [a, hκ, TF]
  · have hsum : (∑ κ ∈ X, (a κ : ℚ)) = ∑ κ : Q,
        artinConductor D.R D.G (characterRepresentation (D.character * κ.val)) := by
      rw [← Finset.sum_coe_sort]
      apply Fintype.sum_equiv D.indices
      intro κ
      simpa only [a, dite_eq_left κ.property] using D.twistConductor κ
    have hArtin : (∑ κ : Q,
        artinConductor D.R D.G (characterRepresentation (D.character * κ.val))) =
        (f : ℚ) * ((TE.multiplicativeConductor η : ℚ) + (d : ℚ)) := by
      rw [sum_artinConductor_twists_trivial_on D.R D.H D.character,
        sum_artinConductor_trivial_on D.R D.H D.cutoff D.cutoff_spec,
        D.differentOrderSum, ← D.restrictionConductor]
      rw [D.residueDegree]
      ring
    exact_mod_cast hsum.trans hArtin

/-- Given the pointwise character identity and finite Artin data, the rank-one
case of the exact conductor statement follows. -/
def CuspidalSigmaLiftConductorRankOneArtinReductionStatement : Prop :=
  SigmaLiftCharacterIdentityStatement.{u, v, uV, uW} →
    CyclicNormPullbackArtinDataStatement.{u, v} →
    CuspidalSigmaLiftConductorRankOneStatement.{u, v, uV, uW}

theorem cuspidalSigmaLiftConductorRankOneArtinReduction :
    CuspidalSigmaLiftConductorRankOneArtinReductionStatement.{u, v, uV, uW} :=
  fun hShintani hArtin => cuspidalSigmaLiftConductorRankOneReduction hShintani
    (cyclicNormPullbackConductor_of_artinData hArtin)

end Langlands.BaseChange
