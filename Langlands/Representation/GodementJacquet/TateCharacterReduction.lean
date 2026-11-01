import Langlands.Representation.Smooth.Schur.Proof
import Langlands.Representation.RankinSelberg.RankOneCharacterReductionProof

/-!
# Actual character models for admissible irreducible GL₁ representations

Admissible Schur supplies the scalar action. Irreducibility then makes the
span of any nonzero vector the whole carrier.
-/

noncomputable section

namespace Langlands.GodementJacquet

open HarmonicAnalysis GeneralLinear

universe uF uV

variable {F : Type uF} [Field F] [TopologicalSpace F]
  [IsTopologicalGroup (Langlands.GeneralLinear 1 F)]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- Every actual admissible irreducible GL₁ representation is equivalent to
the scalar representation of a continuous quasicharacter. -/
theorem exists_tateCharacterModel
    (σ : Representation ℂ (Langlands.GeneralLinear 1 F) V)
    (ha : IsAdmissible σ) (hi : σ.IsIrreducible) :
    ∃ χ : Quasicharacter F,
      Nonempty (σ.Equiv (RankinSelberg.rankOneCharacter (χ : Fˣ →* ℂˣ))) := by
  classical
  let := hi
  let : Nontrivial V :=
    IsSimpleModule.nontrivial (MonoidAlgebra ℂ (Langlands.GeneralLinear 1 F)) σ.asModule
  obtain ⟨c, ⟨hc, hact⟩, -⟩ := admissibleSchur_centralCharacter σ ha hi
  let χ₀ : Fˣ →* ℂˣ := c.comp scalarToCenter
  have hχ₀ : Continuous χ₀ := by
    exact hc.continuous.comp
      ((scalarContinuous (R := F) (n := 1)).continuous.subtype_mk
        (fun a => (scalarToCenter a).property))
  let χ : Quasicharacter F := ⟨χ₀, hχ₀⟩
  have scalar_act (g : Langlands.GeneralLinear 1 F) (v : V) :
      σ g v = (χ (determinant g) : ℂ) • v := by
    have h := hact (scalarToCenter (determinant g)) v
    change σ (scalar (determinant g)) v = (χ (determinant g) : ℂ) • v at h
    rwa [RankinSelberg.scalar_determinant_rankOne] at h
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  let S : Subrepresentation σ :=
    { toSubmodule := ℂ ∙ v
      apply_mem_toSubmodule := fun g x hx => by
        rw [scalar_act]
        exact Submodule.smul_mem _ _ hx }
  have hS : S = ⊤ := by
    refine (hi.eq_bot_or_eq_top S).resolve_left fun h => hv ?_
    have hmem : v ∈ S.toSubmodule := Submodule.mem_span_singleton_self v
    rw [h] at hmem
    exact (Submodule.mem_bot ℂ).mp hmem
  have hspan : (ℂ ∙ v) = ⊤ := congrArg Subrepresentation.toSubmodule hS
  let L : V ≃ₗ[ℂ] ℂ :=
    ((LinearEquiv.toSpanNonzeroSingleton ℂ V v hv).trans
      (LinearEquiv.ofTop _ hspan)).symm
  refine ⟨χ, ⟨Representation.Equiv.mk L fun g => ?_⟩⟩
  apply LinearMap.ext
  intro x
  change L (σ g x) =
    (χ (determinant g) : ℂ) • (1 : Module.End ℂ ℂ) (L x)
  rw [scalar_act, map_smul, Module.End.one_apply]

/-- A concrete continuous character model of the actual carrier, with no
Whittaker, dimension, or central-character premise. -/
def tateCharacterModel
    (σ : Representation ℂ (Langlands.GeneralLinear 1 F) V)
    (ha : IsAdmissible σ) (hi : σ.IsIrreducible) :
    Σ χ : Quasicharacter F,
      σ.Equiv (RankinSelberg.rankOneCharacter (χ : Fˣ →* ℂˣ)) :=
  ⟨Classical.choose (exists_tateCharacterModel σ ha hi),
    Classical.choice (Classical.choose_spec (exists_tateCharacterModel σ ha hi))⟩

end Langlands.GodementJacquet
