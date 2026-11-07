import Langlands.Representation.Conductor.RankOne
import Langlands.Representation.GodementJacquet.TateCharacterReduction

/-!
# The rank-one newvector line

For an admissible irreducible complex representation of GL₁ over an arbitrary
nonarchimedean local field, the first nonzero fixed space is explicitly linearly
equivalent to the complex scalars. This does not identify an epsilon exponent.
-/

noncomputable section

namespace Langlands.Conductor

universe uF uV

variable (F : Type uF) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {V : Type uV} [AddCommGroup V] [Module ℂ V] [Nontrivial V]

/-- Coordinates on the actual first fixed space of an admissible irreducible
rank-one representation. Existence of the finite level is proved from smoothness. -/
def rankOneNewvectorLineEquiv
    (π : Representation ℂ (Langlands.GeneralLinear 1 F) V)
    (ha : IsAdmissible π) (hi : π.IsIrreducible) :
    levelFixedVectors π (rankOneConductor F π ha.1) ≃ₗ[ℂ] ℂ := by
  let e : V ≃ₗ[ℂ] ℂ := (GodementJacquet.tateCharacterModel π ha hi).2.toLinearEquiv
  let S := levelFixedVectors π (rankOneConductor F π ha.1)
  let L : S →ₗ[ℂ] ℂ := e.toLinearMap.comp S.subtype
  have hinj : Function.Injective L := e.injective.comp Subtype.val_injective
  let v := rankOneNewvector F π ha.1
  let w : S := ⟨v.val, v.property.1⟩
  have hw : w ≠ 0 := fun h => v.property.2 (congrArg Subtype.val h)
  have hLw : L w ≠ 0 := fun h => hw (hinj (by simpa using h))
  refine LinearEquiv.ofBijective L ⟨hinj, ?_⟩
  intro z
  refine ⟨(z / L w) • w, ?_⟩
  rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ hLw]

/-- The first nonzero rank-one fixed space has complex dimension one. -/
theorem finrank_rankOne_newvectorSpace
    (π : Representation ℂ (Langlands.GeneralLinear 1 F) V)
    (ha : IsAdmissible π) (hi : π.IsIrreducible) :
    Module.finrank ℂ (levelFixedVectors π (rankOneConductor F π ha.1)) = 1 := by
  rw [(rankOneNewvectorLineEquiv F π ha hi).finrank_eq]
  exact Module.finrank_self ℂ

/-- The fixed-vector part of the rank-one conductor theorem, without an
assumed finite level or any dimension premise. -/
theorem exists_rankOne_newvectorLine
    (π : Representation ℂ (Langlands.GeneralLinear 1 F) V)
    (ha : IsAdmissible π) (hi : π.IsIrreducible) :
    ∃ m : ℕ, IsNewvectorConductor π m ∧
      Module.finrank ℂ (levelFixedVectors π m) = 1 := by
  exact ⟨rankOneConductor F π ha.1,
    newvectorConductor_spec π (hasNewvectorLevel_rankOne F π ha.1),
    finrank_rankOne_newvectorSpace F π ha hi⟩

end Langlands.Conductor
