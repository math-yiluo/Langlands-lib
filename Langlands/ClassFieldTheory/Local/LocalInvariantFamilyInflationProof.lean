import Langlands.ClassFieldTheory.Local.LocalInvariantFamilyLawsStatement
import Langlands.ClassFieldTheory.Local.ClosureInflationIndependenceProof

/-! # Inflation compatibility of the local invariant family

Transport of relative `H²` along field isomorphisms commutes with inflation
when the isomorphisms are compatible with the two field inclusions. A tower
`F ⊆ L ⊆ M` is placed in the algebraic closure through one embedding of `M`;
closure inflation along the image tower and independence of the embedding of
`L` then give the inflation law.
-/

noncomputable section

namespace Langlands.ClassFieldTheory.Local

universe u

section Naturality

variable {K L M L' M' : Type u} [Field K] [Field L] [Field M] [Field L'] [Field M']
  [Algebra K L] [Algebra K M] [Algebra L M] [IsScalarTower K L M] [Normal K L]
  [Algebra K L'] [Algebra K M'] [Algebra L' M'] [IsScalarTower K L' M'] [Normal K L']

/-- Normal restriction commutes with pulling automorphisms back along
isomorphisms compatible with the field inclusions. -/
theorem restrictNormalHom_relativeAutPullback (eL : L ≃ₐ[K] L') (eM : M ≃ₐ[K] M')
    (h : ∀ a : L, eM (algebraMap L M a) = algebraMap L' M' (eL a)) (s : Gal(M'/K)) :
    AlgEquiv.restrictNormalHom L (relativeAutPullback eM s) =
      relativeAutPullback eL (AlgEquiv.restrictNormalHom L' s) := by
  have h' : ∀ b : L', algebraMap L M (eL.symm b) = eM.symm (algebraMap L' M' b) := by
    intro b
    apply eM.injective
    rw [h, eL.apply_symm_apply, eM.apply_symm_apply]
  ext a
  apply (algebraMap L M).injective
  change algebraMap L M ((relativeAutPullback eM s).restrictNormal L a) =
    algebraMap L M (eL.symm ((s.restrictNormal L') (eL a)))
  rw [AlgEquiv.restrictNormal_commutes, h', relativeAutPullback_apply, h,
    ← AlgEquiv.restrictNormal_commutes s L' (eL a)]

/-- Transport of relative `H²` along compatible isomorphisms commutes with
inflation. -/
theorem relativeH2Equiv_relativeInflation (eL : L ≃ₐ[K] L') (eM : M ≃ₐ[K] M')
    (h : ∀ a : L, eM (algebraMap L M a) = algebraMap L' M' (eL a))
    (x : relativeCohomology K L 2) :
    relativeH2Equiv eM (relativeInflation K L M 2 x) =
      relativeInflation K L' M' 2 (relativeH2Equiv eL x) := by
  have key : ∀ a : Additive Lˣ, relativeUnitTransport eM (unitInclusionLinear L M a) =
      unitInclusionLinear L' M' (relativeUnitTransport eL a) :=
    fun a => Units.ext (h _)
  induction x using groupCohomology.H2_induction_on with | h z =>
  rw [relativeH2Equiv_H2π, relativeInflation, relativeInflation,
    groupCohomology.H2π_comp_map_apply, groupCohomology.H2π_comp_map_apply,
    relativeH2Equiv_H2π]
  congr 1
  apply groupCohomology.cocycles₂_ext
  intro s t
  rw [relativeCocycleTransport_apply]
  change relativeUnitTransport eM (unitInclusionLinear L M
      (z (AlgEquiv.restrictNormalHom L (relativeAutPullback eM s),
        AlgEquiv.restrictNormalHom L (relativeAutPullback eM t)))) =
    unitInclusionLinear L' M' (relativeCocycleTransport eL z
      (AlgEquiv.restrictNormalHom L' s, AlgEquiv.restrictNormalHom L' t))
  rw [restrictNormalHom_relativeAutPullback eL eM h, restrictNormalHom_relativeAutPullback eL eM h,
    relativeCocycleTransport_apply]
  exact key _

end Naturality

/-- The relative invariants of the local invariant family agree along actual
inflation. -/
theorem localInvariantFamilyInflation : LocalInvariantFamilyInflationStatement.{u} := by
  intro hEx p _ F L M _ _ _ _ _ _ _ _ _ _ _ x
  let fM := closureEmbedding F.Carrier M
  let g : L →ₐ[F.Carrier] AlgebraicClosure F.Carrier :=
    fM.comp (IsScalarTower.toAlgHom F.Carrier L M)
  have hle : g.fieldRange ≤ fM.fieldRange := by
    rintro _ ⟨a, rfl⟩
    exact ⟨algebraMap L M a, rfl⟩
  let : Algebra g.fieldRange fM.fieldRange := (IntermediateField.inclusion hle).toAlgebra
  let : IsScalarTower F.Carrier g.fieldRange fM.fieldRange :=
    IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower g.fieldRange fM.fieldRange (AlgebraicClosure F.Carrier) :=
    IsScalarTower.of_algebraMap_eq' rfl
  rw [localInvariantFamily_relative, localInvariantFamily_relative,
    embeddedRelativeInvariant_apply, embeddedRelativeInvariant_apply,
    closureInflationTransportIndependence F.Carrier L g.fieldRange
      (closureEmbedding F.Carrier L).fieldRange g.equivFieldRange
      (closureEmbedding F.Carrier L).equivFieldRange x,
    relativeH2Equiv_relativeInflation g.equivFieldRange fM.equivFieldRange
      (fun _ => rfl) x,
    closureInflationTowerCompatibility F.Carrier g.fieldRange fM.fieldRange 2]

end Langlands.ClassFieldTheory.Local
