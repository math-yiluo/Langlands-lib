import Langlands.ClassFieldTheory.Local.LocalInvariantFamilyLawsStatement
import Langlands.ClassFieldTheory.Local.ClosureInflationIndependenceProof
import Langlands.ClassFieldTheory.Local.UnramifiedBaseChangeProof
import Langlands.ClassFieldTheory.Local.UnramifiedInvariantBaseChangeProof

/-! # Restriction law of the local invariant family

Transport of relative `H²` commutes with restriction, and inflation along a
field isomorphism is transport. For a tower `F ⊆ E ⊆ M`, the two algebraic
closures are identified so that the chosen embedding of `M` over `E`
corresponds to an embedding of `M` over `F`; the base-change square for closure
inflation and the degree law of the absolute invariant then give the
restriction law.
-/

noncomputable section

namespace Langlands.ClassFieldTheory.Local

universe u

section Restriction

variable {K E M N : Type u} [Field K] [Field E] [Field M] [Field N]
  [Algebra K E] [Algebra K M] [Algebra E M] [IsScalarTower K E M]
  [Algebra K N] [Algebra E N] [IsScalarTower K E N]

/-- Transport of relative `H²` commutes with restriction to an intermediate
base field. -/
theorem relativeH2Equiv_relativeRestriction (e : M ≃ₐ[E] N)
    (x : relativeCohomology K M 2) :
    relativeH2Equiv e (relativeRestriction K E M 2 x) =
      relativeRestriction K E N 2 (relativeH2Equiv (e.restrictScalars K) x) := by
  induction x using groupCohomology.H2_induction_on with | h z =>
  rw [relativeH2Equiv_H2π, relativeRestriction, relativeRestriction,
    groupCohomology.H2π_comp_map_apply, groupCohomology.H2π_comp_map_apply,
    relativeH2Equiv_H2π]
  congr 1

end Restriction

section InflationEquiv

variable {K M L' M' : Type u} [Field K] [Field M] [Field L'] [Field M']
  [Algebra K M] [Algebra K L'] [Algebra K M'] [Algebra L' M'] [IsScalarTower K L' M']
  [Normal K L']

/-- Inflation along a field isomorphism compatible with two transports is
transport. -/
theorem relativeInflation_relativeH2Equiv (eL : M ≃ₐ[K] L') (eM : M ≃ₐ[K] M')
    (h : ∀ a : M, algebraMap L' M' (eL a) = eM a) (x : relativeCohomology K M 2) :
    relativeInflation K L' M' 2 (relativeH2Equiv eL x) = relativeH2Equiv eM x := by
  have hpull : ∀ s : Gal(M'/K),
      relativeAutPullback eL (AlgEquiv.restrictNormalHom L' s) = relativeAutPullback eM s := by
    intro s
    ext a
    change eL.symm ((s.restrictNormal L') (eL a)) = eM.symm (s (eM a))
    apply eL.injective
    apply (algebraMap L' M').injective
    rw [eL.apply_symm_apply, AlgEquiv.restrictNormal_commutes, h, h, eM.apply_symm_apply]
  induction x using groupCohomology.H2_induction_on with | h z =>
  rw [relativeH2Equiv_H2π, relativeInflation, groupCohomology.H2π_comp_map_apply,
    relativeH2Equiv_H2π]
  congr 1
  apply groupCohomology.cocycles₂_ext
  intro s t
  rw [relativeCocycleTransport_apply]
  change unitInclusionLinear L' M' (relativeCocycleTransport eL z
      (AlgEquiv.restrictNormalHom L' s, AlgEquiv.restrictNormalHom L' t)) = _
  rw [relativeCocycleTransport_apply, hpull, hpull]
  exact Units.ext (h _)

end InflationEquiv

open AbsoluteInvariantAssembly

/-- Actual relative restriction multiplies the relative invariants of the local
invariant family by the base-extension degree. -/
theorem localInvariantFamilyRestriction : LocalInvariantFamilyRestrictionStatement.{u} := by
  intro hEx p _ F E M _ _ _ _ _ _ _ _ _ _ _ x
  let ψ : AlgebraicClosure F.Carrier ≃ₐ[F.Carrier] AlgebraicClosure E.Carrier :=
    IsAlgClosure.equiv F.Carrier _ _
  let : Algebra (AlgebraicClosure F.Carrier) (AlgebraicClosure E.Carrier) :=
    ψ.toAlgHom.toRingHom.toAlgebra
  let : IsScalarTower F.Carrier (AlgebraicClosure F.Carrier) (AlgebraicClosure E.Carrier) :=
    IsScalarTower.of_algebraMap_eq (fun a => (ψ.commutes a).symm)
  let fE := closureEmbedding E.Carrier M
  let N := fE.fieldRange
  let g : M →ₐ[F.Carrier] AlgebraicClosure F.Carrier :=
    ψ.symm.toAlgHom.comp (fE.restrictScalars F.Carrier)
  let EM := g.fieldRange
  let : Algebra F.Carrier N :=
    ((algebraMap E.Carrier N).comp (algebraMap F.Carrier E.Carrier)).toAlgebra
  let : IsScalarTower F.Carrier E.Carrier N := IsScalarTower.of_algebraMap_eq' rfl
  have hImage : ∀ a : EM,
      algebraMap (AlgebraicClosure F.Carrier) (AlgebraicClosure E.Carrier)
        (algebraMap EM (AlgebraicClosure F.Carrier) a) ∈ N := by
    rintro ⟨_, m, rfl⟩
    exact ⟨m, (ψ.apply_symm_apply (fE m)).symm⟩
  let φ : EM →+* N :=
    ((algebraMap (AlgebraicClosure F.Carrier) (AlgebraicClosure E.Carrier)).comp
      (algebraMap EM (AlgebraicClosure F.Carrier))).codRestrict N hImage
  let : Algebra EM N := φ.toAlgebra
  let : IsScalarTower F.Carrier EM N := by
    apply IsScalarTower.of_algebraMap_eq
    intro b
    apply Subtype.ext
    change algebraMap E.Carrier (AlgebraicClosure E.Carrier)
        (algebraMap F.Carrier E.Carrier b) =
      ψ (algebraMap F.Carrier (AlgebraicClosure F.Carrier) b)
    rw [ψ.commutes, ← IsScalarTower.algebraMap_apply]
  have hComm : ∀ a : EM,
      algebraMap N (AlgebraicClosure E.Carrier) (algebraMap EM N a) =
        algebraMap (AlgebraicClosure F.Carrier) (AlgebraicClosure E.Carrier)
          (algebraMap EM (AlgebraicClosure F.Carrier) a) := fun _ => rfl
  have hCompat : ∀ a : M, algebraMap EM N (g.equivFieldRange a) =
      (fE.equivFieldRange.restrictScalars F.Carrier) a :=
    fun a => Subtype.ext (ψ.apply_symm_apply (fE a))
  have hR : (localInvariantFamily hEx p).relative F M x =
      localAbsoluteInvariant hEx F
        (closureInflation F.Carrier EM 2 (relativeH2Equiv g.equivFieldRange x)) := by
    rw [localInvariantFamily_relative, embeddedRelativeInvariant_apply,
      closureInflationTransportIndependence F.Carrier M EM
        (closureEmbedding F.Carrier M).fieldRange g.equivFieldRange
        (closureEmbedding F.Carrier M).equivFieldRange x]
  have hL : (localInvariantFamily hEx p).relative E M
      (relativeRestriction F.Carrier E.Carrier M 2 x) =
      localAbsoluteInvariant hEx E (closureInflation E.Carrier N 2
        (relativeH2Equiv fE.equivFieldRange
          (relativeRestriction F.Carrier E.Carrier M 2 x))) := rfl
  rw [hL, hR, relativeH2Equiv_relativeRestriction,
    ← relativeInflation_relativeH2Equiv g.equivFieldRange
      (fE.equivFieldRange.restrictScalars F.Carrier) hCompat,
    ← closureInflationBaseChangeCompatibility F.Carrier E.Carrier EM N hComm 2]
  exact descendedHom_restriction F hEx closureInflationTowerCompatibility
    unramifiedInvariantInflationCompatibility unramifiedBaseChangeStageExistence
    closureInflationBaseChangeCompatibility unramifiedInvariantBaseChangeCompatibility E _

end Langlands.ClassFieldTheory.Local
