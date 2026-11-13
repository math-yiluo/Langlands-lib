import Langlands.GroupScheme.IntegralModelReduction
import Langlands.GroupScheme.IntegralModel.UnramifiedModelDescent
import Langlands.GroupScheme.IntegralModel.Iso
import Langlands.GroupScheme.RelativeIdentityComponent.BaseChange
import Langlands.GroupScheme.Descent.ValuationIntegerCover

/-! # Connected fibres under unramified model descent -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped ValuativeRel CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- Connectedness of every actual residue fibre is reflected by a surjective base change. -/
theorem connectedFibres_of_surjective_baseChange {S S' : Scheme.{u}}
    (b : S' ⟶ S) [Surjective b] (H : GroupScheme S)
    (h : ∀ s' : S', ConnectedSpace (((GroupScheme.baseChange b).obj H).X.hom.fiber s')) :
    ∀ s : S, ConnectedSpace (H.X.hom.fiber s) := by
  intro s
  obtain ⟨s', rfl⟩ := b.surjective s
  let : ConnectedSpace (((Over.pullback b).obj H.X).hom.fiber s') := h s'
  let : Surjective (Spec.map (b.residueFieldMap s')) :=
    ⟨Function.surjective_to_subsingleton _⟩
  let q := RelativeIdentityComponent.fiberComparison b H.X s'
  have : Surjective q := MorphismProperty.of_isPullback
    (RelativeIdentityComponent.fiberComparison_isPullback b H.X s').flip inferInstance
  exact q.surjective.connectedSpace q.continuous

/-- An actual group-scheme isomorphism transports connectedness of all residue fibres. -/
theorem connectedFibres_of_iso {S : Scheme.{u}} {H H' : GroupScheme S}
    (e : H ≅ H') (h : ∀ s : S, ConnectedSpace (H'.X.hom.fiber s)) :
    ∀ s : S, ConnectedSpace (H.X.hom.fiber s) := by
  intro s
  let e' := (Grp.forget (Over S)).mapIso e
  let e'' := (Over.forget _).mapIso ((Over.pullback (S.fromSpecResidueField s)).mapIso e')
  exact e''.hom.homeomorph.connectedSpace_iff.mpr (h s)

namespace IntegralModel

variable {R K : Type u} [CommRing R] [IsDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K] [IsLocalRing R]
  {G : GroupScheme (Spec (CommRingCat.of K))} (M : IntegralModel R K G)

/-- The usual special fibre and the canonical scheme fibre at the closed point
have the same topology, with the actual projections to the model. -/
def specialFibreHomeomorphClosedFibre :
    M.specialFibre.X.left ≃ₜ M.group.X.hom.fiber (IsLocalRing.closedPoint R) := by
  let b := residueBaseMap R
  have : IsClosedImmersion b :=
    IsClosedImmersion.spec_of_surjective _ (IsLocalRing.residue_surjective (R := R))
  let q := pullback.fst M.group.X.hom b
  have hr : Set.range b = {IsLocalRing.closedPoint R} := by
    ext x
    constructor
    · rintro ⟨z, rfl⟩
      exact IsLocalRing.PrimeSpectrum.comap_residue R z
    · rintro rfl
      exact ⟨IsLocalRing.closedPoint (IsLocalRing.ResidueField R),
        IsLocalRing.PrimeSpectrum.comap_residue R _⟩
  have hq : Set.range q = M.group.X.hom ⁻¹' {IsLocalRing.closedPoint R} := by
    rw [Scheme.Pullback.range_fst, hr]
  exact q.isEmbedding.toHomeomorph |>.trans
    ((Homeomorph.setCongr hq).trans (M.group.X.hom.fiberHomeo _).symm)

/-- Connected fibres give connectedness of the full actual special fibre. -/
theorem hasConnectedSpecialFibre_of_hasConnectedFibres (h : M.HasConnectedFibres) :
    M.HasConnectedSpecialFibre :=
  M.specialFibreHomeomorphClosedFibre.connectedSpace_iff.mpr
    (h (IsLocalRing.closedPoint R))

section Unramified

open Langlands.LocalGalois.Separable GaloisPointComparison

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  (M : IntegralModel ↥𝒪[F] F G)

local instance connectedFibreDescentIntegerAlgebra :
    Algebra ↥𝒪[F] (fixedFieldIntegers F) :=
  Valuation.HasExtension.instAlgebraInteger
    (vR := ValuativeRel.valuation F) (vA := fixedFieldValuation F)

/-- Connected fibres of the actual maximal-unramified base change descend. -/
theorem hasConnectedFibres_of_baseChangeUnramified
    (h : M.baseChangeUnramified.HasConnectedFibres) : M.HasConnectedFibres := by
  let : Surjective (Spec.algebraMap ↥𝒪[F] (fixedFieldIntegers F)) :=
    (valuationInteger_fpqc (ValuativeRel.valuation F) (fixedFieldValuation F)).1
  exact connectedFibres_of_surjective_baseChange _ M.group h

/-- Connected fibres of a supplied model isomorphic to the actual unramified
base change imply connectedness of the original model's full special fibre. -/
theorem hasConnectedSpecialFibre_of_unramified_iso
    {N : IntegralModel (fixedFieldIntegers F) (inertiaFixedField F)
      (baseChanged F (inertiaFixedField F) G)}
    (e : M.baseChangeUnramified.Iso N (CategoryTheory.Iso.refl _))
    (h : N.HasConnectedFibres) : M.HasConnectedSpecialFibre := by
  apply M.hasConnectedSpecialFibre_of_hasConnectedFibres
  apply M.hasConnectedFibres_of_baseChangeUnramified
  exact connectedFibres_of_iso e.iso h

end Unramified
end IntegralModel
end Langlands.GroupScheme
