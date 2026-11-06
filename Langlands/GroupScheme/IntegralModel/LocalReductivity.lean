import Langlands.GroupScheme.IntegralModel.LocalSmoothness
import Langlands.GroupScheme.Reductive.GenericSpreadingAssembly
import Langlands.GroupScheme.Reductive.BaseChange
import Langlands.BruhatTits.IntegralModels.RelativeComponent

/-! # Reductivity and relative components of the supplied good local model -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped ValuativeRel CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- A reductive group scheme is its own all-test relative identity component. -/
theorem isRelativeIdentityComponent_id_of_isReductive
    {S : Scheme.{u}} (H : GroupScheme S) (hH : IsReductive H) :
    IsRelativeIdentityComponent H (𝟙 H) := by
  refine ⟨?_, fun T x => ?_⟩
  · change IsOpenImmersion (𝟙 H.X.left)
    infer_instance
  · constructor
    · intro _ s
      let := (hH.isConnectedReductive_residueFiber s).connectedSpace
      change Set.range (RelativeIdentityComponent.residueFiberPoint H x s).left ⊆
        connectedComponent _
      rw [PreconnectedSpace.connectedComponent_eq_univ]
      exact Set.subset_univ _
    · intro _
      exact ⟨x, Category.comp_id x⟩

namespace IntegralModel

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of F))}
    (M : IntegralModel ↥𝒪[F] F G)

/-- Connected reductivity of the two actual fibres makes the original model
a reductive group scheme over the valuation ring. -/
theorem isReductive_of_reductive_localField
    (hG : IsConnectedReductive G)
    (hSpecial : IsConnectedReductive
      ((baseChange (Spec.algebraMap ↥𝒪[F] 𝓀[F])).obj M.group)) :
    IsReductive M.group := by
  let R := ↥𝒪[F]
  have hgeneric : IsConnectedReductive M.genericFibre := hG.of_iso M.genericIso
  have hgenericResidue :=
    genericResidueReductive_of_fractionFieldReductive R F M.group hgeneric
  have hclosed : (Spec.algebraMap R 𝓀[F]) (IsLocalRing.closedPoint 𝓀[F]) =
      IsLocalRing.closedPoint R := by
    apply PrimeSpectrum.ext
    change Ideal.comap (algebraMap R 𝓀[F]) (IsLocalRing.maximalIdeal 𝓀[F]) =
      IsLocalRing.maximalIdeal R
    rw [IsLocalRing.maximalIdeal_eq_bot]
    exact IsLocalRing.ker_residue (R := R)
  have hspecialResidue :=
    residueReductive_of_fieldReductive M.group (Spec.algebraMap R 𝓀[F]) hSpecial
  rw [hclosed] at hspecialResidue
  have hresidue : ∀ s : Spec (CommRingCat.of R),
      IsConnectedReductive
        ((baseChange ((Spec (CommRingCat.of R)).fromSpecResidueField s)).obj
          M.group) := by
    intro s
    rcases Langlands.AlgebraicGeometry.FlatReducedDvrConnectedness.point_eq_generic_or_closed
      R s with hs | hs
    · have hs' : s = genericPoint (Spec (CommRingCat.of R)) := by
        rw [genericPoint_eq_bot_of_affine]
        exact hs
      rw [hs']
      exact hgenericResidue
    · rw [hs]
      exact hspecialResidue
  refine ⟨M.isSmooth_of_reductive_localField hG hSpecial, M.affine, fun s => ?_⟩
  exact (fieldReductive_of_residueReductive M.group Set.univ
    (fun t _ => hresidue t) (geometricPoint _ s) (Set.mem_univ _)).isPseudoReductive

/-- Every actual scheme-theoretic fibre of the original good local model is
connected. No chosen neutral model is assumed. -/
theorem hasConnectedFibres_of_reductive_localField
    (hG : IsConnectedReductive G)
    (hSpecial : IsConnectedReductive
      ((baseChange (Spec.algebraMap ↥𝒪[F] 𝓀[F])).obj M.group)) :
    M.HasConnectedFibres := by
  intro s
  exact ((M.isReductive_of_reductive_localField hG hSpecial
    ).isConnectedReductive_residueFiber s).connectedSpace

/-- The supplied good local model itself supplies both the full and neutral
models, with their original generic identifications and the identity inclusion. -/
def relativeComponentData_of_reductive_localField
    (hG : IsConnectedReductive G)
    (hSpecial : IsConnectedReductive
      ((baseChange (Spec.algebraMap ↥𝒪[F] 𝓀[F])).obj M.group)) :
    Langlands.BruhatTits.IntegralModels.RelativeComponentModelData ↥𝒪[F] F G where
  full := M
  neutral := M
  full_smooth := M.isSmooth_of_reductive_localField hG hSpecial
  neutral_smooth := M.isSmooth_of_reductive_localField hG hSpecial
  neutral_connectedFibres := M.hasConnectedFibres_of_reductive_localField hG hSpecial
  inclusion := {
    hom := 𝟙 M.group
    generic_comm := by simp }
  isRelativeComponent := isRelativeIdentityComponent_id_of_isReductive M.group
    (M.isReductive_of_reductive_localField hG hSpecial)

end IntegralModel

end Langlands.GroupScheme
