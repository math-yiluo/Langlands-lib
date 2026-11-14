import Langlands.Geometry.Building.KPUnramifiedDoubledRootBlockDescent
import Langlands.Geometry.Building.KPUnramifiedRootFiberDepthComparison
import Langlands.Geometry.Building.KPUnramifiedComparisonLeviContainment

/-! # Reduction of the root comparison field to doubled-root depth models -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2000000

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct
open scoped CategoryTheory.MonObj ValuativeRel NNReal
open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace
open Langlands.GroupScheme.GaloisPointComparison
open Langlands.LocalGalois.Separable

namespace Langlands.Geometry.Building

private instance rootFieldReductionAffineHom {F : Type u} [Field F]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom] :
    IsAffineHom (baseChanged F (UnramifiedClosure F) G).X.hom := by
  change IsAffineHom
    (CategoryTheory.Limits.pullback.snd G.X.hom (baseMap F (UnramifiedClosure F)))
  infer_instance

namespace ParahoricBuildingData.UnramifiedComparisonTorus.ApartmentLift

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
    {P : ParahoricBuildingData G} {t : P.UnramifiedComparisonTorus}
    (L : t.ApartmentLift)

/-- Uniform upper fibre membership descends to the lower two-factor block,
for every root and nonnegative depth, without a separate root-group premise. -/
def HasRootFiberBlockDescent : Prop :=
  ∀ (y : P.Apartment) (a : relativeRoots P.i) (r : ℝ≥0) (g : rationalPoints G),
    rationalExtend F (UnramifiedClosure F) G g ∈
        L.buildingData.rootFiltrationSpan (L.e y) (L.rootFiber a) r →
      g ∈ P.apartment.filtrationBlock y (fun _ => (r : ℝ)) a.val

/-- The exact doubled-root model-existence proposition supplies block descent
at every nonnegative depth. -/
theorem hasRootFiberBlockDescent_of_doubledRootDepthModel
    (hP : P.SatisfiesApartmentAxioms)
    (hModel : UnramifiedDoubledRootDepthModelStatement.{u}) :
    L.HasRootFiberBlockDescent := by
  intro y a r g hg
  by_cases h2a : 2 • a.val ∈ relativeRoots P.i
  · let : Smooth G.X.hom := P.isConnectedReductive.smooth
    obtain ⟨U, q, hq, hqc, _, _⟩ :=
      RelativeRoot.subgroup_has_smooth_closed_representative
        P.isMaximalSplitTorus.isSplitSubtorus.1 P.i (2 • a.val) h2a.1
    obtain ⟨M, hM, hconn, hcompare⟩ :=
      hModel F G P hP t L y a h2a U q hq hqc (2 * r)
    have hmodel : L.IsDoubledRootDepthModelAt y a r q M := by
      intro w
      simpa only [scaledRootDepth, NNReal.coe_mul, NNReal.coe_ofNat] using hcompare w
    exact L.block_mem_rootFiber_of_doubledRootModel
      y a h2a U q hq hqc r M hM hconn hmodel g hg
  · exact L.block_mem_rootFiber_of_not_double y a h2a r g hg

/-- All seven root-comparison fields follow from the uniform fibre block
property, using a positive integral downstairs cocharacter. -/
theorem exists_rootComparison_of_rootFiberBlockDescent
    (hBlock : L.HasRootFiberBlockDescent) (a : relativeRoots P.i) :
    ∃ ν : V L.buildingData.S,
      P.IsUnramifiedRootComparison L.buildingData L.e a (L.rootFiber a) ν := by
  obtain ⟨d, hd, ζ, hζ⟩ :=
    P.isMaximalSplitTorus.isSplitSubtorus.1.exists_pairing_eq_pos a.property.1
  let v : V P.S := (1 : ℝ) ⊗ₜ[ℤ] ζ
  have hv : 0 < eval P.S a v := by
    dsimp [v]
    rw [one_mul, hζ]
    exact_mod_cast hd
  let ν : V L.buildingData.S :=
    descentCocharacterMap F (UnramifiedClosure F) t.f
      P.isMaximalSplitTorus.isSplitSubtorus.1 v
  refine ⟨ν, ?_⟩
  exact
    { closed := L.rootFiber_closed a
      pos := L.rootFiber_pos a v hv
      root_mem := L.root_mem_rootFiber a
      neg_mem := L.neg_mem_negativePairingRoots a v hv
      levi_mem := L.centralizer_mem_pairingLeviSpan_descent_tmul ζ
      filtration_mem := fun y r => L.filtration_mem_rootFiber y a r
      block_mem := fun y r g _ hg => hBlock y a r g hg }

end ParahoricBuildingData.UnramifiedComparisonTorus.ApartmentLift

/-- Conditional reduction of the exact root-field target to the substantive
doubled-root depth-model existence theorem. The premise is not proved here. -/
theorem unramifiedComparisonRootField_of_doubledRootDepthModel
    (hModel : UnramifiedDoubledRootDepthModelStatement.{u}) :
    UnramifiedComparisonRootFieldStatement.{u} := by
  intro F _ _ _ _ G _ P hP t L a
  obtain ⟨ν, hν⟩ := L.exists_rootComparison_of_rootFiberBlockDescent
    (L.hasRootFiberBlockDescent_of_doubledRootDepthModel hP hModel) a
  exact ⟨L.rootFiber a, ν, hν⟩

end Langlands.Geometry.Building
