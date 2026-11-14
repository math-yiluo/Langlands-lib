import Langlands.GroupScheme.IntegralModel.SeparableIsoDepth
import Langlands.Geometry.Building.RootFieldVectorIsoOfOrbit
import Langlands.Geometry.Building.AdditiveRootCoordinateValuation

/-! # Actual root-orbit field depth models and their exact point images -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.FieldTheory Langlands.Geometry.Building

namespace Langlands.GroupScheme.IntegralModel

variable (k L : Type u) [Field k] [Field L] [Algebra k L]
    [FiniteDimensional k L] [IsGalois k L]
    {S T : CommGroupScheme (Spec (CommRingCat.of k))}
    {G : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom] [Smooth G.X.hom]
    (f : S ⟶ T) (j : T.toGrp ⟶ G)
    (hG : IsConnectedReductive G) (hj : IsMaximalTorus j) (hS : IsSplitTorus S.toGrp)
    (hT : IsSplitTorus
      ((CommGroupScheme.baseChange (algebraBaseMap k L)).obj T).toGrp)
    {a : characterLattice S} (ha : a ∈ relativeRoots (CommGroupScheme.groupHom f ≫ j))
    (hhigh : RelativeRoot.HasNoHigherRoots (CommGroupScheme.groupHom f ≫ j) a)
    (β : roots
      (T := (CommGroupScheme.baseChange (algebraBaseMap k L)).obj T)
      (G := (GroupScheme.baseChange (algebraBaseMap k L)).obj G)
      ((GroupScheme.baseChange (algebraBaseMap k L)).map j))

attribute [local instance] rootsGaloisAction

variable
    (horbit : MulAction.orbit (L ≃ₐ[k] L) β = rootRestrictionFiber k L j f a)
    {U : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom U.X.hom]
    {q : U ⟶ G} (hq : (RelativeRoot.subgroup (CommGroupScheme.groupHom f ≫ j) a).IsRepresentedBy q)
    (b : Module.Basis (Fin (Module.finrank k (rootOrbitField k L j β))) k
      (rootOrbitField k L j β))
    (v : Valuation k (WithZero (Multiplicative ℤ)))
    (hH : HenselianLocalRing v.valuationSubring) (hv : Function.Surjective v)

local instance : Algebra.IsSeparable k (rootOrbitField k L j β) :=
  Algebra.isSeparable_tower_bot_of_isSeparable k (rootOrbitField k L j β) L

/-- An integral model on the actual root representative, with generic
identification given by its actual Galois root-orbit field. -/
def rootFieldDepthModelOfOrbit (r : ℝ) : IntegralModel v.valuationSubring k U :=
  separableIsoDepthModel v hH (rootOrbitField k L j β) hv b
    (rootFieldVectorIsoOfOrbit k L f j hG hj hS hT ha hhigh β horbit hq b) r

theorem rootFieldDepthModelOfOrbit_isSmooth (r : ℝ) :
    (rootFieldDepthModelOfOrbit k L f j hG hj hS hT ha hhigh β horbit hq b v hH hv r).IsSmooth := by
  change Smooth (VectorGroup.groupScheme (CommRingCat.of v.valuationSubring)
    (Module.finrank k (rootOrbitField k L j β))).X.hom
  exact VectorGroup.smooth _ _

theorem rootFieldDepthModelOfOrbit_hasGeometricallyConnectedFibres (r : ℝ) :
    (rootFieldDepthModelOfOrbit k L f j hG hj hS hT ha hhigh β horbit hq b v hH hv r
      ).HasGeometricallyConnectedFibres := by
  change GeometricallyConnected (VectorGroup.groupScheme (CommRingCat.of v.valuationSubring)
    (Module.finrank k (rootOrbitField k L j β))).X.hom
  exact VectorGroup.geometricallyConnected _ _

/-- The actual deeper-to-shallower lattice map extends the identity on
this very root representative. -/
def rootFieldDepthTransitionOfOrbit (r s : ℝ) (hrs : r ≤ s) :
    (rootFieldDepthModelOfOrbit k L f j hG hj hS hT ha hhigh β horbit hq b v hH hv s).Hom
      (rootFieldDepthModelOfOrbit k L f j hG hj hS hT ha hhigh β horbit hq b v hH hv r)
        (𝟙 _) :=
  separableIsoDepthTransition _ _ _ _ _ _ r s hrs

/-- Every generic-identity extension between these actual root-field
models has smooth connected unipotent special-fibre kernel. -/
theorem rootFieldDepthModelOfOrbit_kernel_properties (r s : ℝ) (hrs : r ≤ s)
    (φ :
      (rootFieldDepthModelOfOrbit k L f j hG hj hS hT ha hhigh β horbit hq b v hH hv s).Hom
        (rootFieldDepthModelOfOrbit k L f j hG hj hS hT ha hhigh β horbit hq b v hH hv r)
          (𝟙 _)) :
    Smooth (kernel φ.specialFibreMap).X.hom ∧
      ConnectedSpace (kernel φ.specialFibreMap).X.left ∧
        IsUnipotent (kernel φ.specialFibreMap) :=
  separableIsoDepthModel_kernel_properties _ _ _ _ _ _ r s hrs φ

variable [IsAffine T.toGrp.X.left] [IsAffine S.toGrp.X.left]
    (hcent : (torusCentralizer (CommGroupScheme.groupHom f ≫ j)).IsRepresentedBy j)
    (hβ : β ∈ rootRestrictionFiber k L j f a)

/-- Membership in the actual model is the exact root-field valuation bound
for the published rational coordinates. -/
theorem rootFieldDepthModelOfOrbit_mem_integralPoints (r : ℝ) (g : rationalPoints U) :
    g ∈ (rootFieldDepthModelOfOrbit k L f j hG hj hS hT ha hhigh β horbit hq b v hH hv r
      ).integralPoints ↔
      (r : WithTop ℝ) ≤ additiveRootValue
        (henselianSeparableAddValuation v hH (rootOrbitField k L j β))
        (rootFieldCoordinatesOfOrbit k L f j hG hj hS hcent hT ha hhigh β hβ horbit).equiv
        (rationalPoints.map q g) := by
  rw [rootFieldDepthModelOfOrbit, separableIsoDepthModel_mem_integralPoints,
    mem_henselianSeparableDepthLattice]
  change (r : WithTop ℝ) ≤ henselianSeparableAddValuation v hH (rootOrbitField k L j β)
    (b.equivFun.symm
      (VectorGroup.sectionCoordinates _ _
        (rationalPoints.map
          (rootFieldVectorIsoOfOrbit k L f j hG hj hS hT ha hhigh β horbit hq b).hom g)
        ).toAdd) ↔ _
  rw [sectionCoordinates_rootFieldVectorIsoOfOrbit k L f j hG hj hS hT ha hhigh
    β horbit hq b hcent hβ, LinearEquiv.symm_apply_apply]
  exact (iff_of_eq (congrArg (fun t : WithTop ℝ => (r : WithTop ℝ) ≤ t)
    (additiveRootValue_of_mem
      (henselianSeparableAddValuation v hH (rootOrbitField k L j β))
      (rootFieldCoordinatesOfOrbit k L f j hG hj hS hcent hT ha hhigh β hβ horbit).equiv
      (hq.pointsEquiv (Over.mk (𝟙 _)) g)))).symm

/-- The ambient point image of the actual integral model is exactly
the additive filtration defined by the published root-orbit field coordinates. -/
theorem rootFieldDepthModelOfOrbit_integralPoints_map (r : ℝ) :
    (rootFieldDepthModelOfOrbit k L f j hG hj hS hT ha hhigh β horbit hq b v hH hv r
      ).integralPoints.map (rationalPoints.map q) =
      additiveRootFiltration
        (henselianSeparableAddValuation v hH (rootOrbitField k L j β))
        (rootFieldCoordinatesOfOrbit k L f j hG hj hS hcent hT ha hhigh β hβ horbit).equiv r := by
  ext g
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact ⟨(hq.pointsEquiv (Over.mk (𝟙 _)) z).property,
      (rootFieldDepthModelOfOrbit_mem_integralPoints k L f j hG hj hS hT ha hhigh
        β horbit hq b v hH hv hcent hβ r z).mp hz⟩
  · rintro ⟨hg, hdepth⟩
    let z := (hq.pointsEquiv (Over.mk (𝟙 _))).symm ⟨g, hg⟩
    have hz : rationalPoints.map q z = g :=
      hq.pointsEquiv_symm_comp ⟨g, hg⟩
    refine ⟨z, (rootFieldDepthModelOfOrbit_mem_integralPoints k L f j hG hj hS hT ha hhigh
      β horbit hq b v hH hv hcent hβ r z).mpr ?_, hz⟩
    rwa [hz]

end Langlands.GroupScheme.IntegralModel
