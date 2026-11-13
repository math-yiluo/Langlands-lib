import Langlands.GroupScheme.IntegralModel.BaseChangeCoefficientHom
import Langlands.GroupScheme.IntegralModel.RelativeComponentConstruction
import Langlands.GroupScheme.IntegralModel.UnramifiedSplitMaximalTorus
import Langlands.GroupScheme.Rational.SplitTorus
import Langlands.GroupScheme.GeometricConnectedness
import Langlands.GroupScheme.RelativeParabolicNormalizerReduction
import Langlands.GroupScheme.Torus.SplitReductiveProof

/-! # Passing to the relative identity component keeps closed split tori

Let `F` be a nonarchimedean local field with integers `𝒪[F]`, residue field `𝓀[F]`, and
maximal-unramified integers `O_K`, and let `G` be a connected reductive `F`-group. Given a
smooth `𝒪[F]`-model `M` of `G` (no connectedness of the special fibre assumed) which contains

* a closed split `𝒪[F]`-torus with generic fibre identified with a given torus `S` of `G`, and
* after base change to `O_K`, a closed split `O_K`-torus whose generic fibre is a maximal
  split torus of `G_K`,

the relative identity component `N` of `M` is a smooth `𝒪[F]`-model of `G` with connected
special fibre containing the same two tori. This is the passage from `G_x` to `G^0_x` in
the construction of special-torus models.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped ValuativeRel

namespace Langlands.GroupScheme.IntegralModel

section Coefficients

variable {R K : Type u} [CommRing R] [IsDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K]
  {G H : GroupScheme (Spec (CommRingCat.of K))}
  {M : IntegralModel R K G} {N : IntegralModel R K H} {f : G ⟶ H}

/-- Generic torus maps are natural along model homomorphisms. -/
theorem Hom.genericTorusMap_comp (φ : M.Hom N f) (T : CommGroupScheme (Spec (CommRingCat.of R)))
    (j : T.toGrp ⟶ M.group) :
    N.genericTorusMap T (j ≫ φ.hom) = M.genericTorusMap T j ≫ f := by
  unfold genericTorusMap
  rw [Functor.map_comp, Category.assoc, φ.generic_comm, Category.assoc]

/-- A model homomorphism over the identity does not change generic torus maps. -/
theorem Hom.genericTorusMap_comp_of_id {N : IntegralModel R K G} (φ : M.Hom N (𝟙 G))
    (T : CommGroupScheme (Spec (CommRingCat.of R))) (j : T.toGrp ⟶ M.group) :
    N.genericTorusMap T (j ≫ φ.hom) = M.genericTorusMap T j := by
  rw [φ.genericTorusMap_comp, Category.comp_id]

end Coefficients

section Unramified

open Langlands.LocalGalois.Separable GaloisPointComparison

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))}

local instance specialTorusNeutralAlgebra : Algebra ↥𝒪[F] (fixedFieldIntegers F) :=
  Valuation.HasExtension.instAlgebraInteger
    (vR := ValuativeRel.valuation F) (vA := fixedFieldValuation F)

local instance specialTorusNeutralIsScalarTower :
    IsScalarTower ↥𝒪[F] (fixedFieldIntegers F) (inertiaFixedField F) :=
  Valuation.HasExtension.instIsScalarTowerInteger
    (vR := ValuativeRel.valuation F) (vA := fixedFieldValuation F)

/-- A model homomorphism over the identity does not change generic torus maps after base
change to the maximal-unramified integers. -/
theorem Hom.baseChangeUnramified_genericTorusMap_comp {M N : IntegralModel ↥𝒪[F] F G}
    (φ : M.Hom N (𝟙 G))
    (T : CommGroupScheme (Spec (CommRingCat.of (fixedFieldIntegers F))))
    (j : T.toGrp ⟶ M.baseChangeUnramified.group) :
    N.baseChangeUnramified.genericTorusMap T
        (j ≫ (Langlands.GroupScheme.baseChange
          (Spec.algebraMap ↥𝒪[F] (fixedFieldIntegers F))).map φ.hom) =
      M.baseChangeUnramified.genericTorusMap T j := by
  refine ((φ.baseChangeCoefficients (fixedFieldIntegers F) (inertiaFixedField F)).genericTorusMap_comp
    T j).trans ?_
  rw [CategoryTheory.Functor.map_id, Category.comp_id]
  rfl

/-- **From a smooth model to a special-torus model.** Let `G` be a connected reductive group
over a nonarchimedean local field `F`, let `iS : S ⟶ G`, and let `M` be a smooth
`𝒪[F]`-model of `G` containing a closed split `𝒪[F]`-torus over `iS` and, after base change
to the maximal-unramified integers, a closed split torus whose generic fibre is a maximal
split torus. Then the relative identity component of `M` is a smooth `𝒪[F]`-model of `G`
with connected special fibre which contains closed split tori with the same two properties. -/
theorem exists_connected_specialTorusModel (hG : IsConnectedReductive G)
    (S : CommGroupScheme (Spec (CommRingCat.of F))) (iS : S.toGrp ⟶ G)
    (M : IntegralModel ↥𝒪[F] F G) (hM : M.IsSmooth)
    (hS : ∃ (𝒮 : CommGroupScheme (Spec (CommRingCat.of ↥𝒪[F]))) (j : 𝒮.toGrp ⟶ M.group)
        (e : (CommGroupScheme.baseChange (Spec.algebraMap ↥𝒪[F] F)).obj 𝒮 ≅ S),
      IsSplitTorus 𝒮.toGrp ∧ IsClosedSubgroup j ∧
        M.genericTorusMap 𝒮 j = CommGroupScheme.groupHom e.hom ≫ iS)
    (hA : ∃ (𝒜 : CommGroupScheme (Spec (CommRingCat.of (fixedFieldIntegers F))))
        (a : 𝒜.toGrp ⟶ M.baseChangeUnramified.group),
      IsSplitTorus 𝒜.toGrp ∧ IsClosedSubgroup a ∧
        IsMaximalSplitTorus (M.baseChangeUnramified.genericTorusMap 𝒜 a)) :
    ∃ N : IntegralModel ↥𝒪[F] F G, N.IsSmooth ∧
      ConnectedSpace
        ((GroupScheme.baseChange (Spec.algebraMap ↥𝒪[F] 𝓀[F])).obj N.group).X.left ∧
      (∃ (𝒮 : CommGroupScheme (Spec (CommRingCat.of ↥𝒪[F]))) (j : 𝒮.toGrp ⟶ N.group)
          (e : (CommGroupScheme.baseChange (Spec.algebraMap ↥𝒪[F] F)).obj 𝒮 ≅ S),
        IsSplitTorus 𝒮.toGrp ∧ IsClosedSubgroup j ∧
          N.genericTorusMap 𝒮 j = CommGroupScheme.groupHom e.hom ≫ iS) ∧
      ∃ (𝒜 : CommGroupScheme (Spec (CommRingCat.of (fixedFieldIntegers F))))
        (a : 𝒜.toGrp ⟶ N.baseChangeUnramified.group),
        IsSplitTorus 𝒜.toGrp ∧ IsClosedSubgroup a ∧
          IsMaximalSplitTorus (N.baseChangeUnramified.genericTorusMap 𝒜 a) := by
  have : Smooth G.X.hom := hG.smooth
  have : IsAffineHom G.X.hom := hG.isAffineHom
  have : ConnectedSpace G.X.left := hG.connectedSpace
  have : GeometricallyConnected G.X.hom := geometricallyConnected_of_connected G
  obtain ⟨H, i, hi, hH, hgc⟩ := RelativeIdentityComponent.smoothExistence _ M.group hM
  have : GeometricallyConnected H.X.hom := hgc
  let φ := M.neutralInclusion hM hi hH
  refine ⟨M.neutralModel hM hi hH, hH, ?_, ?_, ?_⟩
  · exact connectedSpace_baseChange_of_geometricallyConnected H _
  · obtain ⟨𝒮, j, e, h𝒮, hj, hgen⟩ := hS
    have : GeometricallyConnected 𝒮.toGrp.X.hom := h𝒮.isReductive.geometricallyConnected
    obtain ⟨y, hy⟩ := hi.exists_hom_lift j
    refine ⟨𝒮, y, e, h𝒮, hi.isClosedSubgroup_of_comp (hy ▸ hj), ?_⟩
    rw [← hgen, ← hy]
    exact (φ.genericTorusMap_comp_of_id 𝒮 y).symm
  · obtain ⟨𝒜, a, h𝒜, ha, hmax⟩ := hA
    have : GeometricallyConnected 𝒜.toGrp.X.hom := h𝒜.isReductive.geometricallyConnected
    have hib := RelativeIdentityComponent.smoothBaseChange _ M.group hM H i hi _
      (Spec.algebraMap ↥𝒪[F] (fixedFieldIntegers F))
    obtain ⟨y, hy⟩ := hib.exists_hom_lift a
    refine ⟨𝒜, y, h𝒜, hib.isClosedSubgroup_of_comp (hy ▸ ha), ?_⟩
    have h := φ.baseChangeUnramified_genericTorusMap_comp 𝒜 y
    rw [neutralInclusion_hom] at h
    rw [← h, hy]
    exact hmax

end Unramified

end Langlands.GroupScheme.IntegralModel
