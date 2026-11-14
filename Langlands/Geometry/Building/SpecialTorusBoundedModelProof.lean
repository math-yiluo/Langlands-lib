import Langlands.Geometry.Building.UnramifiedTorusUnitGaloisFixedPointStatement
import Langlands.Geometry.Building.UnramifiedTorusUnitGaloisFixedPointProof
import Langlands.Geometry.Building.SpecialTorusBoundedModelStatement
import Langlands.Geometry.Building.UnramifiedFixedPointStabilizer
import Langlands.Geometry.Building.TorusUnitApartmentFixation
import Langlands.BruhatTits.IntegralModels.UnramifiedFullModelConstruction
import Langlands.GroupScheme.Rational.SplitRankTransport
import Langlands.Geometry.Building.UnramifiedFiniteVertexFixerAssembly
import Langlands.GroupScheme.IntegralModel.FiniteIndexEnlargementProof
import Langlands.GroupScheme.IntegralModel.UnramifiedSmoothDescentProof
import Langlands.Geometry.Building.UnramifiedVertexMaximalBoundedProof
import Langlands.GroupScheme.IntegralModel.MaximalBoundedConstruction
import Langlands.GroupScheme.IntegralModel.SmoothIntersectionConstruction

/-! # A smooth model containing the bounded points of two split tori

The building input of Kaletha–Prasad, Proposition 9.3.4: from a point of the building of `G_K`
fixed by the Galois group and by `S(K)^1`, the smooth model at that point descends to `𝒪[F]`. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped ValuativeRel CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.GroupScheme.GaloisPointComparison
open Langlands.LocalGalois.Separable

namespace Langlands.Geometry.Building

private instance specialTorusBoundedModelAffineHom {F : Type u} [Field F] [ValuativeRel F]
    [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom] :
    IsAffineHom (baseChanged F (inertiaFixedField F) G).X.hom := by
  change IsAffineHom
    (CategoryTheory.Limits.pullback.snd G.X.hom (baseMap F (inertiaFixedField F)))
  infer_instance

/-- If `h` fixes `p`, then `g h g⁻¹` fixes `g • p`. -/
private theorem conj_mem_stabilizer_smul {Γ X : Type*} [Group Γ] [MulAction Γ X]
    (g h : Γ) (p : X) (hp : h • p = p) :
    g * h * g⁻¹ ∈ MulAction.stabilizer Γ (g • p) := by
  rw [MulAction.mem_stabilizer_iff, mul_smul, mul_smul, inv_smul_smul, hp]

set_option maxHeartbeats 800000 in
/-- A Galois-fixed point of the building of `G_K` fixed by `S(K)^1` gives the smooth
`𝒪[F]`-model of `SpecialTorusBoundedModelStatement`. All other inputs are Library theorems. -/
theorem specialTorusBoundedModel_of_torusUnitGaloisFixedPoint
    (hfixed : UnramifiedTorusUnitGaloisFixedPointStatement.{u}) :
    SpecialTorusBoundedModelStatement.{u} := by
  intro F _ _ _ _ G hG S iS hiS
  let : IsAffineHom G.X.hom := hG.isAffineHom
  obtain ⟨C, ρ, y, hρ, hy, hS⟩ := hfixed F G hG S iS hiS
  obtain ⟨g, x, hgx⟩ := C.exists_smul_apartmentMap y
  have hbounded : ∀ f : C.Apartment →ᵃ[ℝ] ℝ, BddAbove (f '' {x}) := by
    intro f
    rw [Set.image_singleton]
    exact bddAbove_singleton
  obtain ⟨M', hM', hM'p⟩ :=
    Langlands.BruhatTits.IntegralModels.exists_smoothFullModel_of_vertexInputs
      MaximalUnramified.vertexOneStabilizerMaximalBounded
      MaximalUnramified.finiteVertexFixerApproximation maximalBoundedIntegralModel
      IntegralModel.smoothIntersection IntegralModel.finiteIndexEnlargement F
      (baseChanged F (inertiaFixedField F) G) C g {x} (Set.singleton_nonempty x) hbounded
  have himage : M'.integralPoints =
      characterValuationKernel (MaximalUnramified.valuation F)
          (baseChanged F (inertiaFixedField F) G) ⊓
        MulAction.stabilizer (rationalPoints (baseChanged F (inertiaFixedField F) G)) y := by
    rw [hM'p, Set.image_singleton, hgx]
    ext h
    rw [Subgroup.mem_inf, Subgroup.mem_inf, MulAction.mem_stabilizer_iff,
      IntegerValuationBuildingData.pointwiseFixer, KPApartmentData.mem_pointwiseFixer,
      Set.forall_mem_singleton]
  obtain ⟨M, hM, ⟨e⟩⟩ := IntegralModel.exists_descent_of_fixedPoint_integralPoints
    IntegralModel.unramifiedSmoothModelDescent G ρ hρ y hy M' hM' himage
  have hpts : M.baseChangeUnramified.integralPoints = M'.integralPoints :=
    e.integralPoints_eq
  refine ⟨M, hM, ?_, C.S,
    C.i ≫ ((baseChanged F (inertiaFixedField F) G).innerIso g).hom,
    C.isMaximalSplitTorus.comp_iso _, ?_⟩
  · rintro _ ⟨s, hs, rfl⟩
    rw [hpts, himage]
    exact ⟨IntegerValuation.map_mem_characterValuationKernel _ _ hs, hS s hs⟩
  · rintro _ ⟨a, ha, rfl⟩
    rw [hpts, himage]
    refine ⟨IntegerValuation.map_mem_characterValuationKernel _ _ ha, ?_⟩
    have hfix := torusUnitApartmentFixation (inertiaFixedField F)
      (MaximalUnramified.valuation F) C.S.toGrp C.S
      (baseChanged F (inertiaFixedField F) G) C.i C.apartment C.centralizer
      C.isOmegaCompatible (𝟙 _) a ha x
    rw [Category.id_comp] at hfix
    have hpoint : rationalPoints.map
        (C.i ≫ ((baseChanged F (inertiaFixedField F) G).innerIso g).hom) a =
        g * rationalPoints.map C.i a * g⁻¹ := by
      change rationalPoints.map ((baseChanged F (inertiaFixedField F) G).innerIso g).hom
          (rationalPoints.map C.i a) = _
      rw [rationalPoints.map_apply, comp_innerIso_hom, constantPoint_self]
    have hconj := conj_mem_stabilizer_smul g (rationalPoints.map C.i a)
      (C.apartmentMap x) hfix
    rw [hgx, ← hpoint] at hconj
    exact hconj

/-- **Kaletha–Prasad, Proposition 9.3.4 (building input).** For a connected reductive group
over a nonarchimedean local field and a maximal split torus, there is a smooth affine
`𝒪[F]`-model whose unramified integral points contain the bounded points of that torus and of
a maximal `K`-split torus of `G_K`. -/
theorem specialTorusBoundedModel : SpecialTorusBoundedModelStatement.{u} :=
  specialTorusBoundedModel_of_torusUnitGaloisFixedPoint unramifiedTorusUnitGaloisFixedPoint

end Langlands.Geometry.Building
