import Langlands.BruhatTits.IntegralModels.IntegralTorus
import Langlands.GroupScheme.IntegralModel.UnramifiedModelDescent
import Langlands.Geometry.Building.MaximalUnramifiedBuildingData
import Langlands.Geometry.Building.KPZeroSubgroups

/-! # The integral split torus of a descended parahoric model (KP §9.2.5) -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped ValuativeRel CategoryTheory.MonObj

namespace Langlands.BruhatTits.IntegralModels

open Langlands.GroupScheme Langlands.GroupScheme.GaloisPointComparison
open Langlands.LocalGalois.Separable Langlands.Geometry.Building

local instance unramifiedTorusClauseAlgebra {F : Type u} [Field F] [ValuativeRel F]
    [TopologicalSpace F] [IsNonarchimedeanLocalField F] :
    Algebra ↥𝒪[F] (fixedFieldIntegers F) :=
  Valuation.HasExtension.instAlgebraInteger
    (vR := ValuativeRel.valuation F) (vA := fixedFieldValuation F)

local instance unramifiedTorusClauseScalarTower {F : Type u} [Field F] [ValuativeRel F]
    [TopologicalSpace F] [IsNonarchimedeanLocalField F] :
    IsScalarTower ↥𝒪[F] (fixedFieldIntegers F) (inertiaFixedField F) :=
  Valuation.HasExtension.instIsScalarTowerInteger
    (vR := ValuativeRel.valuation F) (vA := fixedFieldValuation F)

/-- The base change of an affine group scheme to the maximal unramified extension is affine,
by pullback-stability of affine morphisms. -/
private instance unramifiedTorusClauseAffineHom {F : Type u} [Field F] [ValuativeRel F]
    [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom] :
    IsAffineHom (baseChanged F (inertiaFixedField F) G).X.hom := by
  change IsAffineHom
    (CategoryTheory.Limits.pullback.snd G.X.hom (baseMap F (inertiaFixedField F)))
  infer_instance

/-- **The integral split torus of a descended parahoric model**, a derived target from
Kaletha–Prasad §9.2.5, Proposition 9.3.4, Proposition B.2.4 and Proposition 8.2.1(1),
with Proposition 8.3.14(1) and Axiom 4.1.20(3) over the maximal unramified field.
Let `G` be a connected reductive group over a nonarchimedean local field `F`, with maximal
unramified extension `K = inertiaFixedField F`, and let `iS : S → G` be a maximal `F`-split
torus. Let `C` be supplied building data of `G_K`, `E` a datum computing `G(K)^0`, and `Ya` a
nonempty bounded subset of the apartment of `C` fixed pointwise by the maximal bounded subgroup
`S(K)^1` of `S(K)`. Take `g ∈ G(F)` and put `Y = g · Ya`. Every relative-component model pair
`D` over `𝒪[F]` whose neutral model has, after base change to the integers of `K`, the integral
points `G(K)^0_Y = G(K)^0 ∩ G(K)_Y` contains the conjugate torus `g S g⁻¹` in the sense of
KP Axiom 4.1.20(3): there is a split `𝒪[F]`-torus with generic fibre `S`, closed in the
neutral model over the generic inclusion `Int(g) ∘ iS`, whose special fibre is a maximal split
torus of the special fibre of the neutral model. No further building axioms on `C`,
Galois stability of `Y`, or construction of `D` are assumed. This module states the target
and does not prove it. -/
def UnramifiedTorusClauseStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom],
    IsConnectedReductive G →
    ∀ (S : CommGroupScheme (Spec (CommRingCat.of F))) (iS : S.toGrp ⟶ G),
    IsMaximalSplitTorus iS →
    ∀ (C : MaximalUnramified.BuildingData F (baseChanged F (inertiaFixedField F) G))
      (E : UnramifiedZeroDatum F (baseChanged F (inertiaFixedField F) G))
      (Ya : Set C.Apartment),
      Ya.Nonempty → (∀ f : C.Apartment →ᵃ[ℝ] ℝ, BddAbove (f '' Ya)) →
      (∀ s ∈ characterValuationKernel (MaximalUnramified.valuation F)
            (baseChanged F (inertiaFixedField F) S.toGrp),
        ∀ x ∈ Ya,
          rationalPoints.map ((GroupScheme.baseChange (baseMap F (inertiaFixedField F))).map iS)
              s • C.apartmentMap x = C.apartmentMap x) →
      ∀ (g : rationalPoints G) (D : RelativeComponentModelData ↥𝒪[F] F G),
        D.neutral.baseChangeUnramified.integralPoints =
          E.zeroPoints ⊓ C.pointwiseFixer
            ((fun x => rationalExtend F (inertiaFixedField F) G g • C.apartmentMap x) '' Ya) →
        ∃ T : IntegralTorusData D S (iS ≫ (G.innerIso g).hom), T.SatisfiesTorusClause

end Langlands.BruhatTits.IntegralModels
