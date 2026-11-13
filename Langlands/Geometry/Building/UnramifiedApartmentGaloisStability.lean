import Langlands.Geometry.Building.UnramifiedOmegaGaloisStable
import Langlands.Geometry.Building.UnramifiedValuationDescentStatement
import Langlands.Geometry.Building.IntegerOmegaGaloisStability
import Langlands.Geometry.Building.MaximalUnramifiedValuation
import Langlands.Geometry.Building.CentralizerDatumOfStructure
import Langlands.GroupScheme.FieldCentralizerRepresentabilityProof
import Langlands.GroupScheme.Dynamic.CentralizerReductiveProof
import Langlands.GroupScheme.Rational.CentralSplitTorusCharacterProof
import Langlands.GroupScheme.Reductive.FieldExtensionProof
import Langlands.GroupScheme.BaseChangeReflection
import Langlands.GroupScheme.SubgroupBaseChange
import Langlands.GroupScheme.Torus.MaximalBaseChangeForwardReduction
import Langlands.GroupScheme.Torus.Split
import Langlands.AlgebraicGeometry.SchemeFlatPropertyDescent

/-! # Galois stability of V 6 apartment classes over the maximal unramified extension -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace Langlands.BruhatTits
open Langlands.GroupScheme.GaloisPointComparison
open Langlands.LocalGalois Langlands.LocalGalois.Separable

namespace Langlands.Geometry.Building

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]

local notation "K" => inertiaFixedField F
local notation "b" => algebraBaseMap F (inertiaFixedField F)

private instance galoisStabilityAffineHom
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom] :
    IsAffineHom (baseChanged F (inertiaFixedField F) G).X.hom := by
  change IsAffineHom
    (CategoryTheory.Limits.pullback.snd G.X.hom (baseMap F (inertiaFixedField F)))
  infer_instance

/-- **Galois stability of V 6 classes over the maximal unramified extension.** Let `T` be an
`F`-group with a homomorphism `iT : T → G` whose scalar extension is a maximal split torus of
`G_K`, `K = inertiaFixedField F`. Every class `D` of valuations of the root datum of
`(G_K, T_K)` satisfying V 6 for the order of `K` and some centralizer datum over `K` is stable
under every `σ ∈ Aut(K/F)`. -/
theorem unramifiedGaloisStable_of_isOmegaCompatible
    {G : GroupScheme (Spec (CommRingCat.of F))} (hG : IsConnectedReductive G)
    [IsAffineHom G.X.hom]
    {T : CommGroupScheme (Spec (CommRingCat.of F))} (iT : T.toGrp ⟶ G)
    (hiT : IsMaximalSplitTorus (T := (CommGroupScheme.baseChange b).obj T)
      ((GroupScheme.baseChange b).map iT))
    [Mono ((GroupScheme.baseChange b).map iT).hom.hom.left]
    (hE : RelativeRoot.HasOppositeFactorPairs (T := (CommGroupScheme.baseChange b).obj T)
      ((GroupScheme.baseChange b).map iT))
    (D : KPApartmentData (S := (CommGroupScheme.baseChange b).obj T)
      ((GroupScheme.baseChange b).map iT)
      (IntegerValuation.order (MaximalUnramified.valuation F)))
    (C : CentralizerDatum (S := (CommGroupScheme.baseChange b).obj T)
      ((GroupScheme.baseChange b).map iT))
    (h6 : IntegerValuation.IsOmegaCompatible (MaximalUnramified.valuation F) D C) :
    KPApartmentData.GaloisStable F K iT D := by
  -- `T` is affine: affineness descends along the fpqc morphism `Spec K → Spec F`.
  have hTK : IsAffineHom ((CommGroupScheme.baseChange b).obj T).X.hom :=
    hiT.isSplitSubtorus.1.isAffineHom
  have hT : IsAffineHom T.X.hom := by
    obtain ⟨h1, h2, h3⟩ := fieldExtension_fpqc F K
    exact MorphismProperty.of_pullback_snd_of_descendsAlong
      (P := @IsAffineHom) (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact)
      (f := T.X.hom) (g := b) ⟨⟨h1, h2⟩, h3⟩ hTK
  -- An `F`-representative of the centralizer of `T`, and its scalar extension.
  obtain ⟨Z, j, hj, hjc⟩ := fieldCentralizerRepresentability F T G hT iT
  have hs : torusCentralizerFactor iT hj ≫ j = iT := torusCentralizerFactor_comp iT hj
  have hcl : IsClosedSubgroup ((GroupScheme.baseChange b).map j) := hjc.baseChange b
  have hrep : (torusCentralizer (T := (CommGroupScheme.baseChange b).obj T)
      ((GroupScheme.baseChange b).map iT)).IsRepresentedBy
        ((GroupScheme.baseChange b).map j) := by
    rw [torusCentralizer_baseChange]
    exact hj.baseChange b
  have hcomp : (GroupScheme.baseChange b).map (torusCentralizerFactor iT hj) ≫
      (GroupScheme.baseChange b).map j = (GroupScheme.baseChange b).map iT := by
    rw [← Functor.map_comp, hs]
  have hGK : IsConnectedReductive (baseChanged F K G) :=
    connectedReductiveFieldExtensionStatement F K G hG
  have hK : Function.Bijective (Cartan.restrictionEvaluation
      (S := (CommGroupScheme.baseChange b).obj T)
      ((GroupScheme.baseChange b).map (torusCentralizerFactor iT hj))) := by
    have h := hiT.restrictionEvaluation_torusCentralizerFactor_bijective
      dynamicCentralizerReductive centralSplitTorusCharacter hGK hrep hcl
    have hfac : torusCentralizerFactor (B := (CommGroupScheme.baseChange b).obj T)
        ((GroupScheme.baseChange b).map iT) hrep =
        (GroupScheme.baseChange b).map (torusCentralizerFactor iT hj) := by
      apply hrep.hom_ext
      rw [torusCentralizerFactor_comp, hcomp]
    rwa [hfac] at h
  let C' : CentralizerDatum (S := (CommGroupScheme.baseChange b).obj T)
      ((GroupScheme.baseChange b).map iT) :=
    ⟨(GroupScheme.baseChange b).obj Z, (GroupScheme.baseChange b).map j,
      (GroupScheme.baseChange b).map (torusCentralizerFactor iT hj), hcl, hrep, hcomp, hK⟩
  have h6' : IntegerValuation.IsOmegaCompatible (MaximalUnramified.valuation F) D C' :=
    h6.of_centralizerDatum (MaximalUnramified.valuation F) C'
  exact IntegerValuation.IsOmegaCompatible.galoisStable F K iT j (torusCentralizerFactor iT hj)
    (MaximalUnramified.valuation F) (MaximalUnramified.order_galois F) D hcl hrep hcomp hK h6'
    hGK hiT hE

end Langlands.Geometry.Building
