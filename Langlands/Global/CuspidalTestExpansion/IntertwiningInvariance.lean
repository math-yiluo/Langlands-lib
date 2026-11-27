import Langlands.Global.AdelicIntertwiningIntegrability
import Langlands.Automorphic.GroupSchemeParabolicWeilMeasure
import Langlands.Global.LeftCosetFundamentalDomain

/-! # Left invariance of intertwining integrals under the adelic target radical -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj

set_option autoImplicit false

namespace Langlands.Global.AdelicGroupPoints

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions

variable {F : Type u} [Field F] [NumberField F]
  {G P U V : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom] [IsAffine P.X.left] [IsAffine V.X.left]
  {p : P ⟶ G} [IsClosedImmersion p.hom.hom.left] {K : Subgroup (AdelicGroupPoints F G)}

set_option maxHeartbeats 800000 in
/-- If the rational quotient of the target subgroup `V` is compact and `U` is unipotent, the
intertwining integral of a function `φ` that is left invariant under `U(𝔸)` is left invariant
under `V(𝔸)`: right translation of the quotient `(V(F) ∩ wU(𝔸)w⁻¹) \ V(𝔸)` preserves its
measure. -/
theorem IsIwasawaCompact.intertwiningIntegral_adelicPoints_mul (hK : IsIwasawaCompact p K)
    (iU : U ⟶ P) (j : V ⟶ G) [IsClosedImmersion j.hom.hom.left]
    [CompactSpace (AdelicSubgroupPoints.RationalQuotient F G (SubgroupFunctor.range j))]
    (w : Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ G.X) (hU : IsUnipotent U)
    {φ : AdelicGroupPoints F G → ℂ}
    (hφ : IsLeftInvariantUnder F G (parabolicUnipotentImage F p iU) φ)
    (lam : ComplexCharacterParameter F P)
    (u : AdelicSubgroupPoints.adelicPoints F G (SubgroupFunctor.range j))
    (y : AdelicGroupPoints F G) :
    hK.intertwiningIntegral iU j w φ lam ((u : AdelicGroupPoints F G) * y) =
      hK.intertwiningIntegral iU j w φ lam y := by
  let H := AdelicSubgroupPoints.adelicPoints F G (SubgroupFunctor.range j)
  have hcl : IsClosed (H : Set (AdelicGroupPoints F G)) :=
    AdelicSubgroupPoints.isClosed_adelicPoints_range F G j
  have : LocallyCompactSpace H := hcl.locallyCompactSpace
  have : PolishSpace H := hcl.polishSpace
  let Γ := intertwiningRationalSubgroup F p iU j (innerAdelicPoint F G w)
  have hΓ := isDiscrete_intertwiningRationalSubgroup F p iU j (innerAdelicPoint F G w)
  have : BorelSpace (LeftCosetSpace Γ) := LeftCosetSpace.discreteQuotientBorelSpace Γ hΓ
  let ν := AdelicSubgroupPoints.normalizedHaarMeasure F G (SubgroupFunctor.range j)
  have : (Measure.haar : Measure H).IsMulRightInvariant :=
    AdelicSubgroupPoints.haar_isMulRightInvariant_of_compactRationalQuotient F G
      (SubgroupFunctor.range j)
  have : ν.IsMulLeftInvariant := by
    dsimp only [ν, AdelicSubgroupPoints.normalizedHaarMeasure]; infer_instance
  have : ν.IsMulRightInvariant := by
    dsimp only [ν, AdelicSubgroupPoints.normalizedHaarMeasure]; infer_instance
  have hmp := LeftCosetSpace.measurePreserving_rightTranslate_discrete Γ hΓ ν u
  have hcomp : hK.intertwiningIntegrand iU j w φ lam ((u : AdelicGroupPoints F G) * y) =
      hK.intertwiningIntegrand iU j w φ lam y ∘ LeftCosetSpace.rightTranslate Γ u := by
    funext q
    induction q using Quotient.inductionOn with
    | _ v =>
      change hK.intertwiningIntegrand iU j w φ lam ((u : AdelicGroupPoints F G) * y)
          (LeftCosetSpace.mk Γ v) =
        hK.intertwiningIntegrand iU j w φ lam y
          (LeftCosetSpace.rightTranslate Γ u (LeftCosetSpace.mk Γ v))
      rw [LeftCosetSpace.rightTranslate_mk, hK.intertwiningIntegrand_mk iU j w hU hφ,
        hK.intertwiningIntegrand_mk iU j w hU hφ]
      congr 1
      simp only [Subgroup.coe_mul, mul_assoc]
  have hemb : MeasurableEmbedding (LeftCosetSpace.rightTranslate Γ u) :=
    (LeftCosetSpace.rightTranslateHomeomorph Γ u).measurableEmbedding
  unfold IsIwasawaCompact.intertwiningIntegral
  rw [hcomp]
  exact hmp.integral_comp hemb _

end Langlands.Global.AdelicGroupPoints
