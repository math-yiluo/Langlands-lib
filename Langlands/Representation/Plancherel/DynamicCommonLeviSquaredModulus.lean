import Langlands.Representation.Plancherel.DynamicCommonLeviComposition
import Langlands.Representation.Aubert.General.EqualCentralizerHaarBalance
import Langlands.GroupScheme.Rational.RelativeRootSystemProof
import Langlands.GroupScheme.Rational.LeviFactorization
import Langlands.GroupScheme.Rational.SplitTorusFactorization
import Langlands.GroupScheme.SubgroupIntersection
import Langlands.GroupScheme.Lie.ScalarExtensionCoordinates

/-! # Squared modulus for actual dynamic parabolics with a common Levi -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj NNReal
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology

set_option backward.isDefEq.respectTransparency false

namespace Langlands.Plancherel.DynamicCommonLeviComposition

open Aubert.General Aubert.General.RationalPointFamily StandardIntertwining
open DynamicOppositeStandardIntertwining

attribute [local instance]
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningIsAffine
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningTopologicalSpace
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningT2Space
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningIsTopologicalGroup
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningT2Space2
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningLocallyCompactSpace
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningNonarchimedeanGroup
  DynamicOppositeStandardIntertwining.centralizerClosedImmersion
  DynamicOppositeStandardIntertwining.centralizerAffine

variable {F : Type u} [Field F]
  {T : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom]
  (χ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)
  (i : T.toGrp ⟶ G) (ζ : cocharacterLattice T)
  (hζ : Dynamic.centralizer (CommGroupScheme.groupHom ζ ≫ i) =
    Dynamic.centralizer χ)

/-- The original torus, factored through the actual parameter scheme of the
common Levi, using one cocharacter with that centralizer. -/
def torusParameterFactor : T.toGrp ⟶ parameterScheme χ :=
  Dynamic.torusFactor i (CommGroupScheme.groupHom ζ)
    ⟨(Dynamic.Affine.isRepresentedBy_centralizerHom χ).1,
      (Dynamic.Affine.isRepresentedBy_centralizerHom χ).2.trans hζ.symm⟩

/-- Including the factor into `G` is the original torus homomorphism. -/
theorem torusParameterFactor_comp :
    torusParameterFactor χ i ζ hζ ≫ Dynamic.Affine.centralizerHom χ = i :=
  Dynamic.torusFactor_comp i (CommGroupScheme.groupHom ζ)
    ⟨(Dynamic.Affine.isRepresentedBy_centralizerHom χ).1,
      (Dynamic.Affine.isRepresentedBy_centralizerHom χ).2.trans hζ.symm⟩

/-- Central split torus character detection gives injective restriction to
the torus factor in the common Levi. -/
theorem torusParameterFactor_characterRestrict_injective
    (hCST : CentralSplitTorusCharacterStatement.{u}) (hG : IsConnectedReductive G)
    (hi : IsMaximalSplitTorus i) :
    Function.Injective (characterRestrict (torusParameterFactor χ i ζ hζ)) := by
  have hZred := parameterScheme_isConnectedReductive χ hG
  have : IsAffineHom (parameterScheme χ).X.hom := hZred.isAffineHom
  rw [injective_iff_map_eq_zero]
  intro θ hθ
  by_contra hne
  obtain ⟨A, a, ha, hres⟩ := hCST F (parameterScheme χ) hZred θ hne
  obtain ⟨g, hg⟩ := ha.exists_factor_of_isMaximalSplitTorus
    (Dynamic.Affine.isClosedSubgroup_centralizerHom χ)
    (t := torusParameterFactor χ i ζ hζ)
    (by rwa [torusParameterFactor_comp])
  apply hres
  rw [← hg, characterRestrict_comp, AddMonoidHom.comp_apply, hθ, map_zero]

private theorem closedNormalizerCharacter_congr'
    {H : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [LocallyCompactSpace H] {U V : Subgroup H}
    (hUV : U = V) (hU : IsClosed (U : Set H)) (hV : IsClosed (V : Set H))
    (x : Subgroup.normalizer (U : Set H)) (y : Subgroup.normalizer (V : Set H))
    (hxy : (x : H) = y) :
    HaarModulus.closedNormalizerCharacter U hU x =
      HaarModulus.closedNormalizerCharacter V hV y := by
  subst V
  congr 1
  exact Subtype.ext hxy

variable [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [LocallyOfFiniteType G.X.hom]
  (eta : cocharacterLattice T)
  (heta : Dynamic.centralizer (CommGroupScheme.groupHom eta ≫ i) =
    Dynamic.centralizer χ)
  [MeasurableSpace ((radical (CommGroupScheme.groupHom ζ ≫ i)).subgroupOf
    (radical (CommGroupScheme.groupHom eta ≫ i)))]
  [BorelSpace ((radical (CommGroupScheme.groupHom ζ ≫ i)).subgroupOf
    (radical (CommGroupScheme.groupHom eta ≫ i)))]

/-- The squared-modulus premise of the actual common-Levi pair family follows
from central split torus character detection and connected reductivity.
The two cocharacters factor through the supplied maximal split torus. -/
theorem squaredModulus_of_centralSplitTorusCharacter
    (hCST : CentralSplitTorusCharacterStatement.{u}) (hG : IsConnectedReductive G)
    (hi : IsMaximalSplitTorus i) :
    SquaredModulusCompatibility
      (commonDecomposition χ (CommGroupScheme.groupHom ζ ≫ i) hζ)
      (radical_isClosed (CommGroupScheme.groupHom ζ ≫ i))
      (commonDecomposition χ (CommGroupScheme.groupHom eta ≫ i) heta)
      (radical_isClosed (CommGroupScheme.groupHom eta ≫ i)) := by
  have : Smooth G.X.hom := hG.smooth
  have : Mono i.hom.hom.left := hi.isSplitSubtorus.mono
  let ψ := CommGroupScheme.groupHom ζ ≫ i
  let ψ' := CommGroupScheme.groupHom eta ≫ i
  let iZ := Dynamic.Affine.centralizerHom χ
  have hχrep := Dynamic.Affine.isRepresentedBy_centralizerHom χ
  have hZ : SubgroupFunctor.range iZ ≤ Dynamic.centralizer ψ := by
    rw [show ψ = CommGroupScheme.groupHom ζ ≫ i from rfl, hζ]
    exact hχrep.2.le
  have hZ' : SubgroupFunctor.range iZ ≤ Dynamic.centralizer ψ' := by
    rw [show ψ' = CommGroupScheme.groupHom eta ≫ i from rfl, heta]
    exact hχrep.2.le
  have hEq : Dynamic.centralizer ψ = Dynamic.centralizer ψ' := hζ.trans heta.symm
  have hUc := radical_isClosed ψ
  have hVc := radical_isClosed ψ'
  have hCc : IsClosed ((Dynamic.unipotent ψ ⊓ Dynamic.unipotent ψ').carrier
      (Over.mk (𝟙 _)) : Set (RationalPoint F G.X)) := hUc.inter hVc
  have hUrep := Dynamic.Affine.isRepresentedBy_unipotentHom ψ
  have hVrep := Dynamic.Affine.isRepresentedBy_unipotentHom ψ'
  have hUcl := Dynamic.Affine.isClosedSubgroup_unipotentHom ψ
  have hVcl := Dynamic.Affine.isClosedSubgroup_unipotentHom ψ'
  have hCcl := isClosedSubgroup_subgroupIntersectionHom hUcl hVcl
  have hCrep := isRepresentedBy_subgroupIntersectionHom hUcl hVcl
  rw [hUrep.2, hVrep.2] at hCrep
  have := hUcl.isAffineHom
  have := hVcl.isAffineHom
  have := hCcl.isAffineHom
  have := hUcl.locallyOfFiniteType
  have := hVcl.locallyOfFiniteType
  have := hCcl.locallyOfFiniteType
  let h := commonDecomposition χ ψ hζ
  let h' := commonDecomposition χ ψ' heta
  apply (squaredModulusCompatibility_iff h hUc h' hVc).mpr
  intro m
  have hm : (m : rationalPoints G) ∈ (SubgroupFunctor.range iZ).carrier
      (Over.mk (𝟙 _)) := by
    rw [hχrep.2]
    exact m.property
  obtain ⟨z, hz⟩ := SubgroupFunctor.mem_range.mp hm
  have key := centralizingHaarCharacter_values_square_of_centralizer_eq
    (relativeRootSystem F G hG T i hi) hi.isSplitSubtorus.1 ζ eta hEq iZ hZ hZ'
    hUrep hVrep hCrep (torusParameterFactor χ i ζ hζ)
    (torusParameterFactor_comp χ i ζ hζ)
    (Lie.finiteCoordinates _) (Lie.finiteCoordinates _) (Lie.finiteCoordinates _)
    hUc hVc hCc
    (torusParameterFactor_characterRestrict_injective χ i ζ hζ hCST hG hi) z
  have h1 : centralizingUnipotentHaarCharacter ψ iZ hZ hUc z =
      HaarModulus.closedRestrictCharacter _ hUc _ h.levi_le_normalizer m :=
    closedNormalizerCharacter_congr' rfl hUc hUc _ _ hz
  have h2 : centralizingUnipotentHaarCharacter ψ' iZ hZ' hVc z =
      HaarModulus.closedRestrictCharacter _ hVc _ h'.levi_le_normalizer m :=
    closedNormalizerCharacter_congr' rfl hVc hVc _ _ hz
  have h3 : centralizingUnipotentIntersectionHaarCharacter ψ ψ' iZ hZ hZ' hCc z =
      HaarModulus.closedRestrictCharacter _ (hUc.inter hVc) _
        (levi_le_normalizer_intersection h h') m :=
    closedNormalizerCharacter_congr' rfl hCc (hUc.inter hVc) _ _ hz
  rw [h1, h2, h3] at key
  exact key

end Langlands.Plancherel.DynamicCommonLeviComposition
