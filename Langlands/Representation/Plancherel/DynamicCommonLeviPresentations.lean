import Langlands.Representation.Plancherel.DynamicCommonLeviPresentationComparison
import Langlands.GroupScheme.Rational.RationalCocharacterParabolicModels
import Langlands.GroupScheme.Rational.ParabolicRootPresentationProof
import Langlands.GroupScheme.Rational.SplitComponentProof
import Langlands.GroupScheme.Rational.AffineGeometricUnipotentRadical

/-! # Simultaneous presentations on the actual common Levi -/

noncomputable section

set_option maxHeartbeats 400000

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme

namespace Langlands.Plancherel.DynamicCommonLeviPresentations

open DynamicOppositeStandardIntertwining DynamicCommonLeviPresentationComparison

attribute [local instance]
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningIsAffine
  DynamicOppositeStandardIntertwining.centralizerClosedImmersion
  DynamicOppositeStandardIntertwining.centralizerAffine

variable {F : Type u} [Field F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  (χ ψ ψ' : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)

/-- One complete presentation with the specified canonical common Levi.
The realization equalities hold on all test schemes. -/
structure ParabolicData
    (T : CommGroupScheme (Spec (CommRingCat.of F)))
    (a : T.toGrp ⟶ parameterScheme χ) where
  P : GroupScheme (Spec (CommRingCat.of F))
  U : GroupScheme (Spec (CommRingCat.of F))
  p : P ⟶ G
  l : parameterScheme χ ⟶ P
  n : U ⟶ P
  r : ParabolicRootPresentation p l a
  levi_comp : l ≫ p = Dynamic.Affine.centralizerHom χ
  radical : LeviSubgroup.IsGeometricUnipotentRadical n
  realizes : Realizes χ ψ p l n

/-- Construct a complete presentation while retaining the given common
Levi model and split component literally. -/
def parabolicData (hG : IsConnectedReductive G)
    (hψ : Dynamic.centralizer ψ = Dynamic.centralizer χ)
    (T : CommGroupScheme (Spec (CommRingCat.of F)))
    (a : T.toGrp ⟶ parameterScheme χ) (ha : IsSplitComponent a) :
    ParabolicData χ ψ T a := by
  have hZ : (Dynamic.centralizer ψ).IsRepresentedBy
      (Dynamic.Affine.centralizerHom χ) := by
    rw [hψ]
    exact Dynamic.Affine.isRepresentedBy_centralizerHom χ
  let d := fixedLeviParabolicModel hG ψ hZ
  let U := Dynamic.Affine.unipotentScheme ψ
  let hU := Dynamic.Affine.isRepresentedBy_unipotentHom ψ
  let n := Dynamic.unipotentToParabolic d.parabolic_rep hU
  have hn : n ≫ d.p = Dynamic.Affine.unipotentHom ψ :=
    Dynamic.unipotentToParabolic_comp d.parabolic_rep hU
  have hUn : (Dynamic.unipotent ψ).IsRepresentedBy (n ≫ d.p) := by
    rw [hn]
    exact hU
  letI : IsAffineHom d.P.X.hom := d.levi.isAffineHom
  have hrad : LeviSubgroup.IsGeometricUnipotentRadical n :=
    (dynamicGeometricUnipotentRadical F G hG ψ d.P U d.p n
      d.parabolic_rep hUn).leviSubgroup
  exact
    { P := d.P
      U := U
      p := d.p
      l := d.l
      n := n
      r := Classical.choice (parabolicRootPresentationExistence F G hG
        d.P (parameterScheme χ) T d.p d.l a d.parabolic d.levi ha)
      levi_comp := d.comp
      radical := hrad
      realizes :=
        { parabolic := d.parabolic_rep.2
          levi := by rw [d.comp]; exact
            (Dynamic.Affine.isRepresentedBy_centralizerHom χ).2
          radical := hUn.2 } }

/-- Two complete presentations share the exact Levi model and one
split-component inclusion, before any rational-point comparisons. -/
structure CommonData where
  T : CommGroupScheme (Spec (CommRingCat.of F))
  a : T.toGrp ⟶ parameterScheme χ
  first : ParabolicData χ ψ T a
  second : ParabolicData χ ψ' T a

/-- Simultaneous complete presentations for two dynamic parabolics with
the displayed common centralizer. -/
def commonData (hG : IsConnectedReductive G)
    (hψ : Dynamic.centralizer ψ = Dynamic.centralizer χ)
    (hψ' : Dynamic.centralizer ψ' = Dynamic.centralizer χ) :
    CommonData χ ψ ψ' := by
  apply Classical.choice
  obtain ⟨T, a, ha⟩ := (splitComponentStatement F (parameterScheme χ)
    (parameterScheme_isConnectedReductive χ hG)).1
  exact ⟨⟨T, a, parabolicData χ ψ hG hψ T a ha,
    parabolicData χ ψ' hG hψ' T a ha⟩⟩

/-- The two common-Levi inclusions are equal as scheme morphisms. -/
theorem CommonData.levi_comp (d : CommonData χ ψ ψ') :
    d.first.l ≫ d.first.p = d.second.l ≫ d.second.p :=
  d.first.levi_comp.trans d.second.levi_comp.symm

/-- The auxiliary dynamic opposite and its actual geometric radical. -/
structure OppositeData
    (ξ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G) where
  Q : GroupScheme (Spec (CommRingCat.of F))
  V : GroupScheme (Spec (CommRingCat.of F))
  q : Q ⟶ G
  v : V ⟶ Q
  represented : (Dynamic.parabolic ξ).IsRepresentedBy q
  radical : LeviSubgroup.IsGeometricUnipotentRadical v

/-- Construct auxiliary data for the negative split-component direction
of a complete presentation. -/
def oppositeData (hG : IsConnectedReductive G)
    (ξ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G) :
    OppositeData ξ := by
  let d := Dynamic.affineDecompositionModel ξ
  letI : IsAffineHom d.parabolic.X.hom := d.parabolic_closed.isAffineHom
  exact
    { Q := d.parabolic
      V := d.unipotent
      q := d.parabolicHom
      v := d.unipotentHom
      represented := d.parabolic_rep
      radical := (dynamicGeometricUnipotentRadical F G hG ξ d.parabolic d.unipotent
        d.parabolicHom d.unipotentHom d.parabolic_rep d.unipotent_rep).leviSubgroup }

/-- Local finite type of the fixed common Levi is inherited from the ambient
group, so the simultaneous construction adds no finite-type premise. -/
theorem parameterScheme_locallyOfFiniteType [LocallyOfFiniteType G.X.hom] :
    LocallyOfFiniteType (parameterScheme χ).X.hom :=
  (Dynamic.Affine.isClosedSubgroup_centralizerHom χ).locallyOfFiniteType

end Langlands.Plancherel.DynamicCommonLeviPresentations
