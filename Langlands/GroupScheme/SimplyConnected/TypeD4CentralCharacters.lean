import Langlands.LinearAlgebra.RootDatumD4LeafWeights
import Langlands.GroupScheme.SimplyConnected.TypeDVectorQuotient
import Langlands.GroupScheme.Reductive.SplitSemisimpleRootSpanSufficiency

/-! # Fundamental characters and the D4 relation on central subgroup schemes -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme

variable {K : Type u} [Field K]
    {G : GroupScheme (Spec (CommRingCat.of K))}
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]

/-- Every actual root restricts to the zero character on a central subgroup
mapped into the torus, with equality on all test schemes. -/
theorem root_comp_eq_zero_of_isCentral
    {T Z : CommGroupScheme (Spec (CommRingCat.of K))}
    (i : T.toGrp ⟶ G) (w : Z ⟶ T)
    (hc : IsCentral (CommGroupScheme.groupHom w ≫ i))
    {α : characterLattice T} (hα : α ∈ roots i) :
    w ≫ α = 0 := by
  apply CommGroupScheme.hom_ext_points
  intro U x
  apply Over.OverMorphism.ext
  refine Scheme.Cover.hom_ext U.left.affineOpenCover.openCover _ _ fun j => ?_
  let V : Over (Spec (CommRingCat.of K)) :=
    Over.mk (U.left.affineOpenCover.f j ≫ U.hom)
  let f : V ⟶ U := Over.homMk (U.left.affineOpenCover.f j) rfl
  have : IsAffine V.left := by
    change IsAffine (Spec (U.left.affineOpenCover.X j))
    infer_instance
  have hp := pointCharacters_root_eq_one_of_isCentral i
    (CommGroupScheme.groupHom w) hc V (f ≫ x) hα
  have he :
      f ≫ (x ≫ (CommGroupScheme.groupHom (w ≫ α)).hom.hom) =
        f ≫ (x ≫ (CommGroupScheme.groupHom (0 : characterLattice Z)).hom.hom) := by
    apply (Gm.pointsEquiv _ V).injective
    rw [comp_groupHom_zero, MonObj.comp_one, map_one]
    simpa only [comp_groupHom_comp, characterLattice.pointCharacters_apply,
      Category.assoc] using hp
  exact congrArg CommaMorphism.left he

namespace TitsIndexData

variable (d : TitsIndexData G) (hsc : IsSimplyConnected G)

/-- The actual fundamental character of the split absolute torus at a vertex,
using simple connectedness to obtain the integral simple-coroot basis. -/
def absoluteFundamentalCharacter (a : d.Vertex) :
    characterLattice
      ((CommGroupScheme.baseChange (algebraBaseMap K (SeparableClosure K))).obj
        d.pinning.torus) :=
  Langlands.RootDatum.fundamentalWeightBasis d.pinning.rootDatum d.pinning.base
    (d.pinning_corootSpan_eq_top hsc) a

/-- Restriction of an actual absolute fundamental character to a supplied
commutative subgroup scheme of the split absolute torus. -/
def centralFundamentalCharacter
    {Z : CommGroupScheme (Spec (CommRingCat.of (SeparableClosure K)))}
    (w : Z ⟶ (CommGroupScheme.baseChange (algebraBaseMap K (SeparableClosure K))).obj
      d.pinning.torus) (a : d.Vertex) :
    characterLattice Z :=
  w ≫ d.absoluteFundamentalCharacter hsc a

/-- The three fundamental leaf characters of D4 have zero sum on every
central subgroup mapped into the absolute torus, in every characteristic. -/
theorem centralFundamentalCharacter_D4_leaf_sum_eq_zero
    (e : d.Vertex ≃ Fin 4)
    (hD : ∀ a b, d.cartan a b = CartanMatrix.D 4 (e a) (e b))
    {Z : CommGroupScheme (Spec (CommRingCat.of (SeparableClosure K)))}
    (w : Z ⟶ (CommGroupScheme.baseChange (algebraBaseMap K (SeparableClosure K))).obj
      d.pinning.torus)
    (hc : IsCentral
      (CommGroupScheme.groupHom w ≫
        (GroupScheme.baseChange (algebraBaseMap K (SeparableClosure K))).map
          d.pinning.inclusion)) :
    d.centralFundamentalCharacter hsc w (e.symm 0) +
      d.centralFundamentalCharacter hsc w (e.symm 2) +
      d.centralFundamentalCharacter hsc w (e.symm 3) = 0 := by
  have : IsAffineHom
      ((GroupScheme.baseChange (algebraBaseMap K (SeparableClosure K))).obj G).X.hom := by
    change IsAffineHom
      (Limits.pullback.snd G.X.hom (algebraBaseMap K (SeparableClosure K)))
    infer_instance
  have : LocallyOfFiniteType
      ((GroupScheme.baseChange (algebraBaseMap K (SeparableClosure K))).obj G).X.hom := by
    change LocallyOfFiniteType
      (Limits.pullback.snd G.X.hom (algebraBaseMap K (SeparableClosure K)))
    infer_instance
  have hroot (a : d.pinning.rootIndex) :
      w ≫ d.pinning.rootDatum.root a = 0 := by
    have hα : d.pinning.rootDatum.root a ∈ roots
        ((GroupScheme.baseChange (algebraBaseMap K (SeparableClosure K))).map
          d.pinning.inclusion) :=
      d.pinning.isRootDatum.2.1 ▸ ⟨a, rfl⟩
    exact root_comp_eq_zero_of_isCentral (K := SeparableClosure K)
      (G := (GroupScheme.baseChange (algebraBaseMap K (SeparableClosure K))).obj G)
      (T := (CommGroupScheme.baseChange (algebraBaseMap K (SeparableClosure K))).obj
        d.pinning.torus) (Z := Z)
      ((GroupScheme.baseChange (algebraBaseMap K (SeparableClosure K))).map
        d.pinning.inclusion) w hc hα
  unfold centralFundamentalCharacter absoluteFundamentalCharacter
  rw [← Preadditive.comp_add, ← Preadditive.comp_add]
  change w ≫ Langlands.RootDatum.d4LeafWeightSum d.pinning.rootDatum d.pinning.base
    (d.pinning_corootSpan_eq_top hsc) e = 0
  rw [Langlands.RootDatum.d4LeafWeightSum_eq _ _ _ _ hD]
  simp only [Preadditive.comp_add, Preadditive.comp_zsmul, hroot,
    smul_zero, add_zero]

end TitsIndexData

end Langlands.GroupScheme
