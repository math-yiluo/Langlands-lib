import Langlands.GroupScheme.Reductive.CenterInMaximalTorus
import Langlands.GroupScheme.Reductive.CenterBaseChangeProof
import Langlands.GroupScheme.SimplyConnected.TypeD4CentralCharacters
import Langlands.GroupScheme.Torus.WeilRestrictionNormOneCharacters

/-! # Actual centre characters of a simply connected group and the D4 relation -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.TitsIndexData

variable {K : Type u} [Field K]
    {G : GroupScheme (Spec (CommRingCat.of K))}
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
    (d : TitsIndexData G)

local instance absoluteGroupAffine :
    IsAffineHom
      ((GroupScheme.baseChange (algebraBaseMap K (SeparableClosure K))).obj G).X.hom := by
  change IsAffineHom
    (Limits.pullback.snd G.X.hom (algebraBaseMap K (SeparableClosure K)))
  infer_instance

local instance absoluteGroupLocallyOfFiniteType :
    LocallyOfFiniteType
      ((GroupScheme.baseChange (algebraBaseMap K (SeparableClosure K))).obj G).X.hom := by
  change LocallyOfFiniteType
    (Limits.pullback.snd G.X.hom (algebraBaseMap K (SeparableClosure K)))
  infer_instance

/-- An actual full centre over the ground field, factored through the
ground-field maximal torus in the index data. -/
def toralCenter : CenterInMaximalTorus d.pinning.inclusion :=
  centerInMaximalTorus d.isSemisimple.isConnectedReductive
    d.pinning.inclusion d.maximalTorus

/-- The toral centre remains the full scheme-theoretic centre over the
separable closure, with the specified torus factorization. -/
theorem toralCenter_baseChange_isCenter :
    IsSchemeTheoreticCenter
      (CommGroupScheme.groupHom
        ((CommGroupScheme.baseChange (algebraBaseMap K (SeparableClosure K))).map
          d.toralCenter.torusMap) ≫
        (GroupScheme.baseChange (algebraBaseMap K (SeparableClosure K))).map
          d.pinning.inclusion) := by
  have hb := schemeTheoreticCenterBaseChangeStatement K (SeparableClosure K) G
    d.toralCenter.group.toGrp
    (CommGroupScheme.groupHom d.toralCenter.torusMap ≫ d.pinning.inclusion)
    d.isSemisimple.isConnectedReductive d.toralCenter.isCenter
  change IsSchemeTheoreticCenter
    ((GroupScheme.baseChange (algebraBaseMap K (SeparableClosure K))).map
        (CommGroupScheme.groupHom d.toralCenter.torusMap) ≫
      (GroupScheme.baseChange (algebraBaseMap K (SeparableClosure K))).map
        d.pinning.inclusion)
  rw [← Functor.map_comp]
  exact hb

/-- Every actual absolute root restricts to zero on this full centre. -/
theorem toralCenter_root_comp_eq_zero (a : d.pinning.rootIndex) :
    (CommGroupScheme.baseChange (algebraBaseMap K (SeparableClosure K))).map
      d.toralCenter.torusMap ≫ d.pinning.rootDatum.root a = 0 := by
  have hα : d.pinning.rootDatum.root a ∈ roots
      ((GroupScheme.baseChange (algebraBaseMap K (SeparableClosure K))).map
        d.pinning.inclusion) :=
    d.pinning.isRootDatum.2.1 ▸ ⟨a, rfl⟩
  exact root_comp_eq_zero_of_isCentral (K := SeparableClosure K)
    (G := (GroupScheme.baseChange (algebraBaseMap K (SeparableClosure K))).obj G)
    (T := (CommGroupScheme.baseChange (algebraBaseMap K (SeparableClosure K))).obj
      d.pinning.torus)
    (Z := (CommGroupScheme.baseChange (algebraBaseMap K (SeparableClosure K))).obj
      d.toralCenter.group)
    ((GroupScheme.baseChange (algebraBaseMap K (SeparableClosure K))).map
      d.pinning.inclusion)
    ((CommGroupScheme.baseChange (algebraBaseMap K (SeparableClosure K))).map
      d.toralCenter.torusMap) d.toralCenter_baseChange_isCenter.isCentral hα

/-- The actual character of the full geometric centre at a simple vertex. -/
def centerFundamentalCharacter (hsc : IsSimplyConnected G) (a : d.Vertex) :
    characterLattice
      ((CommGroupScheme.baseChange (algebraBaseMap K (SeparableClosure K))).obj
        d.toralCenter.group) :=
  d.centralFundamentalCharacter hsc
    ((CommGroupScheme.baseChange (algebraBaseMap K (SeparableClosure K))).map
      d.toralCenter.torusMap) a

/-- The full ordinary Galois action on the actual centre characters is the
star permutation of the corresponding fundamental weights. -/
theorem centerFundamentalCharacter_galois
    (hsc : IsSimplyConnected G)
    (σ : SeparableClosure K ≃ₐ[K] SeparableClosure K) (a : d.Vertex) :
    characterLattice.galoisRepresentation K (SeparableClosure K)
        d.toralCenter.group σ (d.centerFundamentalCharacter hsc a) =
      d.centerFundamentalCharacter hsc (d.star σ a) := by
  let F := (characterLattice.precompose
    ((CommGroupScheme.baseChange (algebraBaseMap K (SeparableClosure K))).map
      d.toralCenter.torusMap)).toIntLinearMap
  have hker : d.pinning.rootDatum.rootSpan ℤ ≤ LinearMap.ker F := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨j, rfl⟩
    exact d.toralCenter_root_comp_eq_zero j
  let starAut : d.pinning.rootDatum.Aut := (d.pinning.starAction σ).val
  let galoisAut : d.pinning.rootDatum.Aut := d.pinning.galoisAction σ
  have hs :
      starAut.weightEquiv (d.absoluteFundamentalCharacter hsc a) =
        d.absoluteFundamentalCharacter hsc (d.star σ a) := by
    exact Langlands.RootDatum.fundamentalWeightBasis_aut
      d.pinning.rootDatum d.pinning.base (d.pinning_corootSpan_eq_top hsc)
      starAut (d.pinning.starAction σ).property a
  have hc := Langlands.RootDatum.weightEquiv_sub_mem_rootSpan_of_weyl_correction
    d.pinning.rootDatum starAut galoisAut
    (d.pinning.starAction_mul_galoisAction_inv_mem σ)
    (d.absoluteFundamentalCharacter hsc a)
  rw [hs] at hc
  have hzero : F (d.absoluteFundamentalCharacter hsc (d.star σ a) -
      galoisAut.weightEquiv (d.absoluteFundamentalCharacter hsc a)) = 0 :=
    hker hc
  rw [map_sub] at hzero
  have he := (sub_eq_zero.mp hzero).symm
  unfold centerFundamentalCharacter centralFundamentalCharacter
  rw [characterLattice.galoisRepresentation_precompose]
  exact he

/-- The actual full centre characters of the three D4 leaves have zero sum. -/
theorem centerFundamentalCharacter_D4_leaf_sum_eq_zero
    (hsc : IsSimplyConnected G) (e : d.Vertex ≃ Fin 4)
    (hD : ∀ a b, d.cartan a b = CartanMatrix.D 4 (e a) (e b)) :
    d.centerFundamentalCharacter hsc (e.symm 0) +
      d.centerFundamentalCharacter hsc (e.symm 2) +
      d.centerFundamentalCharacter hsc (e.symm 3) = 0 :=
  d.centralFundamentalCharacter_D4_leaf_sum_eq_zero hsc e hD _
    d.toralCenter_baseChange_isCenter.isCentral

end Langlands.GroupScheme.TitsIndexData
