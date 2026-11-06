import Langlands.GroupScheme.Rational.AnisotropicCompactnessProof
import Langlands.GroupScheme.Rational.AnisotropicRootSystem
import Langlands.GroupScheme.Rational.RootSubgroup
import Langlands.GroupScheme.Dynamic.CentralizerReductiveTransport
import Langlands.Representation.Plancherel.RationalCharacterTopology

/-! # Anisotropic centralizers and their full rational norm kernels -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]
variable {G Z : GroupScheme (Spec (CommRingCat.of k))}
variable {S : CommGroupScheme (Spec (CommRingCat.of k))} {i : S.toGrp ⟶ G}

/-- A split subtorus in an anisotropic group has the full all-test centralizer. -/
theorem IsAnisotropic.torusCentralizer_eq_top (hG : IsAnisotropic G)
    (hi : IsSplitSubtorus i) : torusCentralizer i = ⊤ := by
  let i₀ : S.toGrp ⟶ G := homOfPoints (fun _ => 1) (by
    intro T T' a x
    exact (MonObj.comp_one a).symm)
  have := hG.subsingleton_hom_of_isSplitSubtorus hi G
  have h : i = i₀ := Subsingleton.elim _ _
  apply SubgroupFunctor.ext
  intro T
  apply top_unique
  intro g _ T' a t
  rw [h]
  change Commute (a ≫ g)
    (t ≫ (homOfPoints (fun _ => 1) _).hom.hom)
  rw [comp_homOfPoints]
  exact Commute.one_right _

/-- Every supplied representative of that centralizer is isomorphic to the ambient group. -/
def IsAnisotropic.torusCentralizerIso (hG : IsAnisotropic G)
    (hi : IsSplitSubtorus i) {j : Z ⟶ G}
    (hj : (torusCentralizer i).IsRepresentedBy j) : Z ≅ G :=
  (show (⊤ : SubgroupFunctor G).IsRepresentedBy j from
    (hG.torusCentralizer_eq_top hi) ▸ hj).topIso

@[simp] theorem IsAnisotropic.torusCentralizerIso_hom (hG : IsAnisotropic G)
    (hi : IsSplitSubtorus i) {j : Z ⟶ G}
    (hj : (torusCentralizer i).IsRepresentedBy j) :
    (hG.torusCentralizerIso hi hj).hom = j :=
  SubgroupFunctor.IsRepresentedBy.topIso_hom _

section LocalField

variable [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

/-- All rational points of a connected reductive anisotropic group lie in its norm kernel. -/
theorem IsAnisotropic.rationalCommonNormKernel_eq_top (hG : IsAnisotropic G)
    (hred : IsConnectedReductive G) : Plancherel.rationalCommonNormKernel G = ⊤ := by
  let : IsAffineHom G.X.hom := hred.isAffineHom
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let : TopologicalSpace (rationalPoints G) := rationalPointTopology k G.X
  apply top_unique
  apply Plancherel.compactSubgroup_le_rationalCommonNormKernel
  simpa only [Subgroup.coe_top] using
    (anisotropicCompactness_proof k G hred).mpr hG

/-- The entire rational image of an anisotropic split-torus centralizer is its norm-kernel image. -/
theorem IsAnisotropic.map_normKernel_torusCentralizer_eq_range (hG : IsAnisotropic G)
    (hred : IsConnectedReductive G) (hi : IsSplitSubtorus i) {j : Z ⟶ G}
    (hj : (torusCentralizer i).IsRepresentedBy j) :
    (Plancherel.rationalCommonNormKernel Z).map (rationalPoints.map j) =
      (rationalPoints.map j).range := by
  let e := hG.torusCentralizerIso hi hj
  have hZ : IsAnisotropic Z := by
    change splitRank Z = 0
    rw [splitRank_eq_of_iso e]
    exact hG
  rw [hZ.rationalCommonNormKernel_eq_top (hred.of_iso e), Subgroup.map_top]

/-- The anisotropic case of rank-one centralizer generation needs only the norm-kernel term. -/
theorem IsAnisotropic.centralizer_le_rankOne_sup_normKernel [IsAffineHom G.X.hom]
    (hG : IsAnisotropic G) (hred : IsConnectedReductive G)
    (hi : IsSplitSubtorus i) {j : Z ⟶ G}
    (hj : (torusCentralizer i).IsRepresentedBy j) :
    (rationalPoints.map j).range ≤
      Subgroup.closure (⋃ a ∈ relativeRoots i,
          ((centralizerPoints i ⊓ Subgroup.closure
            (((RelativeRoot.subgroup i a).carrier (Over.mk (𝟙 _)) :
                Set (rationalPoints G)) ∪
              (RelativeRoot.subgroup i (-a)).carrier (Over.mk (𝟙 _))) :
            Subgroup (rationalPoints G)) : Set (rationalPoints G))) ⊔
        (Plancherel.rationalCommonNormKernel Z).map (rationalPoints.map j) := by
  rw [hG.map_normKernel_torusCentralizer_eq_range hred hi hj]
  exact le_sup_right

end LocalField

end Langlands.GroupScheme
