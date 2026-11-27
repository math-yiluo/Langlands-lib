import Langlands.GroupScheme.Descent.GaloisSubgroupTransport
import Langlands.GroupScheme.Reductive.StarActionFiniteStageTower
import Langlands.GroupScheme.Torus.MultiplicativeTypeAbsoluteEquivalenceProof

/-! # Canonical transport of subgroup functors along a tower -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.SubgroupFunctor

open StarActionFiniteStage MultiplicativeTypeAbsoluteEquivalence

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1100000

section Schemes

variable {B S K : Scheme.{u}} (b : S ⟶ B) (j : K ⟶ S) (c : K ⟶ B)
  (hc : j ≫ b = c) (G : GroupScheme B)

/-- Base change from the intermediate base, read on the direct pullback of
the original ambient group. -/
def towerBaseChange (A : SubgroupFunctor ((GroupScheme.baseChange b).obj G)) :
    SubgroupFunctor ((GroupScheme.baseChange c).obj G) :=
  (A.baseChange j).comap (groupTowerIsoOf b j c hc G).hom

/-- The subgroup comparison on a tower commutes with compatible
endomorphisms of the intermediate and upper bases. -/
theorem towerBaseChange_descentTransport
    (aS : S ⟶ S) (haS : aS ≫ b = b) (aK : K ⟶ K) (haK : aK ≫ c = c)
    (h : j ≫ aS = aK ≫ j)
    (A : SubgroupFunctor ((GroupScheme.baseChange b).obj G)) :
    towerBaseChange b j c hc G (descentTransport b aS haS G A) =
      descentTransport c aK haK G (towerBaseChange b j c hc G A) := by
  subst c
  apply SubgroupFunctor.ext
  intro U
  apply Subgroup.ext
  intro x
  unfold towerBaseChange
  rw [mem_comap, mem_baseChange, mem_descentTransport_iff_descentPoint,
    mem_descentTransport_iff_descentPoint, mem_comap, mem_baseChange]
  simp only [groupTowerIsoOf, eqToIso_refl, Iso.refl_trans]
  rw [← towerTestHom_comp_descentPoint b j G aS haS aK haK h U x]
  let e : (Over.map j).obj ((Over.map aK).obj U) ≅ (Over.map aS).obj ((Over.map j).obj U) :=
    Over.isoMk (Iso.refl U.left) (by
      change 𝟙 U.left ≫ (U.hom ≫ j) ≫ aS = (U.hom ≫ aK) ≫ j
      rw [Category.id_comp, Category.assoc, h, Category.assoc])
  have he : towerTestHom j aS aK h U = e.hom := Over.OverMorphism.ext rfl
  rw [he]
  constructor
  · exact A.comp_mem e.hom
  · intro hx
    simpa only [Iso.inv_hom_id_assoc] using A.comp_mem e.inv hx

end Schemes

variable {k : Type u} [Field k] (L : IntermediateField k (SeparableClosure k))
  [Normal k L] (G : GroupScheme (Spec (CommRingCat.of k)))

/-- An absolute coefficient automorphism acts on an extended subgroup by
the transport of its restriction to the intermediate field. -/
theorem towerBaseChange_galoisTransport (σ : SeparableClosure k ≃ₐ[k] SeparableClosure k)
    (A : SubgroupFunctor ((GroupScheme.baseChange (algebraBaseMap k L)).obj G)) :
    towerBaseChange (algebraBaseMap k L) (algebraBaseMap L (SeparableClosure k))
        (algebraBaseMap k (SeparableClosure k)) (algebraBaseMap_tower L (SeparableClosure k)) G
        (galoisTransport k L G (σ.restrictNormal L) A) =
      galoisTransport k (SeparableClosure k) G σ
        (towerBaseChange (algebraBaseMap k L) (algebraBaseMap L (SeparableClosure k))
          (algebraBaseMap k (SeparableClosure k)) (algebraBaseMap_tower L (SeparableClosure k)) G A) := by
  exact towerBaseChange_descentTransport _ _ _ _ G _ _ _ _
    (galoisBaseMap_restrictNormal L σ) A

end Langlands.GroupScheme.SubgroupFunctor
