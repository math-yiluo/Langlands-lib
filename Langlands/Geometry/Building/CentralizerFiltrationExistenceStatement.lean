import Langlands.Geometry.Building.KPMoyPrasadFiltration
import Langlands.Geometry.Building.ValuationBuildingAxioms

/-! # Existence of the KP §9.8 filtration of `Z(F)` -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.GroupScheme

namespace Langlands.Geometry.Building

/-- **The filtration of `Z(F)`** (KP §9.8 and Lemma 9.8.1). For every connected reductive group
`G` over a nonarchimedean local field `F` and all parahoric building data `P` of `G` satisfying
V 7 and AS 2–AS 5, the centralizer `Z(F) = Z_G(S)(F)` carries a decreasing separated
filtration `(Z(F)_r)_{r ≥ 0}` with `Z(F)_0 = Z(F)^0`, by open subgroups, that is commutator
friendly (KP Definition 7.2.1), stable under `N(F)`, satisfies
`[Z(F)_r, Z(F)_s] ⊆ Z(F)_{r+s}` and moves each `U_{a,x,s}` into the block
`U_{a,x,r+s} U_{2a,x,r+s}`. -/
def CentralizerFiltrationExistenceStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom]
    (P : ParahoricBuildingData G), P.SatisfiesApartmentAxioms →
      ∃ Zf : P.CentralizerFiltration, Zf.SatisfiesFiltrationAxioms ∧ Zf.IsOpenFiltration

end Langlands.Geometry.Building
