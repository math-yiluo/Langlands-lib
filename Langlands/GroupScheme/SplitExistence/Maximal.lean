import Langlands.GroupScheme.SplitExistence.Centralizer
import Langlands.GroupScheme.Torus.MaximalSelfCentralizing
import Langlands.GroupScheme.Torus.Lattice

/-! # The torus is a maximal torus of the Chevalley group

The centralizer of the torus lies in the centralizer of the regular cocharacter, which is the
torus. So the torus is self-centralizing, hence maximal (Library
`isMaximalTorus_of_torusCentralizer_eq`). -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.SplitExistence

namespace ChevalleyData

variable {J X Y : Type u} [AddCommGroup X] [AddCommGroup Y] {P : RootDatum J X Y} {b : P.Base}
  {D : ChevalleyData P b} {k : Type u} [Field k]

namespace ChevGroup

variable (G : D.ChevGroup k)

/-- Points centralizing the torus centralize the regular cocharacter. -/
theorem torusCentralizer_le_centralizer :
    torusCentralizer G.t ≤ Dynamic.centralizer G.cochar := by
  intro U g hg
  rw [Dynamic.mem_centralizer]
  have h := hg (U ⊗ (Gm (Spec (CommRingCat.of k))).X) (fst _ _)
    (snd _ _ ≫ (D.cochar k).hom.hom)
  have hc : snd U (Gm (Spec (CommRingCat.of k))).X ≫ G.cochar.hom.hom =
      (snd _ _ ≫ (D.cochar k).hom.hom) ≫ G.t.hom.hom := by
    rw [ChevGroup.cochar, Grp.comp_hom_hom, Category.assoc]
  rw [Dynamic.orbit, hc, ← h.eq, mul_assoc, mul_inv_cancel, mul_one]

/-- Points of the torus centralize the torus. -/
theorem range_le_torusCentralizer :
    SubgroupFunctor.range G.t ≤ torusCentralizer G.t := by
  rintro U g ⟨y, rfl⟩ V a s
  change U ⟶ (Tk (X := X) k).toGrp.X at y
  change Commute (a ≫ y ≫ G.t.hom.hom) (s ≫ G.t.hom.hom)
  have hcomm : (a ≫ y) * s = s * (a ≫ y) := mul_comm _ _
  change (a ≫ y ≫ G.t.hom.hom) * (s ≫ G.t.hom.hom) = (s ≫ G.t.hom.hom) * (a ≫ y ≫ G.t.hom.hom)
  rw [← Category.assoc, ← MonObj.mul_comp, ← MonObj.mul_comp, hcomm]

theorem torusCentralizer_eq [Finite J] [P.IsReduced] [Module.Finite ℤ X] :
    torusCentralizer G.t = SubgroupFunctor.range G.t :=
  le_antisymm (G.torusCentralizer_le_centralizer.trans G.centralizer_le)
    G.range_le_torusCentralizer

/-- **The torus `D(X)` is a maximal torus of the Chevalley group.** -/
theorem isMaximalTorus [Finite J] [P.IsReduced] [Module.Finite ℤ X] : IsMaximalTorus G.t :=
  isMaximalTorus_of_torusCentralizer_eq (isSplitTorus_Tk k P).isTorus G.t_closed
    G.torusCentralizer_eq

end ChevGroup

end ChevalleyData

end Langlands.GroupScheme.SplitExistence
