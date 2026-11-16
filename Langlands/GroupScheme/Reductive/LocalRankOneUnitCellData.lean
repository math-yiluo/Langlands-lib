import Langlands.GroupScheme.Reductive.LocalRankOneUnitCell

/-! # Affine neighbourhoods with unit cell coordinates -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.GroupScheme.LocalRankOneUnitCell

open RingRootCell

variable {R : Type u} [CommRing R] (D : CellData R)
  {Z : Over (Spec (CommRingCat.of R))} (g : Z ⟶ D.G.X)
  {k : Type u} [Field k] (b : Spec (CommRingCat.of k) ⟶ Z.left)

/-- An affine open retaining a field point, with unit coordinates for the
restriction of an actual group-valued section. -/
structure AffineUnitCellData where
  ring : CommRingCat.{u}
  inclusion : Spec ring ⟶ Z.left
  openImmersion : IsOpenImmersion inclusion
  point : Spec (CommRingCat.of k) ⟶ Spec ring
  point_comp : point ≫ inclusion = b
  beta : Γ(Spec ring, ⊤)
  torus : Over.mk (inclusion ≫ Z.hom) ⟶ D.T.X
  delta : Γ(Spec ring, ⊤)
  unit_beta : IsUnit beta
  unit_delta : IsUnit delta
  factorization : Over.homMk inclusion rfl ≫ g = D.cellPt beta torus delta

/-- If a section has unit cell coordinates at a field point, it has unit
cell coordinates on an affine open neighbourhood retaining that exact point. -/
def affineUnitCell
    (beta : Γ(Spec (CommRingCat.of k), ⊤))
    (torus : Over.mk (b ≫ Z.hom) ⟶ D.T.X)
    (delta : Γ(Spec (CommRingCat.of k), ⊤))
    (hbeta : IsUnit beta) (hdelta : IsUnit delta)
    (hcell : Over.homMk b rfl ≫ g = D.cellPt beta torus delta) :
    AffineUnitCellData D g b := Classical.choice <| by
  let V : Z.left.Opens :=
    ⟨g.left ⁻¹' Set.range D.cellMul.left,
      (D.open_cell.isOpen_range D.cellMul.left).preimage g.left.continuous⟩
  have hbV : b default ∈ V := by
    have hbcell : D.InCell (Over.homMk b rfl ≫ g) :=
      (D.inCell_iff _).mpr ⟨beta, torus, delta, hcell⟩
    have h := D.range_subset_of_inCell hbcell
    exact h ⟨(default : Spec (CommRingCat.of k)), rfl⟩
  obtain ⟨U, hU, hbU, hUV⟩ := exists_isAffineOpen_mem_and_subset hbV
  let e := hU.fromSpec
  let W : Over (Spec (CommRingCat.of R)) := Over.mk (e ≫ Z.hom)
  let j : W ⟶ Z := Over.homMk e rfl
  have hb_range : Set.range b ⊆ Set.range e := by
    rw [hU.range_fromSpec]
    rintro _ ⟨x, rfl⟩
    rw [show x = default from Subsingleton.elim _ _]
    exact hbU
  let c := IsOpenImmersion.lift e b hb_range
  have hc : c ≫ e = b := IsOpenImmersion.lift_fac ..
  have hWcell : D.InCell (j ≫ g) := by
    apply D.inCell_of_range_subset
    rintro _ ⟨w, rfl⟩
    exact hUV (by
      change e w ∈ U
      have he : e w ∈ Set.range hU.fromSpec := ⟨w, rfl⟩
      rw [hU.range_fromSpec] at he
      exact he)
  obtain ⟨y, t, x, hfactor⟩ := (D.inCell_iff _).mp hWcell
  let c' : Over.mk (b ≫ Z.hom) ⟶ W :=
    Over.homMk c (by dsimp [W]; rw [← Category.assoc, hc])
  have hcy : c.appTop y = beta ∧ c' ≫ t = torus ∧ c.appTop x = delta := by
    change c'.left.appTop y = beta ∧ c' ≫ t = torus ∧ c'.left.appTop x = delta
    apply D.cellPt_inj (Z := Over.mk (b ≫ Z.hom))
    rw [← D.comp_cellPt, ← hfactor, ← Category.assoc, ← hcell]
    congr 1
    apply Over.OverMorphism.ext
    exact hc
  let E := affineUnitRestriction c y x
    (hcy.1.symm ▸ hbeta) (hcy.2.2.symm ▸ hdelta)
  let W' : Over (Spec (CommRingCat.of R)) :=
    Over.mk ((E.inclusion ≫ e) ≫ Z.hom)
  let q : W' ⟶ W := Over.homMk E.inclusion (by
    dsimp [W, W']
    rw [Category.assoc])
  have : IsOpenImmersion (E.inclusion ≫ e) := by
    have := E.openImmersion
    infer_instance
  refine ⟨{ ring := E.ring, inclusion := E.inclusion ≫ e
            openImmersion := this, point := E.point
            point_comp := ?_, beta := E.inclusion.appTop y
            torus := q ≫ t, delta := E.inclusion.appTop x
            unit_beta := E.unit_left, unit_delta := E.unit_right
            factorization := ?_ }⟩
  · rw [← Category.assoc, E.point_comp, hc]
  · change (q ≫ j) ≫ g = _
    rw [Category.assoc, hfactor, D.comp_cellPt]
    rfl

end Langlands.GroupScheme.LocalRankOneUnitCell
