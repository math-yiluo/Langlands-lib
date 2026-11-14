import Langlands.GroupScheme.Reductive.SplitRankOnePowerGeometry
import Langlands.GroupScheme.OpenCellIsogeny

/-! # Rank-one isogenies with characteristic-power root maps -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.RootCell

variable {k : Type u} [Field k]
    {T T' : CommGroupScheme (Spec (CommRingCat.of k))}
    {G G' : GroupScheme (Spec (CommRingCat.of k))}
    {i : T.toGrp ⟶ G} {i' : T'.toGrp ⟶ G'}
    {χ : characterLattice T} {χv : cocharacterLattice T}
    {χ' : characterLattice T'} {χv' : cocharacterLattice T'}
    {xp xm : Ga k ⟶ G} {xp' xm' : Ga k ⟶ G'}

/-- The actual homomorphism obtained by gluing the characteristic-power root-cell map. -/
def powerHom (hG : IsConnectedReductive G)
    (D : IsRootCell i χ χv xp xm) (D' : IsRootCell i' χ' χv' xp' xm')
    (t : T ⟶ T') (p e : ℕ) [ExpChar k p] (hχ : t ≫ χ' = p ^ e • χ)
    (hχv : χv ≫ t = p ^ e • χv') : G ⟶ G' :=
  Classical.choose (exists_powerHom hG D D' t p e hχ hχv)

/-- The chosen homomorphism has the prescribed torus, root and full-cell restrictions. -/
theorem powerHom_spec (hG : IsConnectedReductive G)
    (D : IsRootCell i χ χv xp xm) (D' : IsRootCell i' χ' χv' xp' xm')
    (t : T ⟶ T') (p e : ℕ) [ExpChar k p] (hχ : t ≫ χ' = p ^ e • χ)
    (hχv : χv ≫ t = p ^ e • χv') :
    let φ := powerHom hG D D' t p e hχ hχv
    i ≫ φ = CommGroupScheme.groupHom t ≫ i' ∧
      xm.hom.hom ≫ φ.hom.hom = gaPower (p ^ e) ≫ xm'.hom.hom ∧
      xp.hom.hom ≫ φ.hom.hom = gaPower (p ^ e) ≫ xp'.hom.hom ∧
      Dynamic.tripleCellMultiplication xm i xp ≫ φ.hom.hom =
        powerCell t (p ^ e) ≫ Dynamic.tripleCellMultiplication xm' i' xp' :=
  Classical.choose_spec (exists_powerHom hG D D' t p e hχ hχv)

/-- A characteristic-power homomorphism is an actual isogeny when its middle map
is an isogeny and both ambient groups are connected reductive. -/
theorem powerHom_isIsogeny (hG : IsConnectedReductive G) (hG' : IsConnectedReductive G')
    (D : IsRootCell i χ χv xp xm) (D' : IsRootCell i' χ' χv' xp' xm')
    (t : T ⟶ T') (ht : IsIsogeny (CommGroupScheme.groupHom t))
    (p e : ℕ) [ExpChar k p] (hχ : t ≫ χ' = p ^ e • χ)
    (hχv : χv ≫ t = p ^ e • χv') :
    IsIsogeny (powerHom hG D D' t p e hχ hχv) := by
  have := hG.smooth
  have := hG.isAffineHom
  have := hG'.smooth
  have := hG'.isAffineHom
  have := hG'.connectedSpace
  have := D.isOpenImmersion
  have := D'.isOpenImmersion
  have : IsFinite (CommGroupScheme.groupHom t).hom.hom.left := ht.1
  have : Surjective (CommGroupScheme.groupHom t).hom.hom.left := ht.2.2
  have hq : 0 < p ^ e := pow_pos (Nat.pos_of_ne_zero (expChar_ne_zero k p)) e
  have : IsFinite (powerCell t (p ^ e)).left := powerCell_isFinite t hq
  have : Surjective (powerCell t (p ^ e)).left := powerCell_surjective t hq
  apply OpenCellGeometry.isIsogeny_of_cell _
    (Dynamic.tripleCellMultiplication xm i xp)
    (Dynamic.tripleCellMultiplication xm' i' xp') (powerCell t (p ^ e)) (unitPt T)
  · exact unitPt_comp.trans (MonObj.one_eq_one G.X).symm
  · exact (powerHom_spec hG D D' t p e hχ hχv).2.2.2

/-- Supplied root cells and a torus isogeny satisfying both root lattice equations
are realized by a group isogeny with the prescribed two root powers. -/
theorem exists_powerIsogeny (hG : IsConnectedReductive G) (hG' : IsConnectedReductive G')
    (D : IsRootCell i χ χv xp xm) (D' : IsRootCell i' χ' χv' xp' xm')
    (t : T ⟶ T') (ht : IsIsogeny (CommGroupScheme.groupHom t))
    (p e : ℕ) [ExpChar k p] (hχ : t ≫ χ' = p ^ e • χ)
    (hχv : χv ≫ t = p ^ e • χv') :
    ∃ φ : G ⟶ G', IsIsogeny φ ∧
      i ≫ φ = CommGroupScheme.groupHom t ≫ i' ∧
      xm.hom.hom ≫ φ.hom.hom = gaPower (p ^ e) ≫ xm'.hom.hom ∧
      xp.hom.hom ≫ φ.hom.hom = gaPower (p ^ e) ≫ xp'.hom.hom ∧
      Dynamic.tripleCellMultiplication xm i xp ≫ φ.hom.hom =
        powerCell t (p ^ e) ≫ Dynamic.tripleCellMultiplication xm' i' xp' :=
  ⟨powerHom hG D D' t p e hχ hχv,
    powerHom_isIsogeny hG hG' D D' t ht p e hχ hχv,
    powerHom_spec hG D D' t p e hχ hχv⟩

end Langlands.GroupScheme.RootCell
