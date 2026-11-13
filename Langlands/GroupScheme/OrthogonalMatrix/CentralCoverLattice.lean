import Langlands.GroupScheme.OrthogonalMatrix.CorootLattice
import Langlands.GroupScheme.OrthogonalMatrix.Reductive
import Langlands.GroupScheme.CentralIsogeny.SimplyConnectedCorootImage

/-! # The integral lattice index of a simply connected cover of split even orthogonal groups -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme.OrthogonalMatrix

variable {l : Type} [Fintype l] [DecidableEq l] {k : Type u} [Field k]

local notation "𝔻" => splitTorus.commGroupScheme (Spec (CommRingCat.of k)) (ULift l)
local notation "𝐆" => identityComponent (groupScheme l (CommRingCat.of k))

variable {S : GroupScheme (Spec (CommRingCat.of k))}
  {T : CommGroupScheme (Spec (CommRingCat.of k))} {p : S ⟶ identityComponent (groupScheme l (CommRingCat.of k))}
  (hp : IsCentralIsogeny p) (hS : IsSimplyConnected S) (hT : IsSplitTorus T.toGrp)
  {i : T.toGrp ⟶ S} (hi : IsMaximalTorus i) (t : T ⟶ splitTorus.commGroupScheme (Spec (CommRingCat.of k)) (ULift l))
  (ht : i ≫ p = CommGroupScheme.groupHom t ≫ identityTorus l k)
  (hl : 3 ≤ Fintype.card l)

include hp hS hT hi ht hl

/-- The image of cocharacter pushforward in the standard orthogonal coordinates is the
integral lattice of vectors with even coordinate sum. -/
theorem map_range_cocharacterMapInt_eq_pairLattice :
    (LinearMap.range (RealTorusSpace.cocharacterMapInt t)).map
      (GeneralLinear.cocharacterCoordEquiv l k).toLinearMap =
        TypeDParityLattice.pairLattice l := by
  have : Nontrivial l := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  let hG := isConnectedReductive_identityComponent l k
  have := hG.isAffineHom
  obtain ⟨J, _, P, hP, _⟩ := rootDatumExistence k 𝐆 hG 𝔻
    (SymplecticMatrix.isSplitTorus_diagonalTorus l k) (identityTorus l k)
    (isMaximalTorus_identityTorus l k)
  rw [hp.range_cocharacterMapInt_eq_corootSpan hS hG hT
    (SymplecticMatrix.isSplitTorus_diagonalTorus l k) hi
    (isMaximalTorus_identityTorus l k) t ht P hP]
  exact map_corootSpan_eq_pairLattice hP hl

/-- The equivalent range formula for pushforward followed by standard coordinates. -/
theorem range_cocharacterCoord_eq_pairLattice :
    LinearMap.range ((GeneralLinear.cocharacterCoordEquiv l k).toLinearMap.comp
      (RealTorusSpace.cocharacterMapInt t)) = TypeDParityLattice.pairLattice l := by
  rw [LinearMap.range_comp]
  exact map_range_cocharacterMapInt_eq_pairLattice hp hS hT hi t ht hl

/-- The quotient by the actual cocharacter image of a simply connected orthogonal cover
is linearly equivalent over the integers to `ZMod 2`. -/
def centralCoverQuotientEquiv :
    (cocharacterLattice 𝔻 ⧸ LinearMap.range (RealTorusSpace.cocharacterMapInt t)) ≃ₗ[ℤ]
      ZMod 2 := by
  letI : Nontrivial l := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  exact (Submodule.Quotient.equiv _ _ (GeneralLinear.cocharacterCoordEquiv l k)
    (map_range_cocharacterMapInt_eq_pairLattice hp hS hT hi t ht hl)).trans
      TypeDParityLattice.quotientEquiv

/-- The cocharacter image has index exactly two, over fields of every characteristic. -/
theorem card_centralCoverQuotient :
    Nat.card (cocharacterLattice 𝔻 ⧸ LinearMap.range (RealTorusSpace.cocharacterMapInt t)) = 2 := by
  rw [Nat.card_congr (centralCoverQuotientEquiv hp hS hT hi t ht hl).toEquiv,
    Nat.card_eq_fintype_card, ZMod.card]

end Langlands.GroupScheme.OrthogonalMatrix
