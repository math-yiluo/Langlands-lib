import Langlands.GroupScheme.ImmersionFromIdentityCell
import Langlands.GroupScheme.Dynamic.MonomorphismCellClosedImmersion

/-! # Immersions from closed dynamic centralizer restrictions -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme.Dynamic

variable {S : Scheme.{u}}

/-- The tuple of the identity sections in the three factors of a triple cell. -/
def tripleCellIdentity (M Z U : GroupScheme S) :
    𝟙_ (Over S) ⟶ M.X ⊗ (Z.X ⊗ U.X) :=
  lift η[M.X] (lift η[Z.X] η[U.X])

@[simp]
theorem tripleCellIdentity_comp {G M Z U : GroupScheme S}
    (iM : M ⟶ G) (iZ : Z ⟶ G) (iU : U ⟶ G) :
    tripleCellIdentity M Z U ≫ tripleCellMultiplication iM iZ iU = 1 := by
  rw [tripleCellIdentity, lift_tripleCellMultiplication, IsMonHom.one_hom,
    IsMonHom.one_hom, IsMonHom.one_hom]
  simp only [MonObj.one_eq_one, one_mul]

variable {H G MH ZH UH MG ZG UG : GroupScheme S}
    (χ : (Gm S).toGrp ⟶ H) (f : H ⟶ G)
    {iM : MH ⟶ H} {iZ : ZH ⟶ H} {iU : UH ⟶ H}
    {jM : MG ⟶ G} {jZ : ZG ⟶ G} {jU : UG ⟶ G}
    (hM : (unipotent (CommGroupScheme.groupHom
      (Gm.powerHom S (-1)) ≫ χ)).IsRepresentedBy iM)
    (hZ : (centralizer χ).IsRepresentedBy iZ)
    (hU : (unipotent χ).IsRepresentedBy iU)
    (hMG : (unipotent (CommGroupScheme.groupHom
      (Gm.powerHom S (-1)) ≫ (χ ≫ f))).IsRepresentedBy jM)
    (hZG : (centralizer (χ ≫ f)).IsRepresentedBy jZ)
    (hUG : (unipotent (χ ≫ f)).IsRepresentedBy jU)
    [Smooth H.X.hom] [IsAffineHom H.X.hom] [GeometricallyConnected H.X.hom]
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [Mono f.hom.hom]

include χ hM hZ hU hMG hZG hUG in
/-- A monomorphism of smooth affine groups with geometrically connected source
is an immersion if its restriction to a dynamic centralizer is closed. -/
theorem isImmersion_of_isClosedSubgroup_centralizer
    (hz : IsClosedSubgroup
      (hZ.restrictionHom hZG f (centralizer_le_comap χ f))) :
    IsImmersion f.hom.hom.left := by
  have : IsOpenImmersion (tripleCellMultiplication jM jZ jU).left :=
    isOpenImmersion_tripleCellMultiplication_overBase (χ ≫ f) hMG hZG hUG
  have : IsClosedImmersion (tripleCellFactor χ f hM hZ hU hMG hZG hUG).left :=
    isClosedImmersion_tripleCellFactor χ f hM hZ hU hMG hZG hUG hz
  have hs : IsPullback (tripleCellMultiplication iM iZ iU)
      (tripleCellFactor χ f hM hZ hU hMG hZG hUG) f.hom.hom
      (tripleCellMultiplication jM jZ jU) := by
    apply IsPullback.of_map_of_faithful (Over.forget S)
    exact (isPullback_tripleCellFactor χ f hM hZ hU hMG hZG hUG).flip
  exact IdentityCell.isImmersion_of_isPullback f
    (tripleCellMultiplication jM jZ jU) (tripleCellMultiplication iM iZ iU)
    (tripleCellFactor χ f hM hZ hU hMG hZG hUG) hs
    (tripleCellIdentity MG ZG UG) (tripleCellIdentity_comp jM jZ jU)

end Langlands.GroupScheme.Dynamic
