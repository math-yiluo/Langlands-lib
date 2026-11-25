/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.AffineFreeBasisGerms
import WeilConjectures.AlgebraicGeometry.AffineScalarSectionAction

/-! # Scalar action on the unit germ of affine sheafification

Source: Stacks Project, Tag 01HV, Lemma 26.5.4, functoriality, and Tag 0098.
(blueprint: lem-sc-affine-regular-stalk-scalar).
-/

@[expose] public section
universe u
namespace AlgebraicGeometry.Scheme

/-- A scalar endomorphism acts on the explicit unit germ by the scalar's germ.

Source: Stacks Project, Tag 01HV, Lemma 26.5.4, functoriality, and Tag 0098.
(blueprint: lem-sc-affine-regular-stalk-scalar).

Proof: Tilde sends multiplication by a in Gamma(X,U) to multiplication by the
corresponding structure-sheaf section on Spec Gamma(X,U). The affine chart pulls
this section back to a on U: its structure-ring map is the canonical sections map,
as follows from the construction of isoSpec and GammaSpecIso. The regular-module
isomorphism affineRegularSheafIso is tildeSelf, restrictUnitIso, and the unit
isomorphism of overEquiv, so it respects this multiplication. On the slice open
U times U the conjugated endomorphism therefore multiplies by the restriction of a
along the second projection. Under pushforwardOver this restriction is exactly the
scalar action of a on sections over U. Apply the germ map to its value on 1.
PresheafOfModules.germ_smul turns the product into germ(a) times the unit germ,
which is affineRegularStalkGerm by its explicit definition. This also applies
to a = 0 and a = 1; an empty U has no x satisfying hxU. -/
theorem affineRegularStalkGerm_scalar
    (X : Scheme.{u}) (x : X) (U : X.Opens) (hxU : x ∈ U) (hU : IsAffineOpen U)
    (a : Γ(X, U)) :
    (affineFreeStalkFunctor X x U hU).map (affineScalarEnd X U a)
        (affineRegularStalkGerm X x U hxU hU) =
      X.presheaf.germ U x hxU a • affineRegularStalkGerm X x U hxU hU := by
  let P := SheafOfModules.pushforward.{u}
    (SheafOfModules.pushforwardOver (R := moduleRings X.toRingedSpace) U)
  let M := (affinePerfectSheafification X U hU).obj (ModuleCat.of Γ(X, U) Γ(X, U))
  let b := (P.map (affineRegularSheafIso X U hU).inv).val.app (.op U)
    (1 : ((moduleRings X.toRingedSpace).over U).obj.obj
      (.op ((CategoryTheory.Over.star U).obj U)))
  change RingedSpace.stalkAddMap X.toRingedSpace x
    (P.map ((affinePerfectSheafification X U hU).map (affineScalarEnd X U a)))
    (TopCat.Presheaf.germ (P.obj M).val.presheaf U x hxU b) = _
  dsimp only [RingedSpace.stalkAddMap]
  erw [TopCat.Presheaf.stalkFunctor_map_germ_apply]
  change TopCat.Presheaf.germ (P.obj M).val.presheaf U x hxU
    ((P.map ((affinePerfectSheafification X U hU).map
      (affineScalarEnd X U a))).val.app (.op U) b) =
    X.presheaf.germ U x hxU a •
      TopCat.Presheaf.germ (P.obj M).val.presheaf U x hxU b
  erw [← PresheafOfModules.germ_smul (R := X.presheaf) (P.obj M).val]
  apply congrArg (TopCat.Presheaf.germ (P.obj M).val.presheaf U x hxU)
  exact affineScalarEnd_section_action X U hU a b

end AlgebraicGeometry.Scheme
