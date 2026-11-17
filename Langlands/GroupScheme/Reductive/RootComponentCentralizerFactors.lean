import Langlands.GroupScheme.Reductive.AffinePinnedModel
import Langlands.GroupScheme.Reductive.SimplyConnectedPinnedModel
import Langlands.GroupScheme.Reductive.SimplyConnectedCorootSubtori

/-! # Character-coordinate input for component centralizers -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme

open Langlands.LinearAlgebra.SimplyConnectedCartanComponents

/-- An integral full character-coordinate decomposition supported on the
Cartan components of a supplied pinned affine model. This input does not
assume algebraic simple connectedness or adjointness. -/
structure RootComponentCoordinates (M : AffinePinnedModel.{u}) where
  characters : (M.coordinates → ℤ) ≃ₗ[ℤ] (M.basis.support → ℤ)
  rootComponent : M.rootIndex → Component M.basis
  root_support : ∀ (r : M.rootIndex) (i : M.basis.support),
    component M.basis i ≠ rootComponent r → characters (M.rootDatum.root r) i = 0
  simple_component : ∀ i : M.basis.support, rootComponent i = component M.basis i

namespace RootComponentCoordinates

variable {M : AffinePinnedModel.{u}} (D : RootComponentCoordinates M)

/-- The simple indices outside a specified Cartan component. -/
abbrev Complement (_D : RootComponentCoordinates M) (c : Component M.basis) :=
  {i : M.basis.support // component M.basis i ≠ c}

/-- The restriction of full character coordinates to the component complement. -/
def restriction (c : Component M.basis) :
    (M.coordinates → ℤ) →ₗ[ℤ] (D.Complement c → ℤ) where
  toFun x i := D.characters x i
  map_add' x y := by ext i; simp only [map_add, Pi.add_apply]
  map_smul' n x := by ext i; simp only [map_smul, Pi.smul_apply, RingHom.id_apply]

/-- Restriction to complementary character coordinates detects exactly the
selected root component, for every root of the supplied full root datum. -/
theorem restriction_root_eq_zero_iff (c : Component M.basis) (r : M.rootIndex) :
    D.restriction c (M.rootDatum.root r) = 0 ↔ D.rootComponent r = c := by
  classical
  constructor
  · intro hr
    by_contra hrc
    have hz : D.characters (M.rootDatum.root r) = 0 := by
      ext i
      by_cases hi : component M.basis i = c
      · exact D.root_support r i (by rw [hi]; exact Ne.symm hrc)
      · exact congrFun hr ⟨i, hi⟩
    exact M.rootDatum.ne_zero r (D.characters.injective (hz.trans (map_zero _).symm))
  · intro hrc
    ext i
    exact D.root_support r i (by rw [hrc]; exact i.property)

/-- The coordinate system has an actual integral extension by zero from
every complementary coordinate set. -/
def extension (c : Component M.basis) :
    (D.Complement c → ℤ) →ₗ[ℤ] (M.coordinates → ℤ) := by
  classical
  exact
    { toFun := fun x => D.characters.symm
        (fun i => if hi : component M.basis i ≠ c then x ⟨i, hi⟩ else 0)
      map_add' := by
        intro x y
        rw [← map_add]
        congr 1
        ext i
        by_cases hi : component M.basis i = c <;> simp [hi]
      map_smul' := by
        intro n x
        rw [← map_smul]
        congr 1
        ext i
        by_cases hi : component M.basis i = c <;> simp [hi] }

/-- Integral restriction followed by the specified extension is the identity. -/
theorem restriction_comp_extension (c : Component M.basis) :
    (D.restriction c).comp (D.extension c) = LinearMap.id := by
  classical
  ext x i
  change D.characters (D.characters.symm _) i = _
  rw [LinearEquiv.apply_symm_apply]
  simp [i.property]

end RootComponentCoordinates

namespace AffineSimplyConnectedPinnedModel

variable (M : AffineSimplyConnectedPinnedModel.{u})

local instance : CommRing M.ring := M.toAffinePinnedModel.commRing
local instance : Fintype M.coordinates := M.toAffinePinnedModel.fintypeCoordinates
local instance : Fintype M.rootIndex := M.toAffinePinnedModel.fintypeRoots
local instance : M.rootDatum.IsReduced := M.fibrewiseRootDatum.isReduced

/-- The simply connected coroot-pairing coordinates supply the generic
component-coordinate input. -/
def rootComponentCoordinates : RootComponentCoordinates M.toAffinePinnedModel where
  characters := SimplyConnectedCorootSubtori.simpleCorootCoordinates
    M.rootDatum M.basis M.corootSpan_eq_top
  rootComponent := rootComponent M.basis M.corootSpan_eq_top
  root_support r i hi := by
    rw [SimplyConnectedCorootSubtori.simpleCorootCoordinates_apply,
      M.rootDatum.root_coroot_eq_pairing]
    exact SimplyConnectedCorootSubtori.root_pairing_eq_zero_of_component_ne
      M.rootDatum M.basis M.corootSpan_eq_top r i hi
  simple_component i := rootComponent_simple M.basis M.corootSpan_eq_top i

end AffineSimplyConnectedPinnedModel

end Langlands.GroupScheme
