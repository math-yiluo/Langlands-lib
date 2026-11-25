/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DirectImageAlgebraDerivedCategory
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.RingTheory.RingHom.Flat
import WeilConjectures.AlgebraicGeometry.AffinePushforwardStalkLocalization
public import Mathlib.RingTheory.Flat.Localization

/-! # Stalkwise flatness over the direct-image algebra
Source: Stacks Project, Tag 0AVW.
(blueprint: lem-sc-affine-algebra-stalk-flat)
-/

@[expose] public section

universe u
open CategoryTheory
namespace AlgebraicGeometry

/-- The canonical morphism to the direct-image algebra is stalkwise flat.
Source: Stacks Project, Tag 0AVW, affine stalk calculation in the proof.
(blueprint: lem-sc-affine-algebra-stalk-flat)

Proof: choose an affine neighborhood Spec B of f(x). Its inverse image is Spec A
because f is affine. Write p for x and q for its image. Distinguished neighborhoods
D(b), b outside q, are cofinal among neighborhoods of q. Their inverse images have
sections A localized at the image of b. Taking the colimit identifies the source
stalk with S⁻¹A, where S is the image of B minus q. The target stalk is A_p, and
naturality of germs identifies the canonical stalk map with the localization map
S⁻¹A → A_p. Since S avoids p, this is a further localization and therefore flat.
The calculation is local around every x; for empty X the assertion is vacuous. -/
theorem affine_algebra_stalkMap_flat
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsAffineHom f] (x : X) :
    ((toDirectImageAlgebraSpace f).hom.stalkMap x).hom.Flat := by
  obtain ⟨U, hU, hx, _⟩ :=
    exists_isAffineOpen_mem_and_subset (X := Y) (x := f x) (U := ⊤) (by trivial)
  let F := (TopCat.Presheaf.pushforward CommRingCat f.base).obj X.presheaf
  let A := X.presheaf.obj (Opposite.op (f ⁻¹ᵁ U))
  let S := F.stalk (f x)
  let T := X.presheaf.stalk x
  let : Algebra A S := TopCat.Presheaf.algebra_section_stalk F ⟨f x, hx⟩
  let : Algebra A T := TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨x, hx⟩
  let g := ((toDirectImageAlgebraSpace f).hom.stalkMap x).hom
  let : Algebra S T := g.toAlgebra
  have : IsLocalization
      ((hU.primeIdealOf ⟨f x, hx⟩).asIdeal.primeCompl.map (f.app U).hom) S :=
    affine_pushforward_stalk_isLocalization f hU ⟨f x, hx⟩
  have : IsScalarTower A S T := IsScalarTower.of_algebraMap_eq fun a ↦ by
    change (X.presheaf.germ (f ⁻¹ᵁ U) x hx).hom a =
      g ((F.germ U (f x) hx).hom a)
    have h := PresheafedSpace.stalkMap_germ (toDirectImageAlgebraSpace f).hom U x hx
    exact (congrArg (fun k ↦ k.hom a) h).symm
  have := (hU.preimage f).isLocalization_stalk ⟨x, hx⟩
  have hflat : Module.Flat A T :=
    IsLocalization.flat T ((hU.preimage f).primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl
  exact (Module.flat_iff_of_isLocalization S
    ((hU.primeIdealOf ⟨f x, hx⟩).asIdeal.primeCompl.map (f.app U).hom) T).mpr hflat

end AlgebraicGeometry
