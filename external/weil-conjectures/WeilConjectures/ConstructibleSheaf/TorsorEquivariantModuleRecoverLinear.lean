/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.ConstructibleSheaf.TorsorAssociatedModule
import WeilConjectures.ConstructibleSheaf.TorsorEquivariantModuleRecoverLinearDiagonal
import WeilConjectures.ConstructibleSheaf.TorsorEquivariantModulePointwiseFromDiagonal

/-!
# Linear recovery for equivariant section transformations

Source: Stacks Project, Tags 0DV5 (3), 0DV6, 0A3R, 04TR and 04TS.
(blueprint: lem-weil-pbc-torsor-equivariant-module-recover-linear)
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory Limits Opposite
namespace AlgebraicGeometry.Scheme.GaloisCover

/-- A natural transformation of equivariant section presheaves acts pointwise
by a linear map when the total space of the torsor is connected.
Source: Stacks Project, etale-cohomology.tex Tags 0DV5 (3), 0DV6 and 0A3R;
sites.tex Tags 04TR and 04TS.
(blueprint: lem-weil-pbc-torsor-equivariant-module-recover-linear)

Proof: On the etale object c.P over V, identify the pulled-back torsor with the
disjoint union of its translates of the diagonal, using the torsor isomorphism.
Evaluation on the diagonal identifies equivariant sections over this object
with locally constant N-valued functions on c.P. Connectedness and nonemptiness
make these functions constant, so evaluation identifies them with N. Conjugate
the component of the natural transformation by these linear identifications;
this gives a linear map f of values. For an arbitrary etale object W, pull back
to W times_V c.P. The diagonal trivializes the torsor there. On open fibres of a
locally constant section its value is constant, and such a constant section is
the restriction of the section over c.P with that value. Naturality with respect
to the map to c.P and to open inclusions therefore says that the transformation
acts there by f. These open fibres cover, so this holds at every point and then
on W by the pulled-back etale cover. Uniqueness follows by evaluation on the
diagonal at any point of the nonempty c.P. This argument recovers linearity and
the pointwise formula only; equivariance of f is a separate consequence. -/
theorem equivariantModulePresheaf_recoverLinear
    {V : Scheme.{u}} (ℓ : ℕ) {P : Type u} [Group P] [Finite P]
    (c : Scheme.GaloisCover (ULift.{u + 1} P) V) [ConnectedSpace c.P]
    (N N' : Rep.{u + 1} (ZMod ℓ) P)
    (η : c.equivariantModulePresheaf ℓ N ⟶ c.equivariantModulePresheaf ℓ N') :
    ∃! f : N.V →ₗ[ZMod ℓ] N'.V,
      ∀ (W : V.Etale) (s : c.equivariantSections ℓ N W) (x : c.sectionSpace W),
        (η.app (op W) s).val x = f (s.val x) := by
  let := c.etale
  obtain ⟨f, hf, huniq⟩ := c.equivariantModulePresheaf_recoverLinear_diagonal ℓ N N' η
  refine ⟨f, c.equivariantModulePresheaf_pointwise_of_diagonal ℓ N N' η f hf, ?_⟩
  intro g hg
  apply huniq g
  intro s x
  exact hg (Etale.mk c.π) s
    ((pullback.lift (f := c.π) (g := c.π) (𝟙 c.P) (𝟙 c.P) rfl) x)

end AlgebraicGeometry.Scheme.GaloisCover
