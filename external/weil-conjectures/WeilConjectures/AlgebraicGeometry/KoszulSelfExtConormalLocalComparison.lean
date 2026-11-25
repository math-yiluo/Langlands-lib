/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Modules.ExteriorPower
public import WeilConjectures.RingTheory.KoszulRegularSequence
public import WeilConjectures.AlgebraicGeometry.TensorPullback
public import WeilConjectures.AlgebraicGeometry.DerivedCategory
public import WeilConjectures.Algebra.Homology.DerivedInternalHom
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module

public import WeilConjectures.AlgebraicGeometry.Modules.Dual


import WeilConjectures.AlgebraicGeometry.KoszulSelfExtConormalLocalComparisonCore
import WeilConjectures.AlgebraicGeometry.KoszulSelfExtConormalLocalAlignment

/-! # Compatible local Koszul comparison maps

Source: Stacks Project, Tag 0BQY, zero-differential Hom and generator comparison. -/

@[expose] public section

set_option autoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- The Koszul Hom calculation supplies compatible local maps which are surjective
on sections over every smaller open. The chosen neighborhoods cover V.

Source: Stacks Project, Tag 0BQY, the zero-differential Hom calculation and its
compatibility under changes of regular generators; Tag 062I for the conormal basis.
(blueprint: lem-sc-koszul-self-ext-conormal-local-comparison).

Proof: On each supplied affine chart let A be its section ring, I its immersion ideal,
and B=A/I. Sheafify the normalized augmented Koszul projective resolution of B.
Open restriction of derived internal Hom and its bounded finite-free model identify
self Ext with the homology of Hom(K,B). Its differentials vanish because each
coefficient is a generator in I. The conormal basis identifies the degree-n term
with Hom_B(wedge^n(I/I²),B). Use the inverse of this coordinate identification to
map the dual exterior conormal to the computed cohomology. The quotient scalar
action is the B-action, so tensor pullback of cohomology gives the same map on Z.
At a point of an overlap the two conormal bases have equal cardinality over the
nonzero local ring. Refine around that point so that the change of coordinates
is invertible. For a substitution of regular generators, construct the Koszul
chain map by exterior powers of the degree-one substitution; the contraction
formula checks the chain equation in each degree. Modulo I this is the change of conormal
coordinates. Applying Hom into B transposes precisely that exterior map. Thus
the local comparison maps agree after a common refinement. Different comparison
maps lifting the quotient identity are homotopic, so the result is independent
of the chosen substitutions. The same formulas commute with localization.
Refine arbitrary intersections by affine opens to check equality of the local maps
on every smaller open by the separated sheaf axiom. Their coordinate images
span the zero-differential Hom term. In fact the coordinate map is an isomorphism
of finite free sheaves on each chart, so it is surjective on sections over every
smaller open, not merely on affine sections. Choose for each point a neighborhood
inside its inverse-image affine chart. The equality just proved gives the
stated compatibility for any open contained in two chosen neighborhoods.
A common K-injective resolution compares derived universes. For n=0 the map
is the quotient unit; for n above the chart length the target is zero. Empty V
has the empty family of neighborhoods and no local conditions. No inverse is needed here. -/
theorem koszulRegularImmersion_self_ext_conormal_local_comparison
    {Z Y : Scheme.{u}} (i : Z ⟶ Y)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [IsClosedImmersion i] (V : Z.Opens) (n : ℕ)
    (hregular : ∀ z : Z, z ∈ V → ∃ U : Y.affineOpens, i z ∈ U.1 ∧
      ∃ (m : ℕ) (f : Fin m → Γ(Y, U.1)),
        Ideal.span (Set.range f) = i.ker.ideal U ∧
          RingTheory.Sequence.IsKoszulRegular f) :
    let B := (Scheme.Modules.pushforward i).obj (SheafOfModules.unit Z.ringCatSheaf)
    let S := DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0
    let H := derivedInternalHom (Opens.grothendieckTopology Y) Y.toRingedSpace.sheaf
    let G := (DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (n : ℤ)).obj
        (H.obj (op (S.obj B), S.obj B))
    let T := (Scheme.Modules.restrictFunctor V.ι).obj
      ((Scheme.Modules.tensorPullback i).obj G)
    let F := (Scheme.Modules.restrictFunctor V.ι).obj
      (Scheme.Modules.dual (Scheme.Modules.exteriorPower
        ((Scheme.Modules.tensorPullback i).obj i.ker.toModules) n))
    ∃ (W : V.toScheme → V.toScheme.Opens)
      (φ : ∀ z : V.toScheme, F.over (W z) ⟶ T.over (W z)),
      (∀ z : V.toScheme, z ∈ W z) ∧
      (∀ (x y : V.toScheme) (U : V.toScheme.Opens)
        (hx : U ≤ W x) (hy : U ≤ W y),
        (φ x).val.app (op (Over.mk (homOfLE hx))) =
          (φ y).val.app (op (Over.mk (homOfLE hy)))) ∧
      (∀ (x : V.toScheme) (U : V.toScheme.Opens) (hx : U ≤ W x),
        Function.Surjective ((φ x).val.app (op (Over.mk (homOfLE hx))))) := by
  classical
  dsimp only
  have hlocal := koszulRegularImmersion_self_ext_conormal_local_iso i V n hregular
  choose W hmem he using hlocal
  let e := fun z ↦ Classical.choice (he z)
  obtain ⟨a, ha⟩ :=
    koszulRegularImmersion_self_ext_conormal_local_alignment i V n hregular W e hmem
  refine ⟨W, fun z ↦ (a z).hom ≫ (e z).hom, hmem, ha, ?_⟩
  intro x U hx t
  let E := a x ≪≫ e x
  let C := op (Over.mk (homOfLE hx))
  refine ⟨E.inv.val.app C t, ?_⟩
  have h := congrArg (fun f ↦ f.val.app C t) E.inv_hom_id
  change E.hom.val.app C (E.inv.val.app C t) = t at h
  exact h

end AlgebraicGeometry
