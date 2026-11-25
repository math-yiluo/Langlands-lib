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

import WeilConjectures.AlgebraicGeometry.KoszulSelfExtConormalComparisonSurjection
import WeilConjectures.AlgebraicGeometry.KoszulSelfExtStalkBases
import WeilConjectures.AlgebraicGeometry.DeterminantDualPairing
import WeilConjectures.AlgebraicGeometry.DeterminantDualPairingLocal
import WeilConjectures.AlgebraicGeometry.AffineConormalFrame
import WeilConjectures.RingTheory.KoszulConormalBasis
import WeilConjectures.AlgebraicGeometry.Modules.ExteriorSheafRestrictIso
import Mathlib.RingTheory.FiniteType

/-! # Self Ext as the dual of the exterior conormal

Source: Stacks Project, Tag 0BQY, the zero-differential Hom calculation. -/

@[expose] public section

set_option autoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

private theorem stalk_surjective_of_local_app
    {X : Scheme.{u}} {M N : X.Modules} (f : M ⟶ N)
    (x : X) (U : X.Opens) (hx : x ∈ U)
    (h : ∀ (W : X.Opens), W ≤ U → Function.Surjective (f.val.app (op W))) :
    Function.Surjective (f.stalkLinearMap x) := by
  intro t
  obtain ⟨W, hWU, hxW, t, rfl⟩ := N.presheaf.exists_le_germ_eq t hx
  obtain ⟨s, hs⟩ := h W hWU t
  refine ⟨M.presheaf.germ W x hxW s, ?_⟩
  rw [Scheme.Modules.Hom.stalkLinearMap_germ]
  exact congrArg (N.presheaf.germ W x hxW) hs

set_option backward.isDefEq.respectTransparency false in
private theorem restrict_stalk_surjective
    {X : Scheme.{u}} {M N : X.Modules} (f : M ⟶ N) (V : X.Opens)
    (z : V.toScheme) (h : Function.Surjective (f.stalkLinearMap z.1)) :
    Function.Surjective (((Scheme.Modules.restrictFunctor V.ι).map f).stalkLinearMap z) := by
  let e := Scheme.Modules.restrictStalkNatIso V.ι z
  intro t
  obtain ⟨s, hs⟩ := h ((e.hom.app N) t)
  obtain ⟨s', hs'⟩ := ConcreteCategory.bijective_of_isIso (e.hom.app M) |>.2 s
  refine ⟨s', ?_⟩
  apply (ConcreteCategory.bijective_of_isIso (e.hom.app N)).1
  have hn := ConcreteCategory.congr_hom (e.hom.naturality f) s'
  change (e.hom.app N)
    (((Scheme.Modules.restrictFunctor V.ι).map f).stalkLinearMap z s') =
      f.stalkLinearMap z.1 ((e.hom.app M) s') at hn
  rw [hn, hs', hs]

-- Comparing the restricted exterior sheaves and their internal duals needs extra elaboration.
set_option backward.isDefEq.respectTransparency false in
/-- The Koszul Hom calculation identifies self Ext with the internal dual of the
exterior conormal, before using any exterior power of the internal dual.

Source: Stacks Project, Tag 0BQY, the displayed identification of Ext with
Hom of the negative-degree Koszul term, and Tag 062I for the conormal basis.
(blueprint: lem-sc-koszul-self-ext-dual-exterior-conormal).

Proof: On a regular affine chart write A = O_Y(U), I = ker(i)(U), and B = A/I.
Use the augmented Koszul projective resolution and sheafify it. Restriction of
RHom and the bounded finite-free Hom comparison identify the restricted self
Ext with degree n of Hom(K,B). All differentials are zero because their
coefficients belong to I. This degree is Hom_B(wedge^n(B^m),B). The conormal
basis identifies B^m with I/I^2, so it is the internal dual of wedge^n C.
The quotient action is the B action; hence tensor pullback after cohomology
does not change this identification. For a change of regular generators
f' = A f, the chain map on Koszul resolutions is wedge^p A in degree -p.
Modulo I its degree-one map is the map on conormal classes. Hom into B
therefore transforms in degree n by the transpose of wedge^n of that
conormal map, exactly the transition map of the dual exterior conormal.
Two expressions for A differ by Koszul syzygies, which vanish modulo I;
comparison maps lifting the identity of B are homotopic and so induce the
same cohomology map. Localization gives the identical formula. Refine every
intersection by affine opens carrying such comparisons and glue the maps
and their inverses by the sheaf condition on V. No affine-intersection or
quasi-separatedness assumption is needed. Compare derived universes using
a common K-injective resolution. For n=0 this is the quotient unit; above
the local sequence length both terms vanish. Empty V is also covered. -/
theorem koszulRegularImmersion_self_ext_dual_exterior_conormal
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
    Nonempty (F ≅ T) := by
  classical
  dsimp only
  have hcomparison :=
    koszulRegularImmersion_self_ext_conormal_comparison_surjection i V n hregular
  let φ := hcomparison.choose
  have hφ := hcomparison.choose_spec
  have : IsIso φ := by
    apply Scheme.Modules.isIso_of_bijective_stalkLinearMap
    intro z
    obtain ⟨U, hzU, m, f, hf, hreg⟩ := hregular z.1 z.2
    have hbases :=
      koszulRegularImmersion_self_ext_stalk_bases i V n z U hzU m f hf hreg
    let bT := hbases.1.some
    let bE := hbases.2.some
    let C := (Scheme.Modules.tensorPullback i).obj i.ker.toModules
    have hpairing := exterior_dual_pairing_exists Z C n
    let p := hpairing.choose
    have hp := hpairing.choose_spec
    let a := (Scheme.Modules.exteriorSheaf_restrict_iso (Scheme.Modules.dual C) n V).some
    let q := a.inv ≫ (Scheme.Modules.restrictFunctor V.ι).map p
    have hbasis := ExteriorAlgebra.exists_koszul_conormal_basis
      Γ(Y, U.1) (i.ker.ideal U) m f hreg hf
    let c := hbasis.choose
    have hframe := affine_conormal_frame i U m c
    let e := hframe.1.some
    have hps : Function.Surjective (p.stalkLinearMap z.1) :=
      stalk_surjective_of_local_app p z.1 (i ⁻¹ᵁ U.1) hzU fun W hW ↦
        (exterior_dual_pairing_app_bijective Z C n p hp (i ⁻¹ᵁ U.1) m e W
          (homOfLE hW)).2
    have hqs : Function.Surjective (q.stalkLinearMap z) := by
      let L := Scheme.Modules.toPresheaf V.toScheme ⋙
        TopCat.Presheaf.stalkFunctor Ab.{u} z
      have hs := restrict_stalk_surjective p V z hps
      change Function.Surjective
        (L.map ((Scheme.Modules.restrictFunctor V.ι).map p)) at hs
      have has := (ConcreteCategory.bijective_of_isIso (L.map a.inv)).2
      change Function.Surjective (L.map q)
      simpa only [q, Functor.map_comp, ConcreteCategory.coe_comp] using hs.comp has
    let e' := bE.equiv bT (Equiv.refl _)
    let := Module.Finite.of_basis bT
    have hcomp : Function.Bijective ((φ.stalkLinearMap z).comp (q.stalkLinearMap z)) :=
      OrzechProperty.bijective_of_surjective_of_injective e'.toLinearMap
        ((φ.stalkLinearMap z).comp (q.stalkLinearMap z)) e'.injective
        ((hφ z).comp hqs)
    refine ⟨?_, hφ z⟩
    intro x y hxy
    obtain ⟨x', rfl⟩ := hqs x
    obtain ⟨y', rfl⟩ := hqs y
    exact congrArg (q.stalkLinearMap z) (hcomp.1 hxy)
  exact ⟨asIso φ⟩

end AlgebraicGeometry
