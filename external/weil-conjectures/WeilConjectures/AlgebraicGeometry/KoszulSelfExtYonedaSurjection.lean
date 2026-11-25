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

public import WeilConjectures.AlgebraicGeometry.Modules.FlatPullbackStalk

import WeilConjectures.AlgebraicGeometry.KoszulSelfExtDualExteriorConormal
import WeilConjectures.AlgebraicGeometry.DeterminantDualPairing
import WeilConjectures.AlgebraicGeometry.DeterminantDualPairingLocal
import WeilConjectures.AlgebraicGeometry.AffineConormalFrame
import WeilConjectures.AlgebraicGeometry.Modules.ExteriorSheafRestrictIso
import WeilConjectures.RingTheory.KoszulConormalBasis

/-! # Surjectivity of the exterior Yoneda comparison

Source: Stacks Project, Tags 0BQW and 0BQY. -/

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

private theorem stalk_surjective_iso_comp
    {X : Scheme.{u}} {M M' N N' : X.Modules}
    (a : M ≅ M') (q : M ⟶ N) (b : N ≅ N') (x : X)
    (hq : Function.Surjective (q.stalkLinearMap x)) :
    Function.Surjective ((a.inv ≫ q ≫ b.hom).stalkLinearMap x) := by
  let F := Scheme.Modules.toPresheaf X ⋙ TopCat.Presheaf.stalkFunctor Ab.{u} x
  change Function.Surjective (F.map q) at hq
  have has := (ConcreteCategory.bijective_of_isIso (F.map a.inv)).2
  have hbs := (ConcreteCategory.bijective_of_isIso (F.map b.hom)).2
  change Function.Surjective (F.map (a.inv ≫ q ≫ b.hom))
  simpa only [Functor.map_comp, ConcreteCategory.coe_comp, Function.comp_assoc] using
    hbs.comp (hq.comp has)

private theorem exterior_dual_stalk_surjection
    (X : Scheme.{u}) (C : X.Modules) (V : X.Opens) (n : ℕ)
    (hfree : ∀ x : X, x ∈ V → ∃ U : X.Opens, x ∈ U ∧ ∃ m : ℕ,
      Nonempty (C.over U ≅ SheafOfModules.free (ULift.{u} (Fin m)))) :
    ∃ φ : Scheme.Modules.exteriorPower
        ((Scheme.Modules.restrictFunctor V.ι).obj (Scheme.Modules.dual C)) n ⟶
      (Scheme.Modules.restrictFunctor V.ι).obj
        (Scheme.Modules.dual (Scheme.Modules.exteriorPower C n)),
      ∀ z : V.toScheme, Function.Surjective (φ.stalkLinearMap z) := by
  classical
  obtain ⟨p, hp⟩ := exterior_dual_pairing_exists X C n
  obtain ⟨a⟩ := Scheme.Modules.exteriorSheaf_restrict_iso (Scheme.Modules.dual C) n V
  let q := (Scheme.Modules.restrictFunctor V.ι).map p
  refine ⟨a.inv ≫ q, ?_⟩
  intro z
  obtain ⟨U, hzU, m, ⟨e⟩⟩ := hfree z.1 z.2
  have hps : Function.Surjective (p.stalkLinearMap z.1) :=
    stalk_surjective_of_local_app p z.1 U hzU fun W hW ↦
      (exterior_dual_pairing_app_bijective X C n p hp U m e W (homOfLE hW)).2
  have hqs : Function.Surjective (q.stalkLinearMap z) :=
    restrict_stalk_surjective p V z hps
  simpa only [Iso.refl_hom, Category.comp_id] using
    stalk_surjective_iso_comp a q (Iso.refl _) z hqs

set_option backward.isDefEq.respectTransparency false in
/-- The alternating Yoneda products give a surjection from the exterior sheaf to
self Ext on the Koszul-regular open. This asserts generation, not injectivity.

Source: Stacks Project, Tags 0BQW and 0BQY, the degree-one boundary and the
contraction-product spanning argument.
(blueprint: lem-sc-koszul-self-ext-yoneda-surjection).

Proof: The second-order thickening sequence gives the intrinsic degree-one map
from the conormal dual to self Ext by pushing out extensions. Compose n such
classes using derived internal Hom composition. On a regular affine chart,
represent these classes by the degree-one derivations of the augmented Koszul
DG algebra. Each derivation squares to zero and distinct derivations anticommute.
Thus the product vanishes when two arguments agree, even in characteristic two;
it is alternating, rather than merely skew symmetric. The exterior universal
property and module sheafification give a map on the regular locus. All maps
come from the intrinsic boundary and composition, so they commute with restriction
and agree on overlaps without a quasi-separatedness hypothesis. The resulting
map is linear for the quotient action. Tensor pullback of cohomology preserves
this action and restriction yields the displayed morphism on V.
On a chart of length m, Hom of the Koszul resolution into the quotient has zero
differentials. Products of n distinct contraction classes span its degree-n term,
so the morphism is surjective on each stalk. Use a common K-injective Hom model
to compare the given derived universe. For n=0 the empty product is the unit;
for n>m the target stalk is zero. Empty V has no stalk obligations. -/
theorem koszulRegularImmersion_self_ext_yoneda_surjection
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
    let E := Scheme.Modules.exteriorPower
      ((Scheme.Modules.restrictFunctor V.ι).obj
        (SheafOfModules.homObj (R := Z.sheaf)
          ((Scheme.Modules.tensorPullback i).obj i.ker.toModules)
          (SheafOfModules.unit Z.ringCatSheaf))) n
    ∃ φ : E ⟶ T, ∀ z : V.toScheme, Function.Surjective (φ.stalkLinearMap z) := by
  classical
  dsimp only
  let C := (Scheme.Modules.tensorPullback i).obj i.ker.toModules
  have hfree : ∀ z : Z, z ∈ V → ∃ U : Z.Opens, z ∈ U ∧ ∃ m : ℕ,
      Nonempty (C.over U ≅ SheafOfModules.free (ULift.{u} (Fin m))) := by
    intro z hz
    obtain ⟨U, hzU, m, f, hf, hreg⟩ := hregular z hz
    obtain ⟨c, hc⟩ := ExteriorAlgebra.exists_koszul_conormal_basis
      Γ(Y, U.1) (i.ker.ideal U) m f hreg hf
    obtain ⟨e, he⟩ := affine_conormal_frame i U m c
    exact ⟨i ⁻¹ᵁ U.1, hzU, m, e⟩
  obtain ⟨q, hq⟩ := exterior_dual_stalk_surjection Z C V n hfree
  obtain ⟨b⟩ := koszulRegularImmersion_self_ext_dual_exterior_conormal i V n hregular
  refine ⟨q ≫ b.hom, ?_⟩
  intro z
  simpa only [Iso.refl_inv, Category.id_comp] using
    stalk_surjective_iso_comp (Iso.refl _) q b z (hq z)

end AlgebraicGeometry
