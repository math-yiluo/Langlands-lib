/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import WeilConjectures.AlgebraicGeometry.AffinePerfectModuleModel
public import Mathlib.RingTheory.Spectrum.Prime.Module
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.Algebra.Category.Grp.Zero
/-! # Elementwise torsion for an affine model of a supported target

Source: Stacks Project, Tag 08EJ, affine support paragraph, and Tag 06Z0.
(blueprint: new-affine-restricted-homology-support).
-/
@[expose] public section
universe u w
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme
attribute [local instance] Functor.additive_of_preserves_binary_products
  comp_preservesFiniteLimits comp_preservesFiniteColimits
set_option autoImplicit false
/-- An ordinary affine module identified with restricted shifted cohomology has
support disjoint from the scalar's basic open.
Source: Stacks Project, Tag 08EJ, affine support paragraph, and Tag 06Z0.
(blueprint: new-affine-restricted-homology-support).

Proof: Exactness of over-site restriction and the canonical over equivalence
identify its homology with open-subscheme restriction of the homology of E'[k].
The homology shift isomorphism identifies the latter's stalk at x with the stalk
of H^(i+k)(E') at x. Undo the over equivalence and affine chart in hN to identify
the tilde of N with this restricted cohomology. The global section compatibility
identifies D(f|U) with the points of U outside the global V(f). Hence tilde N has
zero stalks on D(f|U). Tilde stalks are prime localizations of N; zero stalks are
nonmembership in Module.support by Module.notMem_support_iff. This is the claimed
disjointness. For f=0 the basic open is empty; for units all stalks vanish. Empty
opens, zero rings and zero modules are included. No finite generation is used. -/
theorem affine_restricted_homology_support
    (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [∀ U : X.Opens, HasDerivedCategory.{w}
      (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))]
    (f : RingCat.sectionsSubring (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat.{u}))
    (E' : schemeDerivedQCohCategory X)
    (hSupport : ∀ (i : ℤ) (x : X), x ∉ X.zeroLocus (U := ⊤) {f.val (op ⊤)} →
      Subsingleton (↑(TopCat.Presheaf.stalk ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) i).obj E'.obj).val.presheaf x)))
    (U : X.Opens) (hU : IsAffineOpen U) (k : ℤ)
    (i : ℤ) (N : ModuleCat.{u} (X.sheaf.obj.obj (op U)))
    (hN : Nonempty ((affinePerfectSheafification X U hU).obj N ≅
      (DerivedCategory.homologyFunctor
        (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U)) i).obj
        ((SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U).mapDerivedCategory.obj
          (E'.obj⟦k⟧)))) :
    Disjoint (↑(PrimeSpectrum.basicOpen (R := (X.sheaf.obj.obj (op U) : Type u))
      (f.val (op U)))) (Module.support (X.sheaf.obj.obj (op U)) N) := by
  let C := SheafOfModules.{u} (moduleRings X.toRingedSpace)
  let D := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U)
  let r := SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U
  let e := Modules.overEquiv U
  let H := DerivedCategory.homologyFunctor C i
  let HU := DerivedCategory.homologyFunctor D i
  obtain ⟨α⟩ := hN
  let δ : (Modules.restrictFunctor hU.isoSpec.hom).obj
      ((tilde.functor (X.presheaf.obj (op U))).obj N) ≅
      (Modules.restrictFunctor U.ι).obj (H.obj (E'.obj⟦k⟧)) :=
    (e.counitIso.app _).symm ≪≫ e.functor.mapIso α ≪≫
      e.functor.mapIso ((r.mapDerivedCategoryHomologyFunctorIso i).app (E'.obj⟦k⟧)).symm ≪≫
      (Modules.overFunctorEquiv U).app _
  let σ : H.obj (E'.obj⟦k⟧) ≅
      (DerivedCategory.homologyFunctor C (k + i)).obj E'.obj :=
    ((DerivedCategory.homologyFunctor C 0).shiftIso k i (k + i) rfl).app E'.obj
  rw [Set.disjoint_left]
  intro p hp hs
  let y : U.toScheme := hU.isoSpec.inv p
  have hy : hU.isoSpec.hom y = p := by
    dsimp [y]
    rw [← Scheme.Hom.comp_apply, hU.isoSpec.inv_hom_id]
    rfl
  have hx : y.val ∉ X.zeroLocus (U := ⊤) {f.val (op ⊤)} := by
    have hf : X.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op
        (f.val (op ⊤)) = f.val (op U) := f.property _
    have hb : X.basicOpen (f.val (op U)) = X.basicOpen (f.val (op ⊤)) ⊓ U := by
      rw [← hf, Scheme.basicOpen_res, inf_comm]
    have hp' : hU.fromSpec p ∈ X.basicOpen (f.val (op U)) := by
      change p ∈ hU.fromSpec ⁻¹ᵁ X.basicOpen (f.val (op U))
      rw [hU.fromSpec_preimage_basicOpen]
      exact hp
    have hyval : hU.fromSpec p = y.val := rfl
    rw [hyval, hb] at hp'
    rw [X.zeroLocus_singleton]
    exact fun h ↦ h hp'.1
  let st := SheafOfModules.toSheaf.{u} (moduleRings U.toScheme.toRingedSpace) ⋙
    TopCat.Sheaf.forget AddCommGrpCat.{u} U.toScheme.toTopCat ⋙
    TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} y
  let dS := (Modules.restrictStalkNatIso hU.isoSpec.hom y).app
      ((tilde.functor (X.presheaf.obj (op U))).obj N)
  let dT := st.mapIso δ ≪≫
    (Modules.restrictStalkNatIso U.ι y).app (H.obj (E'.obj⟦k⟧))
  let sX := SheafOfModules.toSheaf.{u} (moduleRings X.toRingedSpace) ⋙
    TopCat.Sheaf.forget AddCommGrpCat.{u} X.toTopCat ⋙
    TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} y.val
  have hzero : IsZero (TopCat.Presheaf.stalk
      ((DerivedCategory.homologyFunctor C (k+i)).obj E'.obj).val.presheaf y.val) :=
    AddCommGrpCat.isZero_iff_subsingleton.mpr (hSupport (k+i) y.val hx)
  have hz : IsZero (TopCat.Presheaf.stalk
      ((tilde.functor (X.presheaf.obj (op U))).obj N).val.presheaf
        (hU.isoSpec.hom y)) := hzero.of_iso (dS.symm ≪≫ dT ≪≫ sX.mapIso σ)
  rw [hy] at hz
  have hst : Subsingleton (↑(TopCat.Presheaf.stalk
      ((tilde.functor (X.presheaf.obj (op U))).obj N).val.presheaf p)) :=
    AddCommGrpCat.subsingleton_of_isZero hz
  have : Subsingleton ((tilde N).presheaf.stalk p) := hst
  have hloc : Subsingleton (LocalizedModule p.asIdeal.primeCompl N) := by
    apply LocalizedModule.subsingleton_iff.mpr
    intro m
    have hz' : (tilde.toStalk N p).hom m = 0 := Subsingleton.elim _ _
    obtain ⟨s, hs⟩ := (IsLocalizedModule.eq_zero_iff p.asIdeal.primeCompl
      (tilde.toStalk N p).hom).mp hz'
    exact ⟨s, s.property, hs⟩
  exact (Module.notMem_support_iff.mpr hloc) hs
end AlgebraicGeometry.Scheme
