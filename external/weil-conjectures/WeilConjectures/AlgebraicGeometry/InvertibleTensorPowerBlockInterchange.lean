/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
import WeilConjectures.AlgebraicGeometry.Modules.ProjectionFormula

/-! # Interchanging blocks of powers of a line bundle

Source: Stacks Project, Tag 01CA (tensor symmetry), and Tag 09MS (tensor powers).
(blueprint: lem-sc-invertible-tensor-power-block-interchange).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite TopologicalSpace
namespace AlgebraicGeometry.Scheme.Modules
universe u
noncomputable section

private def localPowerSection {X : Scheme.{u}} {L : X.Modules} {U : X.Opens}
    (ell : Γ(L, U)) : ∀ d : ℕ, Γ(L.tensorPow d, U)
  | 0 => unitSectionsEquiv U 1
  | d + 1 => tmulSection ell (localPowerSection ell d)

private theorem localPowerSection_free {X : Scheme.{u}} {L : X.Modules}
    {U : X.Opens} {ell : Γ(L, U)} (he : IsFreeGenerator ell) (d : ℕ) :
    IsFreeGenerator (localPowerSection ell d) := by
  induction d with
  | zero => exact isFreeGenerator_one U
  | succ d ih => exact he.tmulSection ih

private theorem localPowerSection_cast {X : Scheme.{u}} {L : X.Modules}
    {U : X.Opens} (ell : Γ(L, U)) {a b : ℕ} (h : a = b) :
    (eqToHom (congrArg L.tensorPow h)).app U (localPowerSection ell a) =
      localPowerSection ell b := by
  subst b
  rfl

private theorem localPowerSection_add {X : Scheme.{u}} {L : X.Modules}
    {U : X.Opens} (ell : Γ(L, U)) (a b : ℕ) :
    (L.tensorPowAddIso a b).inv.app U
      (tmulSection (localPowerSection ell a) (localPowerSection ell b)) =
        localPowerSection ell (a + b) := by
  induction a with
  | zero =>
    rw [tensorPowAddIso, Iso.trans_inv, Iso.symm_inv, eqToIso.inv, Hom.comp_app,
      ConcreteCategory.comp_apply]
    exact (congrArg _ ((leftUnitor_hom_app_tmulSection _ _).trans (one_smul _ _))).trans
      (localPowerSection_cast ell (Nat.zero_add b).symm)
  | succ a ih =>
    rw [tensorPowAddIso, Iso.trans_inv, Iso.trans_inv, Iso.symm_inv, eqToIso.inv,
      Hom.comp_app, Hom.comp_app, ConcreteCategory.comp_apply, ConcreteCategory.comp_apply]
    change (eqToHom (congrArg L.tensorPow (Nat.succ_add a b).symm)).app U
      ((Iso.refl L ⊗ᵢ L.tensorPowAddIso a b).inv.app U
        ((α_ L (L.tensorPow a) (L.tensorPow b)).hom.app U
          (tmulSection (tmulSection ell (localPowerSection ell a))
            (localPowerSection ell b)))) = _
    rw [associator_hom_app_tmulSection, tensorIso_inv, Iso.refl_inv,
      tensorHom_app_tmulSection, ih, Hom.id_app]
    exact localPowerSection_cast ell (Nat.succ_add a b).symm

/-- Concatenating two powers of an invertible module is unaffected by interchanging
its two blocks and casting the total degree.

Source: Stacks Project, Tag 01CA (tensor symmetry), Tag 09MS, coherent-equation-ses.
(blueprint: lem-sc-invertible-tensor-power-block-interchange).
Proof: restrict to a trivializing open for L. The recursive tensorPowAddIso sends
ell^(a+b) to ell^a tensor ell^b, as follows by induction on a; its inverse
concatenates these generators. The braiding interchanges the two generators,
and the arithmetic cast identifies their total degrees. Both morphisms therefore
send ell^a tensor ell^b to the same generator of L^(a+b). Since this tensor
module is free of rank one on the open, the morphisms agree there. Equality
of sheaf morphisms is local, so they agree on X. At a=0 or b=0 the generator
is 1 and the same argument is the unitor identity; empty opens cause no exception.
This statement would fail for a general module, which is why invertibility is required. -/
theorem tensorPowAddIso_inv_block_interchange {X : Scheme.{u}}
    (L : X.Modules) [L.IsInvertible] (a b : ℕ) :
    (L.tensorPowAddIso a b).inv =
      (β_ (L.tensorPow a) (L.tensorPow b)).hom ≫
        (L.tensorPowAddIso b a).inv ≫
        eqToHom (congrArg L.tensorPow (Nat.add_comm b a))  := by
  classical
  have := IsInvertible.sheafOfModules_isInvertible L
  refine hom_ext _ _ fun U ↦ ?_
  ext z
  choose W hx hWU ell he using fun x : U ↦ exists_isFreeGenerator L x.property
  refine TopCat.Sheaf.eq_of_locally_eq'
    ⟨(L.tensorPow (a + b)).presheaf, (L.tensorPow (a + b)).isSheaf⟩
    (fun x ↦ (W x).1) U (fun x ↦ homOfLE (hWU x))
    (fun x hxU ↦ Opens.mem_iSup.mpr ⟨⟨x, hxU⟩, hx _⟩) _ _ fun x ↦ ?_
  rw [← Hom.app_presheaf_map, ← Hom.app_presheaf_map]
  obtain ⟨r, hr⟩ := ((localPowerSection_free (he x) a).tmulSection
    (localPowerSection_free (he x) b)).exists_smul_eq
      ((L.tensorPow a ⊗ L.tensorPow b).presheaf.map (homOfLE (hWU x)).op z)
  rw [← hr, Hom.app_smul, Hom.app_smul]
  congr 1
  simp only [Hom.comp_app, ConcreteCategory.comp_apply]
  rw [braiding_hom_app_tmulSection, localPowerSection_add, localPowerSection_add,
    localPowerSection_cast]
  exact Nat.add_comm b a

end
end AlgebraicGeometry.Scheme.Modules
