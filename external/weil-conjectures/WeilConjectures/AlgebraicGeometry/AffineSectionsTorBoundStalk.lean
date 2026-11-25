/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PerfectMorphism
public import Mathlib.AlgebraicGeometry.AffineScheme
import WeilConjectures.RingTheory.TorVanishingLocalizedAlgebra
import WeilConjectures.RingTheory.TorVanishingLocalizedBase

/-! # Localization of an affine coordinate Tor bound

Source: Stacks Project, Tags 0B67 and 069C.
(blueprint: lem-pc-affine-sections-tor-bound-stalk).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- A fixed affine coordinate Tor bound holds at every source stalk in that affine open.
Source: Stacks Project, Tag 0B67, `lemma-tor-amplitude-localization`,
implication (1) to (2), applied to B[0];
Tag 069C, proof of (1) implies (2).

Proof: write A = Γ(Y,U), B = Γ(X,V), and φ = f.appLE U V e. For y in V,
let q be the prime of B corresponding to y and p its inverse image in A.
The affine stalk isomorphisms identify the given stalk homomorphism with
A_p to B_q; compatibility follows by composing the section-to-germ maps with φ.
For any A_p-module M, restrict scalars to A. A projective A-resolution of B
computes the Tor' groups in the hypothesis. Localizing this resolution at p
is exact and gives a projective A_p-resolution of B tensor_A A_p. Its tensor
with M agrees with the original resolution tensor_A M. Consequently these
Tor groups vanish above d. To localize in the B variable at q, compute the same Tor
groups instead with an A_p-projective resolution of M, using balancedness of Tor. Tensoring it with
B tensor_A A_p gives a complex of B-modules. Localizing that complex at q is exact,
commutes with homology, and replaces B tensor_A A_p by B_q. It therefore gives
Tor_j over A_p of B_q and M equal to the localization of the already zero group.
Transport across the affine stalk isomorphisms to obtain precisely the stated
Tor' object with f.stalkMap y.
No finite type or Noetherian hypothesis is needed. For V empty there is no y;
for d = 0 this is the preservation of flatness under these localizations.
(blueprint: lem-pc-affine-sections-tor-bound-stalk). -/
theorem affineSections_torBound_stalk
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (U : Y.Opens) (hU : IsAffineOpen U)
    (V : X.Opens) (hV : IsAffineOpen V) (e : V ≤ f ⁻¹ᵁ U)
    (d : ℕ)
    (hbound : ∀ M : ModuleCat.{u} Γ(Y, U), ∀ j : ℕ, d < j →
      IsZero (((Tor' (ModuleCat.{u} Γ(Y, U)) j).obj
        ((ModuleCat.restrictScalars (f.appLE U V e).hom).obj
          (ModuleCat.of Γ(X, V) Γ(X, V)))).obj M)) :
    ∀ y : X, y ∈ V → ∀ M : ModuleCat.{u} (Y.presheaf.stalk (f y)),
      ∀ j : ℕ, d < j →
        IsZero (((Tor' (ModuleCat.{u} (Y.presheaf.stalk (f y))) j).obj
          ((ModuleCat.restrictScalars (f.stalkMap y).hom).obj
            (ModuleCat.of (X.presheaf.stalk y) (X.presheaf.stalk y)))).obj M) := by
  intro y hy M j hj
  let := Y.presheaf.algebra_section_stalk ⟨f y, e hy⟩
  have := hU.isLocalization_stalk ⟨f y, e hy⟩
  let := X.presheaf.algebra_section_stalk ⟨y, hy⟩
  have := hV.isLocalization_stalk ⟨y, hy⟩
  let a := algebraMap Γ(Y, U) (Y.presheaf.stalk (f y))
  let b := algebraMap Γ(X, V) (X.presheaf.stalk y)
  have hcomp : b.comp (f.appLE U V e).hom = (f.stalkMap y).hom.comp a := by
    ext r
    change X.presheaf.germ V y hy ((f.appLE U V e).hom r) =
      f.stalkMap y (Y.presheaf.germ U (f y) (e hy) r)
    simp only [Scheme.Hom.germ_stalkMap_apply, Scheme.Hom.appLE,
      homOfLE_leOfHom, CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply,
      X.presheaf.germ_res_apply]
  have hlocalized := ModuleCat.isZero_tor_localized_algebra
    Γ(Y, U) Γ(X, V) (X.presheaf.stalk y) (f.appLE U V e).hom
    (hV.primeIdealOf ⟨y, hy⟩).asIdeal.primeCompl
    ((ModuleCat.restrictScalars a).obj M) j
    (hbound ((ModuleCat.restrictScalars a).obj M) j hj)
  change IsZero (((Tor' (ModuleCat.{u} Γ(Y, U)) j).obj
    ((ModuleCat.restrictScalars (b.comp (f.appLE U V e).hom)).obj
      (ModuleCat.of (X.presheaf.stalk y) (X.presheaf.stalk y)))).obj
        ((ModuleCat.restrictScalars a).obj M)) at hlocalized
  rw [hcomp] at hlocalized
  let c := ModuleCat.restrictScalarsComp'App a (f.stalkMap y).hom
    ((f.stalkMap y).hom.comp a) rfl
    (ModuleCat.of (X.presheaf.stalk y) (X.presheaf.stalk y))
  have hrestricted := hlocalized.of_iso
    (((Tor' (ModuleCat.{u} Γ(Y, U)) j).mapIso c).app ((ModuleCat.restrictScalars a).obj M))
  exact ModuleCat.isZero_tor_of_restrictScalars_localization
    Γ(Y, U) (Y.presheaf.stalk (f y))
    (hU.primeIdealOf ⟨f y, e hy⟩).asIdeal.primeCompl
    ((ModuleCat.restrictScalars (f.stalkMap y).hom).obj
      (ModuleCat.of (X.presheaf.stalk y) (X.presheaf.stalk y))) M j hrestricted

end AlgebraicGeometry
