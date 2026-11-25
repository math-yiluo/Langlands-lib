/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.Localization
public import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.Algebra.Module.LocalizedModule.IsLocalization

/-! # The stalk represented by a supported polynomial prime
Source: Stacks Project, Tag 069C, proof of (3) implies (1), affine localization.
(blueprint: lem-pc-affine-polynomial-supported-localization-stalk).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- A supported prime of a surjective affine presentation gives a source stalk, compatibly
with the affine base action. This statement has no Tor or perfectness hypothesis.
Source: Stacks Project, Tag 069C, proof of (3) implies (1).
Proof: The image q of p under g is prime because g is surjective and its kernel lies in p;
its inverse image is p. The affine equivalence V ≅ Spec Γ(X,V) gives x corresponding to q.
The germ Γ(X,V) → O(X,x) is localization at q. Surjectivity and g⁻¹(q) = p imply that the
image of the complement of p is exactly the complement of q. Thus the germ, regarded as
a map of polynomial-ring modules, exhibits the stalk as localization of Γ(X,V) at p.
The universal property of module localization gives a polynomial-ring linear equivalence
from the displayed localized module to the stalk. Restrict it to Γ(Y,U). The equation
on g and naturality of germs identify this scalar action with the composite of the base
germ and the actual stalk map of f. This constructs the required module isomorphism.
For n = 0 the same argument applies. A zero quotient has no prime containing the kernel,
so that case is vacuous; no Noetherian or finite type hypothesis is needed.
(blueprint: lem-pc-affine-polynomial-supported-localization-stalk). -/
theorem affinePolynomial_supportedLocalization_stalk
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (U : Y.Opens) (V : X.Opens) (hV : IsAffineOpen V) (e : V ≤ f ⁻¹ᵁ U)
    (n : ℕ) (g : MvPolynomial (Fin n) Γ(Y, U) →+* Γ(X, V))
    (hg : Function.Surjective g)
    (hcomp : g.comp MvPolynomial.C = (f.appLE U V e).hom)
    (p : PrimeSpectrum (MvPolynomial (Fin n) Γ(Y, U)))
    (hker : RingHom.ker g ≤ p.asIdeal) :
    ∃ (x : X) (hx : x ∈ V), Nonempty
      (((ModuleCat.restrictScalars
          ((algebraMap (MvPolynomial (Fin n) Γ(Y, U))
            (Localization p.asIdeal.primeCompl)).comp MvPolynomial.C)).obj
          (((ModuleCat.restrictScalars g).obj
            (ModuleCat.of Γ(X, V) Γ(X, V))).localizedModule p.asIdeal.primeCompl)) ≅
        (ModuleCat.restrictScalars ((f.stalkMap x).hom.comp
          (Y.presheaf.germ U (f x) (e hx)).hom)).obj
            (ModuleCat.of (X.presheaf.stalk x) (X.presheaf.stalk x))) := by
  let q : PrimeSpectrum Γ(X, V) :=
    ⟨p.asIdeal.map g, Ideal.map_isPrime_of_surjective hg hker⟩
  have : q.asIdeal.IsPrime := q.isPrime
  let xV : V := hV.isoSpec.inv q
  let x : X := xV.1
  have hx : x ∈ V := xV.2
  have hq : hV.primeIdealOf ⟨x, hx⟩ = q := by
    change hV.isoSpec.hom (hV.isoSpec.inv q) = q
    rw [← Scheme.Hom.comp_apply, Iso.inv_hom_id]
    rfl
  have hp : q.asIdeal.comap g = p.asIdeal := by
    change (p.asIdeal.map g).comap g = p.asIdeal
    rw [Ideal.comap_map_of_surjective g hg, ← RingHom.ker_eq_comap_bot,
      sup_eq_left.mpr hker]
  have hS : p.asIdeal.primeCompl.map g = q.asIdeal.primeCompl := by
    simpa only [hp] using Ideal.map_primeCompl_comap_of_surjective g hg q.asIdeal
  let R := MvPolynomial (Fin n) Γ(Y, U)
  let B := Γ(X, V)
  let H := X.presheaf.stalk x
  let : Algebra R B := g.toAlgebra
  let : Algebra B H := X.presheaf.algebra_section_stalk ⟨x, hx⟩
  let : Algebra R H := ((X.presheaf.germ V x hx).hom.comp g).toAlgebra
  let : IsScalarTower R B H := IsScalarTower.of_algebraMap_eq' rfl
  have : IsLocalization q.asIdeal.primeCompl H := by
    simpa only [hq] using hV.isLocalization_stalk ⟨x, hx⟩
  have : IsLocalization (Algebra.algebraMapSubmonoid B p.asIdeal.primeCompl) H := by
    change IsLocalization (p.asIdeal.primeCompl.map g) H
    rw [hS]
    infer_instance
  let M := (ModuleCat.restrictScalars g).obj (ModuleCat.of B B)
  let K := (ModuleCat.restrictScalars ((X.presheaf.germ V x hx).hom.comp g)).obj
    (ModuleCat.of H H)
  let b : M →ₗ[R] K := (IsScalarTower.toAlgHom R B H).toLinearMap
  have : IsLocalizedModule p.asIdeal.primeCompl b := by
    dsimp only [b]
    exact (isLocalizedModule_iff_isLocalization (R := R) (A := B) (Aₛ := H)).mpr
      (inferInstance : IsLocalization
        (Algebra.algebraMapSubmonoid B p.asIdeal.primeCompl) H)
  let k := M.localizedModuleMkLinearMap p.asIdeal.primeCompl
  let E : M.localizedModule p.asIdeal.primeCompl ≃ₗ[R] K :=
    IsLocalizedModule.linearEquiv p.asIdeal.primeCompl k b
  let α : ((ModuleCat.restrictScalars
      ((algebraMap R (Localization p.asIdeal.primeCompl)).comp MvPolynomial.C)).obj
        (M.localizedModule p.asIdeal.primeCompl)) ≅
      (ModuleCat.restrictScalars
        ((X.presheaf.germ V x hx).hom.comp (g.comp MvPolynomial.C))).obj
          (ModuleCat.of H H) :=
    (show ((ModuleCat.restrictScalars
        ((algebraMap R (Localization p.asIdeal.primeCompl)).comp MvPolynomial.C)).obj
          (M.localizedModule p.asIdeal.primeCompl)) ≃ₗ[Γ(Y, U)]
        ((ModuleCat.restrictScalars
          ((X.presheaf.germ V x hx).hom.comp (g.comp MvPolynomial.C))).obj
            (ModuleCat.of H H)) from
      { __ := E.toAddEquiv
        map_smul' := fun a m ↦ by
          change E ((algebraMap R (Localization p.asIdeal.primeCompl)
            (MvPolynomial.C a)) • (show M.localizedModule p.asIdeal.primeCompl from m)) =
              (MvPolynomial.C a : R) • E m
          rw [IsScalarTower.algebraMap_smul (A := Localization p.asIdeal.primeCompl)
            (M := M.localizedModule p.asIdeal.primeCompl)]
          exact E.map_smul (MvPolynomial.C a) m }).toModuleIso
  have hcomm : (X.presheaf.germ V x hx).hom.comp (f.appLE U V e).hom =
      (f.stalkMap x).hom.comp (Y.presheaf.germ U (f x) (e hx)).hom := by
    ext r
    change X.presheaf.germ V x hx ((f.appLE U V e).hom r) =
      f.stalkMap x (Y.presheaf.germ U (f x) (e hx) r)
    simp only [Scheme.Hom.germ_stalkMap_apply, Scheme.Hom.appLE,
      homOfLE_leOfHom, CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply,
      X.presheaf.germ_res_apply]
  refine ⟨x, hx, ?_⟩
  rw [hcomp, hcomm] at α
  exact ⟨α⟩

end AlgebraicGeometry
