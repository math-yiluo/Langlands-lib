/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.ModuleStalkFunctor
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.RingTheory.Flat.Basic
import WeilConjectures.AlgebraicGeometry.IntrinsicFlatModuleStalkTensorPresentation
import WeilConjectures.RingTheory.Flat.LocalizationPreservesFlatness
public import Mathlib.AlgebraicGeometry.AffineScheme

/-! # Relative flatness on a single affine chart

Source: Stacks Project, Morphisms Tag 01U4; Algebra Tag 00HT (6).
(blueprint: lem-pc-affine-chart-relative-flat-criterion).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory
namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
/-- Sections on one affine chart are flat over an affine base precisely when the
module stalks on that chart are flat over the corresponding base stalks.
Source: Stacks Project, Morphisms Tag 01U4; Algebra Tag 00HT (6).
(blueprint: lem-pc-affine-chart-relative-flat-criterion).

Proof: Write R = O(S) and C = O(U). Quasi-coherence identifies each stalk at x in U
with C_x tensor_C G(U), using the ordinary germ action. If G(U) is R-flat,
localization in C preserves R-flatness. The base stalk is a localization of R,
and flatness over R is equivalent to flatness over that localization for a module
on which it acts. Germ-stalkMap compatibility identifies these actions.
Conversely, choose the point of U for each maximal ideal of C. The base stalk is
R_p and is R-flat. Relative stalk flatness therefore gives R-flatness of each
localized C-module by transitivity. The relative local criterion gives R-flatness
of G(U). Empty U and zero modules are included in the localization criterion. -/
theorem affine_chart_relative_flat_iff {X S : Scheme.{u}} [IsAffine S]
    (f : X ⟶ S) (G : X.Modules) [G.IsQuasicoherent] (U : X.affineOpens) :
    (letI : Module Γ(S, ⊤) Γ(G, U.1) :=
      Module.compHom _ (f.appLE ⊤ U.1 (by simp)).hom
     Module.Flat Γ(S, ⊤) Γ(G, U.1)) ↔
    (∀ x : X, x ∈ U.1 → Module.Flat (S.presheaf.stalk (f x))
      ((ModuleCat.restrictScalars (f.stalkMap x).hom).obj
        ((RingedSpace.moduleStalkFunctor X.toRingedSpace x).obj G))) := by
  constructor
  · intro h x hx
    let R := Γ(S, ⊤)
    let A := Γ(X, U.1)
    let N := Γ(G, U.1)
    let P := (RingedSpace.moduleStalkFunctor X.toRingedSpace x).obj G
    let D := X.presheaf.stalk x
    let B := S.presheaf.stalk (f x)
    let : Algebra R A := (f.appLE ⊤ U.1 (by simp)).hom.toAlgebra
    let : Module R N := Module.compHom N (algebraMap R A)
    have : IsScalarTower R A N := IsScalarTower.of_compHom R A N
    let : Algebra A D := X.presheaf.algebra_section_stalk ⟨x, hx⟩
    let : Module A P := Module.compHom P (algebraMap A D)
    have : IsScalarTower A D P := IsScalarTower.of_compHom A D P
    let : Module R P := Module.compHom P (algebraMap R A)
    have : IsScalarTower R A P := IsScalarTower.of_compHom R A P
    have := U.2.isLocalization_stalk ⟨x, hx⟩
    let Q := (U.2.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl
    have hid : ((𝟙 X : X ⟶ X).appLE U.1 U.1 le_rfl).hom = RingHom.id A := by
      simp only [Scheme.Hom.appLE, Scheme.Hom.id_base, Scheme.Hom.id_app,
        homOfLE_refl, CategoryTheory.op_id, Category.id_comp]
      exact congrArg CommRingCat.Hom.hom (X.presheaf.map_id (Opposite.op U.1))
    have hmod : Module.compHom N ((𝟙 X : X ⟶ X).appLE U.1 U.1 le_rfl).hom =
        (inferInstance : Module A N) := by rw [hid]; rfl
    let E : TensorProduct A D N ≃ₗ[D] P := by
      have he := affine_sections_stalk_tensor_presentation G U x hx
      rw [hmod] at he
      exact he.some
    let ell : N →ₗ[A] P :=
      (E.restrictScalars A).toLinearMap ∘ₗ TensorProduct.mk A D N 1
    have : IsLocalizedModule Q ell :=
      IsLocalizedModule.of_linearEquiv Q (TensorProduct.mk A D N 1) (E.restrictScalars A)
    have hloc : Module.Flat R (LocalizedModule Q N) :=
      Module.Flat.localizedModule_of_algebra Q h
    let e := IsLocalizedModule.linearEquiv Q (LocalizedModule.mkLinearMap Q N) ell
    have : Module.Flat R P := (Module.Flat.equiv_iff (e.restrictScalars R)).mp hloc
    let : Algebra R B := S.presheaf.algebra_section_stalk
      ⟨f x, show f x ∈ (⊤ : S.Opens) from trivial⟩
    let : Module B P := Module.compHom P (f.stalkMap x).hom
    have : IsScalarTower R B P := by
      apply IsScalarTower.of_algebraMap_smul
      intro r m
      change (f.stalkMap x).hom ((S.presheaf.germ ⊤ (f x) (by trivial)).hom r) • m =
        (X.presheaf.germ U.1 x hx).hom ((f.appLE ⊤ U.1 (by simp)).hom r) • m
      rw [f.germ_stalkMap_apply]
      congr 1
      exact (TopCat.Presheaf.germ_res_apply X.presheaf (homOfLE (by simp)) x
        hx (f.app ⊤ r)).symm
    have := (isAffineOpen_top S).isLocalization_stalk ⟨f x, trivial⟩
    exact (Module.flat_iff_of_isLocalization B
      ((isAffineOpen_top S).primeIdealOf ⟨f x, trivial⟩).asIdeal.primeCompl P).mpr
        (inferInstance : Module.Flat R P)
  · intro h
    classical
    let V : S.affineOpens := ⟨⊤, isAffineOpen_top S⟩
    have hUV : U.1 ≤ f ⁻¹ᵁ V.1 := le_top
    let R := Γ(S, V.1)
    let A := Γ(X, U.1)
    let N := Γ(G, U.1)
    let : Algebra R A := (f.appLE V.1 U.1 hUV).hom.toAlgebra
    let : Module R N := Module.compHom N (algebraMap R A)
    have : IsScalarTower R A N := IsScalarTower.of_compHom R A N
    let x (q : Ideal A) [q.IsMaximal] : U.1 :=
      U.2.isoSpec.inv ⟨q, inferInstance⟩
    let P (q : Ideal A) [q.IsMaximal] : Type u :=
      (RingedSpace.moduleStalkFunctor X.toRingedSpace (x q).1).obj G
    let astalk (q : Ideal A) [q.IsMaximal] : Algebra A (X.presheaf.stalk (x q).1) :=
      X.presheaf.algebra_section_stalk (x q)
    let amod (q : Ideal A) [q.IsMaximal] : Module A (P q) :=
      Module.compHom _ (algebraMap A (X.presheaf.stalk (x q).1))
    have towerA (q : Ideal A) [q.IsMaximal] :
        IsScalarTower A (X.presheaf.stalk (x q).1) (P q) :=
      IsScalarTower.of_compHom A (X.presheaf.stalk (x q).1) (P q)
    let rmod (q : Ideal A) [q.IsMaximal] : Module R (P q) :=
      Module.compHom _ (algebraMap R A)
    have tower (q : Ideal A) [q.IsMaximal] : IsScalarTower R A (P q) :=
      IsScalarTower.of_compHom R A (P q)
    have prime (q : Ideal A) [q.IsMaximal] : (U.2.primeIdealOf (x q)).asIdeal = q := by
      change (U.2.isoSpec.hom (U.2.isoSpec.inv ⟨q, inferInstance⟩)).asIdeal = q
      rw [← Scheme.Hom.comp_apply, Iso.inv_hom_id]
      rfl
    have loc (q : Ideal A) [q.IsMaximal] :
        IsLocalization.AtPrime (X.presheaf.stalk (x q).1) q := by
      have hl := U.2.isLocalization_stalk (x q)
      simpa only [IsLocalization.AtPrime, prime q] using hl
    have hid : ((𝟙 X : X ⟶ X).appLE U.1 U.1 le_rfl).hom = RingHom.id A := by
      simp only [Scheme.Hom.appLE, Scheme.Hom.id_base, Scheme.Hom.id_app,
        homOfLE_refl, CategoryTheory.op_id, Category.id_comp]
      exact congrArg CommRingCat.Hom.hom (X.presheaf.map_id (Opposite.op U.1))
    have hmod : Module.compHom N ((𝟙 X : X ⟶ X).appLE U.1 U.1 le_rfl).hom =
        (inferInstance : Module A N) := by
      rw [hid]
      rfl
    let E (q : Ideal A) [q.IsMaximal] :
        TensorProduct A (X.presheaf.stalk (x q).1) N ≃ₗ[X.presheaf.stalk (x q).1] P q := by
      have he := affine_sections_stalk_tensor_presentation G U (x q).1 (x q).2
      rw [hmod] at he
      exact he.some
    let ell (q : Ideal A) [q.IsMaximal] : N →ₗ[A] P q :=
      ((E q).restrictScalars A).toLinearMap ∘ₗ TensorProduct.mk A (X.presheaf.stalk (x q).1) N 1
    have hlocal (q : Ideal A) [q.IsMaximal] : IsLocalizedModule.AtPrime q (ell q) := by
      exact IsLocalizedModule.of_linearEquiv q.primeCompl
        (TensorProduct.mk A (X.presheaf.stalk (x q).1) N 1) ((E q).restrictScalars A)
    apply @Module.flat_of_isLocalized_maximal R A _ _ _ N _ _ _ _ P _ rmod amod
      tower ell hlocal
    intro q hq
    let y := (x q).1
    have hy : f y ∈ V.1 := hUV (x q).2
    let B := S.presheaf.stalk (f y)
    let : Algebra R B := S.presheaf.algebra_section_stalk ⟨f y, hy⟩
    let : Module B (P q) := Module.compHom _ (f.stalkMap y).hom
    have hf : Module.Flat B (P q) := h y (x q).2
    have := V.2.isLocalization_stalk ⟨f y, hy⟩
    have : Module.Flat R B := IsLocalization.flat B
      (V.2.primeIdealOf ⟨f y, hy⟩).asIdeal.primeCompl
    have ht : IsScalarTower R B (P q) := by
      apply IsScalarTower.of_algebraMap_smul
      intro r m
      change (f.stalkMap y).hom ((S.presheaf.germ V.1 (f y) hy).hom r) • m =
        (X.presheaf.germ U.1 y (x q).2).hom ((f.appLE V.1 U.1 hUV).hom r) • m
      rw [f.germ_stalkMap_apply]
      congr 1
      exact (TopCat.Presheaf.germ_res_apply X.presheaf (homOfLE hUV) y
        (x q).2 (f.app V.1 r)).symm
    exact Module.Flat.trans R B (P q)

end AlgebraicGeometry
