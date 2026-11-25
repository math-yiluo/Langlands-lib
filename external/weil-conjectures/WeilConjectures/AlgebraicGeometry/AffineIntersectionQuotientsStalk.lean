/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
public import WeilConjectures.Algebra.Homology.ModuleStalkFunctor
public import Mathlib.Order.Hom.Basic
import WeilConjectures.AlgebraicGeometry.Morphisms.AffineModuleGermLocalization
import Mathlib.Algebra.Module.LocalizedModule.Submodule
import WeilConjectures.AlgebraicGeometry.QuasicoherentPushforwardQcqs
import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel

/-! # Localization of affine intersection quotient systems

Source: Stacks Project, Tags 01IB, 01IC, and 00CS; ideal products as in 01I8.
(blueprint: lem-weil-pbc-affine-intersection-quotients-stalk).
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
/-- Localizing compatible affine quotients preserves any prescribed kernel filtration.

Source: Stacks Project, Schemes, Tags 01IB and 01IC, and Algebra, Tag 00CS.
(blueprint: lem-weil-pbc-affine-intersection-quotients-stalk).

Proof: Put A = Gamma(U,O_X), B = O_(X,x), and let P be the prime of x in U.
Construct M = B tensor_A L, with L restricted from R to A. The affine
quasi-coherent stalk correspondence identifies each stalk S_m,x with the
localization of Gamma(U,S_m); localize q_m to define p_m. Naturality of germs
identifies the localized section transitions with the stalk transitions, giving
compatibility of all p_m. Localization preserves surjectivity and exactness.
For an R-submodule Q of L, define phi(Q) as the image of B tensor_A Q in M.
Inclusions of submodules make this an order homomorphism. Exactness applied to
the section kernel criterion identifies ker p_m with phi(D_m). Restriction of
scalars identifies K^r L with
I(U)^r L: K is the extended ideal, R coefficients can be absorbed into elements
of L, and ideal extension commutes with powers. Localization of ideal products
therefore gives phi(K^r L) = (I(U)B)^r M. The quasi-coherent ideal/stalk
correspondence identifies I(U)B with the image J of the ideal stalk inclusion;
the assumed germ equation for e ensures it uses exactly this unit-stalk
identification. This also proves the formula at r=0, since localization of the
identity on L has full image. No finiteness, Noetherian hypothesis, completion,
formal module, kernel stabilization, or Artin--Rees bound is used. If U is empty
there is no x; zero or unit ideals and zero modules obey the same equations. -/
theorem affine_intersection_quotients_stalk
    {X : Scheme.{u}} (I : X.IdealSheafData) (S : ℕᵒᵖ ⥤ X.Modules)
    (U : X.affineOpens)
    (R : Type u) [CommRing R] [Algebra Γ(X, U.1) R]
    (L : ModuleCat.{u} R) (D : ℕ → Submodule R L)
    (q : ∀ m : ℕ,
      ((ModuleCat.restrictScalars (algebraMap Γ(X, U.1) R)).obj L)
        →ₗ[Γ(X, U.1)] Γ(S.obj (op m), U.1))
    (hqc : ∀ m : ℕ, (S.obj (op m)).IsQuasicoherent)
    (hq : ∀ m : ℕ, Function.Surjective (q m))
    (ht : ∀ (a b : ℕ) (h : a ≤ b) (z : L),
      (S.map (homOfLE h).op).app U.1 (q b z) = q a z)
    (hk : ∀ (m : ℕ) (z : L), q m z = 0 ↔ z ∈ D m)
    (x : X) (hx : x ∈ U.1)
    (e : (RingedSpace.moduleStalkFunctor X.toRingedSpace x).obj
        (SheafOfModules.unit X.ringCatSheaf) ≅
        ModuleCat.of (X.presheaf.stalk x) (X.presheaf.stalk x))
    (he : ∀ (V : X.Opens) (hx : x ∈ V) (r : Γ(X, V)),
      e.hom (TopCat.Presheaf.germ (SheafOfModules.unit X.ringCatSheaf).val.presheaf
        V x hx r) = X.presheaf.germ V x hx r) :
    let K := (I.ideal U).map (algebraMap Γ(X, U.1) R)
    let T := RingedSpace.moduleStalkFunctor X.toRingedSpace x
    let J : Ideal (X.presheaf.stalk x) := LinearMap.range (T.map I.toModulesι ≫ e.hom).hom
    ∃ M : ModuleCat.{u} (X.presheaf.stalk x),
      ∃ p : ∀ m : ℕ, M →ₗ[X.presheaf.stalk x] T.obj (S.obj (op m)),
        (∀ m : ℕ, Function.Surjective (p m)) ∧
        (∀ (a b : ℕ) (h : a ≤ b) (z : M),
          (T.map (S.map (homOfLE h).op)).hom (p b z) = p a z) ∧
        ∃ φ : Submodule R L →o Submodule (X.presheaf.stalk x) M,
          (∀ r : ℕ, φ (K ^ r • (⊤ : Submodule R L)) =
            J ^ r • (⊤ : Submodule (X.presheaf.stalk x) M)) ∧
          (∀ m : ℕ, LinearMap.ker (p m) =
            φ (D m)) := by
  classical
  let A := Γ(X, U.1)
  let B := X.presheaf.stalk x
  let W := (U.2.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl
  let T := RingedSpace.moduleStalkFunctor X.toRingedSpace x
  let : Algebra A B := X.presheaf.algebra_section_stalk ⟨x, hx⟩
  let : IsLocalization W B := U.2.isLocalization_stalk ⟨x, hx⟩
  let : Module A L := Module.compHom _ (algebraMap A R)
  let : IsScalarTower A R L := IsScalarTower.of_algebraMap_smul fun r z ↦ rfl
  let L₀ := (ModuleCat.restrictScalars (algebraMap A R)).obj L
  let M₀ := LocalizedModule W L₀
  let : Module B M₀ := LocalizedModule.moduleOfIsLocalization
  let : IsScalarTower A B M₀ := inferInstance
  let f : L₀ →ₗ[A] M₀ := LocalizedModule.mkLinearMap W L₀
  let (m : ℕ) : Module A
      (TopCat.Presheaf.stalk (C := Ab.{u}) (X := X) (S.obj (op m)).val.presheaf x) :=
    Module.compHom _ (X.presheaf.germ U.1 x hx).hom
  let (m : ℕ) : Module A (T.obj (S.obj (op m))) :=
    Module.compHom _ (X.presheaf.germ U.1 x hx).hom
  let (m : ℕ) : IsScalarTower A B (T.obj (S.obj (op m))) :=
    IsScalarTower.of_algebraMap_smul fun r z ↦ rfl
  let g (m : ℕ) : Γ(S.obj (op m), U.1) →ₗ[A] T.obj (S.obj (op m)) :=
    { toFun := (S.obj (op m)).presheaf.germ U.1 x hx
      map_add' := map_add _
      map_smul' := fun r z ↦ PresheafOfModules.germ_smul (R := X.presheaf)
        (S.obj (op m)).val x U.1 hx r z }
  have hg (m : ℕ) (z : Γ(S.obj (op m), U.1)) :
      g m z = (S.obj (op m)).presheaf.germ U.1 x hx z := rfl
  let (m : ℕ) : IsLocalizedModule W (g m) := by
    obtain ⟨g', hg', hloc⟩ := Scheme.isLocalizedModule_affine_germ
      (S.obj (op m)) (hqc m) U.1 U.2 ⟨x, hx⟩
    convert hloc using 1 <;> try rfl
    apply LinearMap.ext
    intro z
    exact (hg' z).symm
  let p (m : ℕ) : M₀ →ₗ[B] T.obj (S.obj (op m)) :=
    (IsLocalizedModule.map W f (g m) (q m)).extendScalarsOfIsLocalization W B
  let φ : Submodule R L →o Submodule B M₀ :=
    { toFun := fun Q ↦ (Q.restrictScalars A).localized' B W f
      monotone' := fun Q Q' h ↦
        (Submodule.localized'gi B W f).gc.monotone_l h }
  refine ⟨ModuleCat.of B M₀, p, ?_, ?_, φ, ?_, ?_⟩
  · intro m
    exact IsLocalizedModule.map_surjective W f (g m) (q m) (hq m)
  · intro a b h z
    have hp : ((T.map (S.map (homOfLE h).op)).hom.comp (p b)).restrictScalars A =
        (p a).restrictScalars A := by
      apply IsLocalizedModule.linearMap_ext W f (g a)
      ext t
      dsimp only [LinearMap.comp_apply, LinearMap.restrictScalars_apply, p]
      rw [LinearMap.extendScalarsOfIsLocalization_apply', IsLocalizedModule.map_apply,
        LinearMap.extendScalarsOfIsLocalization_apply', IsLocalizedModule.map_apply]
      rw [hg b, hg a]
      change RingedSpace.stalkAddMap X.toRingedSpace x
        (S.map (homOfLE h).op) ((S.obj (op b)).presheaf.germ U.1 x hx (q b t)) = _
      dsimp only [RingedSpace.stalkAddMap]
      erw [TopCat.Presheaf.stalkFunctor_map_germ_apply]
      exact congrArg ((S.obj (op a)).presheaf.germ U.1 x hx) (ht a b h t)
    exact LinearMap.congr_fun hp z
  · have hIqc : I.toModules.IsQuasicoherent := by
      have := SheafOfModules.isQuasicoherent_unit (R := I.subscheme.ringCatSheaf)
      have := SheafOfModules.isQuasicoherent_unit (R := X.ringCatSheaf)
      have : SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf)
          ((SheafOfModules.pushforward I.subschemeι.toRingCatSheafHom).obj
            (SheafOfModules.unit I.subscheme.ringCatSheaf)) :=
        Scheme.Modules.isQuasicoherent_pushforward_of_quasiCompact_quasiSeparated
          I.subschemeι _
      exact Scheme.Modules.isQuasicoherent_kernel I.toPushforwardSubscheme
    let : Module A
        (TopCat.Presheaf.stalk (C := Ab.{u}) (X := X) I.toModules.val.presheaf x) :=
      Module.compHom _ (X.presheaf.germ U.1 x hx).hom
    let : Module A (T.obj I.toModules) :=
      Module.compHom _ (X.presheaf.germ U.1 x hx).hom
    let : IsScalarTower A B (T.obj I.toModules) :=
      IsScalarTower.of_algebraMap_smul fun r z ↦ rfl
    let : IsScalarTower A B
        (TopCat.Presheaf.stalk (C := Ab.{u}) (X := X) I.toModules.val.presheaf x) :=
      IsScalarTower.of_algebraMap_smul fun r z ↦ rfl
    obtain ⟨gI, hgI, hlocI⟩ := Scheme.isLocalizedModule_affine_germ
      I.toModules hIqc U.1 U.2 ⟨x, hx⟩
    let : IsLocalizedModule W gI := hlocI
    let i : Γ(I.toModules, U.1) →ₗ[A] A := (I.toModulesι.val.app (op U.1)).hom
    have hi : LinearMap.range i = I.ideal U := by
      apply SetLike.ext'
      exact I.range_toModulesι_app U
    have hmap : IsLocalizedModule.map W gI (Algebra.linearMap A B) i =
        (T.map I.toModulesι ≫ e.hom).hom.restrictScalars A := by
      apply IsLocalizedModule.linearMap_ext W gI (Algebra.linearMap A B)
      ext z
      rw [LinearMap.comp_apply, IsLocalizedModule.map_apply, LinearMap.comp_apply, hgI]
      change X.presheaf.germ U.1 x hx (i z) =
        e.hom (RingedSpace.stalkAddMap X.toRingedSpace x I.toModulesι
          (I.toModules.presheaf.germ U.1 x hx z))
      dsimp only [RingedSpace.stalkAddMap]
      erw [TopCat.Presheaf.stalkFunctor_map_germ_apply]
      exact (he U.1 hx (i z)).symm
    have hJ : LinearMap.range (T.map I.toModulesι ≫ e.hom).hom =
        (I.ideal U).map (algebraMap A B) := by
      have hh := LinearMap.localized'_range_eq_range_localizedMap B W gI
        (Algebra.linearMap A B) i
      rw [hi, hmap] at hh
      change _ = LinearMap.range (T.map I.toModulesι ≫ e.hom).hom at hh
      rw [← hh, Submodule.localized'_eq_span]
      rfl
    intro r
    change (((I.ideal U).map (algebraMap A R) ^ r •
      (⊤ : Submodule R L)).restrictScalars A).localized' B W f = _
    rw [← Ideal.map_pow, Submodule.restrictScalars_map_smul_eq,
      Submodule.restrictScalars_top, Submodule.localized'_smul,
      Submodule.localized'_top, Submodule.localized'_eq_span]
    change (I.ideal U ^ r).map (algebraMap A B) • (⊤ : Submodule B M₀) = _
    rw [Ideal.map_pow, hJ]
  · intro m
    have hk' : LinearMap.ker (q m) = (D m).restrictScalars A := by
      ext z
      exact hk m z
    exact ((LinearMap.localized'_ker_eq_ker_localizedMap B W f (g m) (q m)).symm).trans
      (congrArg (Submodule.localized' B W f) hk')

end AlgebraicGeometry
