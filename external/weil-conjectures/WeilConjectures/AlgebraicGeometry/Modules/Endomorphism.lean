/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Cohomology.Defs
public import WeilConjectures.AlgebraicGeometry.Modules.FreeGenerator
public import WeilConjectures.AlgebraicGeometry.Modules.ProjectionFormula

/-!
# Endomorphisms of invertible modules

Every endomorphism of an invertible `𝒪_X`-module `ℒ` is multiplication by a global function, and
multiplication by global functions is compatible with pullback. As a consequence we obtain a
rigidity statement: if `g : Z ⟶ B` has a section `s` and `Γ(B, 𝒪_B) ⟶ Γ(Z, 𝒪_Z)` is surjective,
then an endomorphism of an invertible `𝒪_Z`-module is determined by its pullback along `s`.

## Main statements

- `AlgebraicGeometry.Scheme.Modules.exists_eq_smulHom`: every endomorphism of an invertible
  module is `ℒ.smulHom c` for a global function `c`.
- `AlgebraicGeometry.Scheme.Modules.eq_of_smulHom_eq`: on an invertible module, multiplication
  by global functions is faithful.
- `AlgebraicGeometry.Scheme.Modules.pullback_map_smulHom`: the pullback of multiplication by `c`
  is multiplication by the pullback of `c`.
- `AlgebraicGeometry.Scheme.Modules.eq_of_pullback_map_eq`: the rigidity statement.
-/

@[expose] public section

universe u

open CategoryTheory Opposite TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

section Generator

variable {M : X.Modules} {U : X.Opens}
  (e : M.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U))

/-- The generator of an `𝒪_X`-module `M` over an open `U` given by a trivialisation
`M.over U ≅ 𝒪_U`: the section of `M` over `U` corresponding to `1`. -/
noncomputable def generatorOfOverIsoUnit : Γ(M, U) :=
  (sectionsLinearEquivOfOverIsoUnit e le_rfl).symm 1

lemma sectionsLinearEquivOfOverIsoUnit_symm_one {W : X.Opens} (h : W ≤ U) :
    (sectionsLinearEquivOfOverIsoUnit e h).symm 1 =
      M.presheaf.map (homOfLE h).op (generatorOfOverIsoUnit e) := by
  have := ConcreteCategory.congr_hom
    (e.inv.val.naturality (Over.homMk (homOfLE h) : Over.mk (homOfLE h) ⟶
      Over.mk (homOfLE (le_refl U))).op) (1 : Γ(X, U))
  refine Eq.trans ?_ (this.trans rfl)
  exact congrArg (e.inv.val.app (op (Over.mk (homOfLE h)))).hom
    (map_one (X.presheaf.map (homOfLE h).op).hom).symm

lemma eq_smul_generatorOfOverIsoUnit {W : X.Opens} (h : W ≤ U) (m : Γ(M, W)) :
    m = sectionsLinearEquivOfOverIsoUnit e h m •
      M.presheaf.map (homOfLE h).op (generatorOfOverIsoUnit e) := by
  rw [← sectionsLinearEquivOfOverIsoUnit_symm_one, ← LinearEquiv.map_smul, smul_eq_mul, mul_one,
    LinearEquiv.symm_apply_apply]

lemma smul_generatorOfOverIsoUnit_injective {W : X.Opens} (h : W ≤ U) :
    Function.Injective fun a : Γ(X, W) ↦
      a • M.presheaf.map (homOfLE h).op (generatorOfOverIsoUnit e) := by
  intro a b hab
  have := congrArg (sectionsLinearEquivOfOverIsoUnit e h) hab
  simpa [← sectionsLinearEquivOfOverIsoUnit_symm_one] using this

end Generator

section Invertible

variable (M : X.Modules) [M.IsInvertible]

/-- **Endomorphisms of an invertible module are scalars.** Every endomorphism of an invertible
`𝒪_X`-module `M` is multiplication by a global function: on an open `U` where `M` is generated
by a single section `g`, the endomorphism sends `g` to `c_U • g`, and the functions `c_U` glue. -/
theorem exists_eq_smulHom (φ : M ⟶ M) : ∃ c : Γ(X, ⊤), φ = M.smulHom c := by
  have := IsInvertible.sheafOfModules_isInvertible M
  choose U hU e using fun x : X ↦ exists_mem_over_iso_unit M x
  let g (x : X) := generatorOfOverIsoUnit (e x).some
  let c (x : X) : Γ(X, U x) :=
    sectionsLinearEquivOfOverIsoUnit (e x).some le_rfl (φ.app (U x) (g x))
  have hc (x : X) {W : X.Opens} (hW : W ≤ U x) (m : Γ(M, W)) :
      φ.app W m = X.presheaf.map (homOfLE hW).op (c x) • m := by
    have h₀ := eq_smul_generatorOfOverIsoUnit (e x).some (le_refl (U x)) (φ.app (U x) (g x))
    have h₁ : M.presheaf.map (homOfLE (le_refl (U x))).op (g x) = g x := by
      rw [show homOfLE (le_refl (U x)) = 𝟙 _ from rfl, op_id, M.presheaf.map_id]
      rfl
    rw [h₁] at h₀
    rw [eq_smul_generatorOfOverIsoUnit (e x).some hW m, Hom.app_smul, Hom.app_presheaf_map, h₀,
      map_smul, smul_comm]
  have hcompat : TopCat.Presheaf.IsCompatible X.sheaf.1 U c := by
    intro x y
    refine smul_generatorOfOverIsoUnit_injective (e x).some (inf_le_left : U x ⊓ U y ≤ U x) ?_
    exact (hc x (W := U x ⊓ U y) inf_le_left _).symm.trans (hc y inf_le_right _)
  obtain ⟨c₀, hc₀, -⟩ : ∃! c₀ : Γ(X, ⊤), ∀ x, X.presheaf.map (homOfLE le_top : U x ⟶ ⊤).op c₀ =
      c x := X.sheaf.existsUnique_gluing' U ⊤ (fun _ ↦ homOfLE le_top)
    (fun x _ ↦ Opens.mem_iSup.mpr ⟨x, hU x⟩) c hcompat
  refine ⟨c₀, hom_ext _ _ fun W ↦ ?_⟩
  ext m
  refine (TopCat.Sheaf.eq_of_locally_eq' ⟨M.presheaf, M.isSheaf⟩ (fun x ↦ W ⊓ U x) W
    (fun _ ↦ homOfLE inf_le_left) (fun y hy ↦ Opens.mem_iSup.mpr ⟨y, hy, hU y⟩) _ _ fun x ↦ ?_)
  change M.presheaf.map (homOfLE inf_le_left : W ⊓ U x ⟶ W).op (φ.app W m) =
    M.presheaf.map (homOfLE inf_le_left : W ⊓ U x ⟶ W).op ((M.smulHom c₀).app W m)
  rw [← Hom.app_presheaf_map, hc x inf_le_right, smulHom_app_apply, map_smul, ← hc₀ x]
  congr 1
  change (X.presheaf.map _ ≫ X.presheaf.map _) c₀ = (X.presheaf.map _ ≫ X.presheaf.map _) c₀
  rw [← Functor.map_comp, ← Functor.map_comp]
  rfl

/-- **Multiplication by global functions is faithful on an invertible module.** -/
theorem eq_of_smulHom_eq {c d : Γ(X, ⊤)} (h : M.smulHom c = M.smulHom d) : c = d := by
  have := IsInvertible.sheafOfModules_isInvertible M
  choose U hU e using fun x : X ↦ exists_mem_over_iso_unit M x
  refine TopCat.Sheaf.eq_of_locally_eq' X.sheaf U ⊤ (fun _ ↦ homOfLE le_top)
    (fun x _ ↦ Opens.mem_iSup.mpr ⟨x, hU x⟩) c d fun x ↦ ?_
  refine smul_generatorOfOverIsoUnit_injective (e x).some (le_refl (U x)) ?_
  have := congrArg (fun φ ↦ φ.app (U x) (M.presheaf.map (homOfLE (le_refl (U x))).op
    (generatorOfOverIsoUnit (e x).some))) h
  simp only [smulHom_app_apply] at this
  exact this

end Invertible

section Functoriality

variable {Y : Scheme.{u}} (g : X ⟶ Y)

/-- **Pullback of multiplication by a global function.** The pullback along `g` of
multiplication by `c` is multiplication by `g^♯ c`. -/
lemma pullback_map_smulHom (M : Y.Modules) (c : Γ(Y, ⊤)) :
    (pullback g).map (M.smulHom c) = ((pullback g).obj M).smulHom (g.appTop c) := by
  apply ((pullbackPushforwardAdjunction g).homEquiv _ _).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, pushforward_map_smulHom]
  erw [← (pullbackPushforwardAdjunction g).unit.naturality (M.smulHom c)]
  exact smulHom_naturality _ _

end Functoriality

/-- **Rigidity.** Let `p : Z ⟶ B` be a morphism with a section `s` such that
`p^♯ : Γ(B, 𝒪_B) ⟶ Γ(Z, 𝒪_Z)` is surjective. Two morphisms `φ, ψ : A ⟶ C` from an invertible
`𝒪_Z`-module, with `ψ` an isomorphism, which agree after pullback along `s` are equal: the
endomorphism `φ ≫ ψ⁻¹` of `A` is multiplication by a function `p^♯ b`, and its pullback along
`s` is multiplication by `s^♯ p^♯ b = b`, so `b = 1`. -/
theorem eq_of_pullback_map_eq {Z B : Scheme.{u}} (p : Z ⟶ B) (s : B ⟶ Z) (hs : s ≫ p = 𝟙 B)
    (hp : Function.Surjective p.appTop) {A C : Z.Modules} [A.IsInvertible] (φ ψ : A ⟶ C)
    [IsIso ψ] (h : (pullback s).map φ = (pullback s).map ψ) : φ = ψ := by
  obtain ⟨c, hc⟩ := exists_eq_smulHom A (φ ≫ inv ψ)
  obtain ⟨b, rfl⟩ := hp c
  have hb : ((pullback s).obj A).smulHom b = ((pullback s).obj A).smulHom 1 := by
    have h₁ : s.appTop (p.appTop b) = b := by
      rw [← ConcreteCategory.comp_apply, ← Scheme.Hom.comp_appTop, hs]
      rfl
    rw [smulHom_one, ← h₁, ← pullback_map_smulHom, ← hc, Functor.map_comp, h, Functor.map_inv,
      IsIso.hom_inv_id]
  rw [eq_of_smulHom_eq _ hb, map_one, smulHom_one] at hc
  rw [← cancel_mono (inv ψ), IsIso.hom_inv_id, hc]

end AlgebraicGeometry.Scheme.Modules
