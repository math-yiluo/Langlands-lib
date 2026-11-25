/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Modules.FreeGenerator
public import WeilConjectures.AlgebraicGeometry.Modules.LocallyFreeAffine
public import WeilConjectures.AlgebraicGeometry.Modules.ProjectionFormula
public import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Tilde
public import WeilConjectures.Mathlib.RingTheory.PicardGroup

/-!
# Sections of invertible modules over affine opens

Let `M` be an invertible `𝒪_X`-module and `U` an affine open of the scheme `X`. Then `Γ(M, U)` is
an invertible `Γ(X, U)`-module, and `M` is trivial on `U` as soon as `Γ(M, U)` is free of rank
one.

## Main statements

- `AlgebraicGeometry.Scheme.Modules.invertible_sections_of_isAffineOpen`: `Γ(M, U)` is an
  invertible `Γ(X, U)`-module.
- `AlgebraicGeometry.Scheme.Modules.isFreeGenerator_of_bijective_smul`: a section `e` over an
  affine open `U` such that `r ↦ r • e` is a bijection `Γ(X, U) ≃ Γ(M, U)` is a free generator.
- `AlgebraicGeometry.Scheme.Modules.exists_mem_isFreeGenerator_basicOpen`: if the localization of
  `Γ(X, U)` at a submonoid `S` is a unique factorization domain, then `M` is trivial on a basic
  open `D(s) ⊆ U` with `s ∈ S`.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

/-- **Sections of an invertible module over an affine open are an invertible module.** For an
invertible `𝒪_X`-module `M` and an affine open `U`, `Γ(M, U)` is finitely presented and free of
rank one locally on `Spec Γ(X, U)` (on the basic opens trivializing `M`), hence invertible. -/
theorem invertible_sections_of_isAffineOpen (M : X.Modules) [M.IsInvertible] {U : X.Opens}
    (hU : IsAffineOpen U) : Module.Invertible Γ(X, U) Γ(M, U) := by
  have := IsInvertible.sheafOfModules_isInvertible M
  have := (finitePresentation_projective_sections M hU).1
  let s : Set Γ(X, U) := {g | ∃ Y : X.Opens, X.basicOpen g ≤ Y ∧
    Nonempty (M.over Y ≅ SheafOfModules.unit (X.ringCatSheaf.over Y))}
  have hs : Ideal.span s = ⊤ := by
    rw [← hU.self_le_iSup_basicOpen_iff]
    intro x hx
    obtain ⟨Y, hxY, ⟨e⟩⟩ := exists_mem_over_iso_unit M x
    obtain ⟨g, hgY, hxg⟩ := hU.exists_basicOpen_le ⟨x, hxY⟩ hx
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨g, Y, hgY, ⟨e⟩⟩, hxg⟩
  let _ (r : s) : Module Γ(X, U) Γ(M, X.basicOpen r.1) :=
    Module.compHom _ (algebraMap Γ(X, U) Γ(X, X.basicOpen r.1))
  have _ (r : s) := isLocalizedModule_basicOpen M hU r.1
  have _ (r : s) := hU.isLocalization_basicOpen r.1
  have _ (r : s) : IsScalarTower Γ(X, U) Γ(X, X.basicOpen r.1) Γ(M, X.basicOpen r.1) :=
    ⟨fun a b m ↦ mul_smul _ _ _⟩
  refine Module.Invertible.of_isLocalized_span s hs (fun r ↦ Γ(X, X.basicOpen r.1))
    (fun r ↦ Γ(M, X.basicOpen r.1)) (fun r ↦
      { toFun := M.presheaf.map (homOfLE (X.basicOpen_le r.1)).op
        map_add' := map_add _
        map_smul' := map_smul M _ }) fun r ↦ ?_
  obtain ⟨Y, hY, ⟨e⟩⟩ := r.2
  exact ⟨sectionsLinearEquivOfOverIsoUnit e hY⟩

/-- Let `M` be quasi-coherent, `U` an affine open and `e ∈ Γ(M, U)` such that `r ↦ r • e` is a
bijection `Γ(X, U) ≃ Γ(M, U)`. Then for every `g ∈ Γ(X, U)`, `r ↦ r • e|_{D(g)}` is a bijection
`Γ(X, D(g)) ≃ Γ(M, D(g))`, being the localization at `g` of the former bijection. -/
lemma bijective_smul_map_basicOpen (M : X.Modules)
    [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) M] {U : X.Opens} (hU : IsAffineOpen U)
    {e : Γ(M, U)} (he : Function.Bijective fun r : Γ(X, U) ↦ r • e) (g : Γ(X, U)) :
    Function.Bijective fun r : Γ(X, X.basicOpen g) ↦
      r • M.presheaf.map (homOfLE (X.basicOpen_le g)).op e := by
  let : Module Γ(X, U) Γ(M, X.basicOpen g) :=
    Module.compHom _ (algebraMap Γ(X, U) Γ(X, X.basicOpen g))
  have := isLocalizedModule_basicOpen M hU g
  have := hU.isLocalization_basicOpen g
  let ψ : Γ(X, X.basicOpen g) →ₗ[Γ(X, U)] Γ(M, X.basicOpen g) :=
    { toFun r := r • M.presheaf.map (homOfLE (X.basicOpen_le g)).op e
      map_add' a b := add_smul a b _
      map_smul' a r := mul_smul _ _ _ }
  let res : Γ(M, U) →ₗ[Γ(X, U)] Γ(M, X.basicOpen g) :=
    { toFun := M.presheaf.map (homOfLE (X.basicOpen_le g)).op
      map_add' := map_add _
      map_smul' := map_smul M _ }
  have hψ : ψ = IsLocalizedModule.map (.powers g) (Algebra.linearMap _ _) res
      (LinearMap.toSpanSingleton _ _ e) := by
    refine IsLocalizedModule.ext (.powers g) (Algebra.linearMap _ _)
      (IsLocalizedModule.map_units (S := .powers g) res) ?_
    rw [IsLocalizedModule.map_comp]
    ext
    simp [ψ, res]
  have hb : Function.Bijective ψ := by
    rw [hψ]
    exact ⟨IsLocalizedModule.map_injective _ _ _ _ he.1,
      IsLocalizedModule.map_surjective _ _ _ _ he.2⟩
  exact hb

/-- If `f` is a free generator of `M` on `U` and `e` is a section over `U` such that `r ↦ r • e`
is a bijection `Γ(X, U) ≃ Γ(M, U)`, then `e` is a unit multiple of `f`, hence a free
generator. -/
lemma IsFreeGenerator.of_bijective_smul {M : X.Modules} {U : X.Opens} {e f : Γ(M, U)}
    (hf : IsFreeGenerator f) (he : Function.Bijective fun r : Γ(X, U) ↦ r • e) :
    IsFreeGenerator e := by
  obtain ⟨a, rfl⟩ := hf.exists_smul_eq e
  obtain ⟨b, hb⟩ := he.2 f
  dsimp only at hb
  have hba : b * a = 1 := hf.smul_left_injective (by simp only [mul_smul, one_smul, hb])
  exact hf.units_smul ⟨a, b, by rw [mul_comm, hba], hba⟩

/-- **A free generator from a basis of the sections over an affine open.** Let `M` be an
invertible `𝒪_X`-module and `e` a section of `M` over an affine open `U` such that `r ↦ r • e`
is a bijection `Γ(X, U) ≃ Γ(M, U)`. Then `e` is a free generator of `M` on `U`: on every basic
open `D(g) ⊆ U` the sections of `𝒪_X` and of `M` are the localizations at `g`. -/
theorem isFreeGenerator_of_bijective_smul (M : X.Modules) [M.IsInvertible] {U : X.Opens}
    (hU : IsAffineOpen U) {e : Γ(M, U)} (he : Function.Bijective fun r : Γ(X, U) ↦ r • e) :
    IsFreeGenerator e := by
  have := IsInvertible.sheafOfModules_isInvertible M
  let S : Sieve U :=
    { arrows V _ := ∃ g : Γ(X, U), V ≤ X.basicOpen g ∧
        ∃ W : X.Opens, X.basicOpen g ≤ W ∧ ∃ f : Γ(M, W), IsFreeGenerator f
      downward_closed := by
        rintro V V' i ⟨g, hg, h⟩ j
        exact ⟨g, (leOfHom j).trans hg, h⟩ }
  refine isFreeGenerator_of_mem e (S := S) ?_ ?_
  · intro x hx
    obtain ⟨W, hxW, hWU, f, hf⟩ := exists_isFreeGenerator M hx
    obtain ⟨g, hgW, hxg⟩ := hU.exists_basicOpen_le ⟨x, hxW⟩ hx
    exact ⟨_, homOfLE (X.basicOpen_le g), ⟨g, le_rfl, W.1, hgW, f, hf⟩, hxg⟩
  · rintro V i ⟨g, hVg, W, hgW, f, hf⟩
    have hg := (hf.map hgW).of_bijective_smul (bijective_smul_map_basicOpen M hU he g)
    have := hg.map hVg
    rwa [presheaf_map_map_apply] at this

/-- **Triviality near a UFD localization.** Let `M` be an invertible `𝒪_X`-module, `U` an affine
open and `S` a submonoid of `Γ(X, U)` whose localization is a unique factorization domain. Then
`M` is trivial on a basic open `D(s) ⊆ U` for some `s ∈ S`. -/
theorem exists_mem_isFreeGenerator_basicOpen (M : X.Modules) [M.IsInvertible] {U : X.Opens}
    (hU : IsAffineOpen U) (S : Submonoid Γ(X, U)) [IsDomain (Localization S)]
    [UniqueFactorizationMonoid (Localization S)] :
    ∃ s ∈ S, ∃ e : Γ(M, X.basicOpen s), IsFreeGenerator e := by
  have := invertible_sections_of_isAffineOpen M hU
  obtain ⟨s, hs, m, H⟩ := Module.Invertible.exists_mem_bijective_smul (M := Γ(M, U)) S
  let : Module Γ(X, U) Γ(M, X.basicOpen s) :=
    Module.compHom _ (algebraMap Γ(X, U) Γ(X, X.basicOpen s))
  have := isLocalizedModule_basicOpen M hU s
  have := hU.isLocalization_basicOpen s
  have : IsScalarTower Γ(X, U) Γ(X, X.basicOpen s) Γ(M, X.basicOpen s) :=
    ⟨fun a b m ↦ mul_smul _ _ _⟩
  exact ⟨s, hs, _, isFreeGenerator_of_bijective_smul M (hU.basicOpen s)
    (H Γ(X, X.basicOpen s) Γ(M, X.basicOpen s)
      { toFun := M.presheaf.map (homOfLE (X.basicOpen_le s)).op
        map_add' := map_add _
        map_smul' := map_smul M _ })⟩

end AlgebraicGeometry.Scheme.Modules
