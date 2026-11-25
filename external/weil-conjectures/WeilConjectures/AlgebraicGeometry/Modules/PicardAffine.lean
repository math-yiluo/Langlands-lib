/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Modules.FreeGenerator
public import WeilConjectures.AlgebraicGeometry.Modules.LocallyFreeAffine
public import WeilConjectures.Mathlib.RingTheory.PicardGroup

/-!
# Invertible modules over affine opens with trivial Picard group

Let `L` be an invertible `𝒪_X`-module and `U` an affine open of the scheme `X`. The sections
`Γ(L, U)` form an invertible `Γ(X, U)`-module, since they are finitely presented and localize to
the free modules of rank one `Γ(L, D(g))` on basic opens `D(g) ⊆ U` trivializing `L`. Hence if the
Picard group of `Γ(X, U)` is trivial, `Γ(L, U)` is free of rank one, and a basis vector is a free
generator of `L` on `U`. This applies in particular when `Γ(X, U)` is a unique factorization
domain.

## Main statements

- `AlgebraicGeometry.Scheme.Modules.invertible_sections_of_isAffineOpen`: the sections of an
  invertible module over an affine open are an invertible module.
- `AlgebraicGeometry.Scheme.Modules.exists_isFreeGenerator_of_isAffineOpen`: an invertible module
  is trivial on an affine open `U` with `Pic Γ(X, U) = 0`.
- `AlgebraicGeometry.Scheme.Modules.exists_isFreeGenerator_of_uniqueFactorizationMonoid`: an
  invertible module is trivial on an affine open `U` such that `Γ(X, U)` is a UFD.
-/

@[expose] public section

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

/-- An invertible module has free generators on basic opens `D(g)` of an affine open `U`
covering `U`. -/
lemma exists_isFreeGenerator_basicOpen (L : X.Modules) [SheafOfModules.IsInvertible.{u, u, u} L]
    {U : X.Opens} (hU : IsAffineOpen U) {x : X} (hx : x ∈ U) :
    ∃ g : Γ(X, U), x ∈ X.basicOpen g ∧ ∃ f : Γ(L, X.basicOpen g), IsFreeGenerator f := by
  obtain ⟨V, hxV, -, f, hf⟩ := exists_isFreeGenerator L hx
  obtain ⟨g, hgV, hxg⟩ := hU.exists_basicOpen_le ⟨x, hxV⟩ hx
  exact ⟨g, hxg, _, hf.map hgV⟩

/-- **Sections of invertible modules over affine opens.** The sections `Γ(L, U)` of an invertible
`𝒪_X`-module over an affine open `U` form an invertible `Γ(X, U)`-module: they are finitely
presented, and localize to the free modules of rank one `Γ(L, D(g))` over the basic opens `D(g)`
on which `L` is trivial. -/
private theorem invertible_sections_of_isAffineOpen (L : X.Modules)
    [SheafOfModules.IsInvertible.{u, u, u} L] {U : X.Opens} (hU : IsAffineOpen U) :
    Module.Invertible Γ(X, U) Γ(L, U) := by
  have := SheafOfModules.IsInvertible.isFiniteLocallyFree L
  have := SheafOfModules.IsFiniteLocallyFree.isLocallyFree L
  have := SheafOfModules.instIsQuasicoherentOfIsLocallyFree L
  let s : Set Γ(X, U) := {g | ∃ f : Γ(L, X.basicOpen g), IsFreeGenerator f}
  have hs : Ideal.span s = ⊤ := by
    rw [← hU.self_le_iSup_basicOpen_iff]
    intro x hx
    obtain ⟨g, hxg, hg⟩ := exists_isFreeGenerator_basicOpen L hU hx
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨g, hg⟩, hxg⟩
  let _ (g : Γ(X, U)) : Module Γ(X, U) Γ(L, X.basicOpen g) :=
    Module.compHom _ (algebraMap Γ(X, U) Γ(X, X.basicOpen g))
  have _ (g : Γ(X, U)) := isLocalizedModule_basicOpen L hU g
  have _ (g : Γ(X, U)) := hU.isLocalization_basicOpen g
  have _ (g : Γ(X, U)) : IsScalarTower Γ(X, U) Γ(X, X.basicOpen g) Γ(L, X.basicOpen g) :=
    ⟨fun a b m ↦ mul_smul _ _ _⟩
  have := (finitePresentation_projective_sections L hU).1
  refine Module.Invertible.of_isLocalized_span s hs (fun r ↦ Γ(X, X.basicOpen r.1))
    (fun r ↦ Γ(L, X.basicOpen r.1)) (fun r ↦
      { toFun := L.presheaf.map (homOfLE (X.basicOpen_le r.1)).op
        map_add' := map_add _
        map_smul' := map_smul L _ }) fun r ↦ ?_
  obtain ⟨f, hf⟩ := r.2
  exact ⟨(LinearEquiv.ofBijective (LinearMap.toSpanSingleton _ _ f) hf.bijective).symm⟩

/-- **Generators of sections over affine opens are free generators.** If a section `e` of an
invertible module `L` over an affine open `U` generates the `Γ(X, U)`-module `Γ(L, U)`, then `e`
is a free generator of `L` on `U`. Indeed, on a basic open `D(g) ⊆ U` on which `L` has a free
generator `f`, write `e|_{D(g)} = a • f`; as `e|_{D(g)}` generates the localization
`Γ(L, D(g))` of `Γ(L, U)`, the coefficient `a` is a unit. -/
theorem isFreeGenerator_of_surjective_smul (L : X.Modules)
    [SheafOfModules.IsInvertible.{u, u, u} L] {U : X.Opens} (hU : IsAffineOpen U) (e : Γ(L, U))
    (he : Function.Surjective fun r : Γ(X, U) ↦ r • e) : IsFreeGenerator e := by
  have := SheafOfModules.IsInvertible.isFiniteLocallyFree L
  have := SheafOfModules.IsFiniteLocallyFree.isLocallyFree L
  have := SheafOfModules.instIsQuasicoherentOfIsLocallyFree L
  -- `e` is a free generator on every basic open `D(g)` on which `L` has a free generator
  have hloc {g : Γ(X, U)} {f : Γ(L, X.basicOpen g)} (hf : IsFreeGenerator f) :
      IsFreeGenerator (L.presheaf.map (homOfLE (X.basicOpen_le g)).op e) := by
    let _ : Module Γ(X, U) Γ(L, X.basicOpen g) :=
      Module.compHom _ (algebraMap Γ(X, U) Γ(X, X.basicOpen g))
    have := isLocalizedModule_basicOpen L hU g
    have := hU.isLocalization_basicOpen g
    obtain ⟨a, ha⟩ := hf.exists_smul_eq (L.presheaf.map (homOfLE (X.basicOpen_le g)).op e)
    obtain ⟨⟨m, t⟩, hmt⟩ := IsLocalizedModule.surj (.powers g)
      { toFun := L.presheaf.map (homOfLE (X.basicOpen_le g)).op
        map_add' := map_add _
        map_smul' := map_smul L _ : Γ(L, U) →ₗ[Γ(X, U)] Γ(L, X.basicOpen g) } f
    obtain ⟨c, rfl⟩ := he m
    have ht : algebraMap Γ(X, U) Γ(X, X.basicOpen g) t =
        algebraMap Γ(X, U) Γ(X, X.basicOpen g) c * a := by
      refine hf.smul_left_injective ?_
      dsimp only
      rw [mul_smul, ha]
      rw [LinearMap.map_smul] at hmt
      exact hmt
    obtain ⟨u, hu⟩ := isUnit_of_mul_isUnit_right
      (ht ▸ IsLocalization.map_units Γ(X, X.basicOpen g) t)
    rw [← ha, ← hu]
    exact hf.units_smul u
  let S : Sieve U :=
    { arrows V i := IsFreeGenerator (L.presheaf.map i.op e)
      downward_closed {V W} i hi j := by
        rw [← presheaf_map_map_apply, ← homOfLE_leOfHom j]
        exact hi.map _ }
  refine isFreeGenerator_of_mem e (S := S) (fun x hx ↦ ?_) fun V i hi ↦ hi
  obtain ⟨g, hxg, f, hf⟩ := exists_isFreeGenerator_basicOpen L hU hx
  exact ⟨_, homOfLE (X.basicOpen_le g), hloc hf, hxg⟩

/-- **Invertible modules are trivial on affine opens with trivial Picard group.** If `U` is an
affine open such that the Picard group of `Γ(X, U)` is trivial, then an invertible module `L` has
a free generator on `U`, i.e. `L|_U ≅ 𝒪_U`. -/
theorem exists_isFreeGenerator_of_isAffineOpen (L : X.Modules)
    [SheafOfModules.IsInvertible.{u, u, u} L] {U : X.Opens} (hU : IsAffineOpen U)
    [Subsingleton (CommRing.Pic Γ(X, U))] : ∃ e : Γ(L, U), IsFreeGenerator e := by
  have := invertible_sections_of_isAffineOpen L hU
  obtain ⟨b⟩ := Module.Invertible.free_iff_linearEquiv.1
    (inferInstance : Module.Free Γ(X, U) Γ(L, U))
  refine ⟨b.symm 1, isFreeGenerator_of_surjective_smul L hU _ fun m ↦ ⟨b m, ?_⟩⟩
  dsimp only
  rw [← b.symm.map_smul, smul_eq_mul, mul_one, b.symm_apply_apply]

/-- **Invertible modules are trivial on factorial affine opens.** If `U` is an affine open such
that `Γ(X, U)` is a unique factorization domain, then an invertible module `L` has a free
generator on `U`: the Picard group of a UFD is trivial. -/
theorem exists_isFreeGenerator_of_uniqueFactorizationMonoid (L : X.Modules)
    [SheafOfModules.IsInvertible.{u, u, u} L] {U : X.Opens} (hU : IsAffineOpen U)
    [IsDomain Γ(X, U)] [UniqueFactorizationMonoid Γ(X, U)] :
    ∃ e : Γ(L, U), IsFreeGenerator e :=
  exists_isFreeGenerator_of_isAffineOpen L hU

end AlgebraicGeometry.Scheme.Modules
