import Mathlib.Analysis.Complex.Basic
import Mathlib.RepresentationTheory.Irreducible
import Mathlib.RingTheory.SimpleModule.Isotypic

/-!
# Irreducible representations inside an isotypic representation

Let `ρA` be an irreducible representation of a monoid `G` over `ℂ`, and let `σ` be
`ρA`-isotypic: the ranges of the intertwining maps from `ρA` to `σ` span the carrier of `σ`.
This module proves that an irreducible representation `ρW` with a nonzero intertwining map
into `σ` is isomorphic to `ρA` (it has a nonzero, hence surjective, intertwining map to
`ρA`), so that `σ` is also `ρW`-isotypic.

* `range_toLinearMap_eq_map_range`: the range of an intertwining map is the range of the
  corresponding `ℂ[G]`-linear map.
* `exists_ne_zero_of_iSup_range_eq_top`: a nonzero isotypic representation receives a nonzero
  intertwining map.
* `exists_intertwiningMap_ne_zero_of_isotypic`: the nonzero intertwining map from `ρW` to `ρA`.
* `iSup_range_eq_top_of_isotypic`: `σ` is `ρW`-isotypic.
* `isotypic_iff_exists_ne_zero`: for nonzero `σ`, it is `ρW`-isotypic exactly when some
  intertwining map from `ρW` to `σ` is nonzero.

The proof passes to modules over the monoid algebra `ℂ[G]` (`Representation.asModule`) and
uses Mathlib's `Submodule.linearEquiv_of_sSup_eq_top`: a simple submodule of a sum of simple
submodules is isomorphic to one of them.
-/

noncomputable section

set_option autoImplicit false

namespace Langlands.IsotypicEmbedding

open scoped MonoidAlgebra
open Representation

universe uG uA uW uQ

variable {G : Type uG} [Monoid G]
  {A : Type uA} [AddCommGroup A] [Module ℂ A]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]
  {Q : Type uQ} [AddCommGroup Q] [Module ℂ Q]

/-- The range of an intertwining map is the range of the corresponding `ℂ[G]`-linear map. -/
theorem range_toLinearMap_eq_map_range (ρ : Representation ℂ G W) (σ : Representation ℂ G Q)
    (f : ρ.IntertwiningMap σ) :
    LinearMap.range f.toLinearMap =
      ((LinearMap.range (IntertwiningMap.equivLinearMapAsModule ρ σ f)).restrictScalars ℂ).map
        σ.asModuleEquiv.toLinearMap := by
  ext w
  constructor
  · rintro ⟨v, rfl⟩
    exact ⟨_, ⟨ρ.asModuleEquiv.symm v, rfl⟩, rfl⟩
  · rintro ⟨v, ⟨u, rfl⟩, rfl⟩
    exact ⟨ρ.asModuleEquiv u, rfl⟩

/-- A nonzero representation spanned by the ranges of the intertwining maps from `ρ` receives
a nonzero intertwining map from `ρ`. -/
theorem exists_ne_zero_of_iSup_range_eq_top [Nontrivial Q] (ρ : Representation ℂ G W)
    (σ : Representation ℂ G Q)
    (h : ⨆ f : ρ.IntertwiningMap σ, LinearMap.range f.toLinearMap = ⊤) :
    ∃ f : ρ.IntertwiningMap σ, f ≠ 0 := by
  by_contra hne
  simp only [not_exists, not_not] at hne
  have hbot : (⨆ f : ρ.IntertwiningMap σ, LinearMap.range f.toLinearMap) = ⊥ := by
    refine iSup_eq_bot.mpr fun f => ?_
    rw [hne f, IntertwiningMap.zero_toLinearMap, LinearMap.range_zero]
  exact bot_ne_top (hbot.symm.trans h)

/-- A nonzero intertwining map from an irreducible representation is injective, read on the
group-algebra modules. -/
theorem injective_equivLinearMapAsModule (ρ : Representation ℂ G W) [ρ.IsIrreducible]
    (σ : Representation ℂ G Q) (f : ρ.IntertwiningMap σ) (hf : f ≠ 0) :
    Function.Injective (IntertwiningMap.equivLinearMapAsModule ρ σ f) := by
  refine ((IntertwiningMap.equivLinearMapAsModule ρ σ f).injective_or_eq_zero).resolve_right ?_
  intro h
  exact hf ((LinearEquiv.map_eq_zero_iff (IntertwiningMap.equivLinearMapAsModule ρ σ)).mp h)

/-- **An irreducible constituent of an isotypic representation is the isotypic type.** If
`σ` is `ρA`-isotypic for an irreducible `ρA`, an irreducible `ρW` with a nonzero intertwining
map to `σ` has a nonzero intertwining map to `ρA`. -/
theorem exists_intertwiningMap_ne_zero_of_isotypic (ρA : Representation ℂ G A)
    (ρW : Representation ℂ G W) (σ : Representation ℂ G Q) [ρA.IsIrreducible] [ρW.IsIrreducible]
    (hiso : ⨆ g : ρA.IntertwiningMap σ, LinearMap.range g.toLinearMap = ⊤)
    (f : ρW.IntertwiningMap σ) (hf : f ≠ 0) :
    ∃ e : ρW.IntertwiningMap ρA, e ≠ 0 := by
  classical
  let F := IntertwiningMap.equivLinearMapAsModule ρW σ f
  have hFinj : Function.Injective F := injective_equivLinearMapAsModule ρW σ f hf
  let N : Submodule ℂ[G] σ.asModule := LinearMap.range F
  have : IsSimpleModule ℂ[G] N := IsSimpleModule.congr (LinearEquiv.ofInjective F hFinj).symm
  let s : Set (Submodule ℂ[G] σ.asModule) :=
    {m | ∃ g : ρA.IntertwiningMap σ, g ≠ 0 ∧
      m = LinearMap.range (IntertwiningMap.equivLinearMapAsModule ρA σ g)}
  have hsimple : ∀ m : s, IsSimpleModule ℂ[G] m := by
    rintro ⟨m, g, hg, rfl⟩
    exact IsSimpleModule.congr
      (LinearEquiv.ofInjective _ (injective_equivLinearMapAsModule ρA σ g hg)).symm
  have hs : sSup s = ⊤ := by
    have hle : (⨆ g : ρA.IntertwiningMap σ, LinearMap.range g.toLinearMap) ≤
        ((sSup s).restrictScalars ℂ).map σ.asModuleEquiv.toLinearMap := by
      refine iSup_le fun g => ?_
      by_cases hg : g = 0
      · rw [hg, IntertwiningMap.zero_toLinearMap, LinearMap.range_zero]
        exact bot_le
      · rw [range_toLinearMap_eq_map_range]
        exact Submodule.map_mono (Submodule.restrictScalars_mono ℂ (le_sSup ⟨g, hg, rfl⟩))
    rw [eq_top_iff]
    intro y _
    have hy : σ.asModuleEquiv y ∈
        ((sSup s).restrictScalars ℂ).map σ.asModuleEquiv.toLinearMap :=
      hle (hiso ▸ Submodule.mem_top)
    obtain ⟨z, hz, hzy⟩ := hy
    have hzy' : z = y := σ.asModuleEquiv.injective hzy
    exact hzy' ▸ hz
  obtain ⟨m, ⟨g, hg, rfl⟩, ⟨φ⟩⟩ := N.linearEquiv_of_sSup_eq_top s hs
  let eL : ρW.asModule ≃ₗ[ℂ[G]] ρA.asModule :=
    (LinearEquiv.ofInjective F hFinj).trans
      (φ.trans (LinearEquiv.ofInjective _ (injective_equivLinearMapAsModule ρA σ g hg)).symm)
  refine ⟨(IntertwiningMap.equivLinearMapAsModule ρW ρA).symm eL.toLinearMap, ?_⟩
  intro h0
  have h0' : eL.toLinearMap = 0 := by
    have := congrArg (IntertwiningMap.equivLinearMapAsModule ρW ρA) h0
    rwa [LinearEquiv.apply_symm_apply, map_zero] at this
  have : Nontrivial ρW.asModule := IsSimpleModule.nontrivial ℂ[G] ρW.asModule
  obtain ⟨x, hx⟩ := exists_ne (0 : ρW.asModule)
  apply hx
  apply eL.injective
  rw [map_zero]
  exact LinearMap.congr_fun h0' x

/-- **Isotypy transfers to an embedded irreducible representation.** If `σ` is
`ρA`-isotypic for an irreducible `ρA`, and an irreducible `ρW` has a nonzero intertwining map
to `σ`, then `σ` is `ρW`-isotypic. -/
theorem iSup_range_eq_top_of_isotypic (ρA : Representation ℂ G A)
    (ρW : Representation ℂ G W) (σ : Representation ℂ G Q) [ρA.IsIrreducible] [ρW.IsIrreducible]
    (hiso : ⨆ g : ρA.IntertwiningMap σ, LinearMap.range g.toLinearMap = ⊤)
    (f : ρW.IntertwiningMap σ) (hf : f ≠ 0) :
    ⨆ h : ρW.IntertwiningMap σ, LinearMap.range h.toLinearMap = ⊤ := by
  obtain ⟨e, he⟩ := exists_intertwiningMap_ne_zero_of_isotypic ρA ρW σ hiso f hf
  have hsurj : Function.Surjective e := (IsIrreducible.surjective_or_eq_zero e).resolve_right he
  rw [eq_top_iff, ← hiso]
  refine iSup_le fun g => ?_
  have hrange : LinearMap.range (g.comp e).toLinearMap = LinearMap.range g.toLinearMap := by
    rw [IntertwiningMap.comp_toLinearMap, LinearMap.range_comp_of_range_eq_top]
    exact LinearMap.range_eq_top.mpr hsurj
  rw [← hrange]
  exact le_iSup (fun h : ρW.IntertwiningMap σ => LinearMap.range h.toLinearMap) (g.comp e)

/-- **Isotypic types of an isotypic representation.** Let `σ` be nonzero and `ρA`-isotypic for
an irreducible `ρA`. An irreducible `ρW` makes `σ` `ρW`-isotypic exactly when some
intertwining map from `ρW` to `σ` is nonzero. -/
theorem isotypic_iff_exists_ne_zero [Nontrivial Q] (ρA : Representation ℂ G A)
    (ρW : Representation ℂ G W) (σ : Representation ℂ G Q) [ρA.IsIrreducible] [ρW.IsIrreducible]
    (hiso : ⨆ g : ρA.IntertwiningMap σ, LinearMap.range g.toLinearMap = ⊤) :
    (⨆ h : ρW.IntertwiningMap σ, LinearMap.range h.toLinearMap = ⊤) ↔
      ∃ f : ρW.IntertwiningMap σ, f ≠ 0 :=
  ⟨exists_ne_zero_of_iSup_range_eq_top ρW σ,
    fun ⟨f, hf⟩ => iSup_range_eq_top_of_isotypic ρA ρW σ hiso f hf⟩

end Langlands.IsotypicEmbedding
