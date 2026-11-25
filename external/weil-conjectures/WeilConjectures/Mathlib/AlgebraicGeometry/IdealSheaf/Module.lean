/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf

/-!
# The ideal sheaf of a `Scheme.IdealSheafData` as a sheaf of modules

Mathlib's `AlgebraicGeometry.Scheme.IdealSheafData` is deliberately *not* a subsheaf of
`𝒪_X`: it records an ideal `I(U) ≤ Γ(X, U)` for every **affine** open `U`, together with the
compatibility `I(D(f)) = I(U)_f`, and nothing else. That is enough to determine an ideal
sheaf, and the file that introduces it says explicitly that turning it into an actual
subsheaf is left for later. Nothing in Mathlib does so: `Mathlib/AlgebraicGeometry/Modules/`
never mentions `IdealSheafData`, and conversely the `IdealSheaf/` directory never mentions
`SheafOfModules`.

This file supplies the missing bridge. The construction goes through the closed subscheme
rather than through the sections: `J.subschemeι : V(J) ⟶ X` is a closed immersion with
`𝒪_{V(J)} = 𝒪_X/J`, so the ideal sheaf is the kernel of `𝒪_X ⟶ (ι_J)_* 𝒪_{V(J)}` in the
abelian category `X.Modules`. This costs nothing: `Scheme.IdealSheafData.subscheme` and
`ker_subschemeι_app` are already in Mathlib, and `X.Modules` is already abelian.

The alternative — extending `J.ideal` to all opens by
`⨅ V affine, V ≤ U, (J.ideal V).comap (res)`, packaging it as a
`PresheafOfModules.Submodule` and then proving the sheaf condition by hand — needs a genuine
sheaf-condition argument that the kernel description gets for free.

## Main definitions

- `AlgebraicGeometry.Scheme.IdealSheafData.toModules` — the ideal sheaf as an `𝒪_X`-module.
- `AlgebraicGeometry.Scheme.IdealSheafData.toModulesι` — its inclusion into `𝒪_X`.
- `AlgebraicGeometry.Scheme.IdealSheafData.idealOfOpens` — the ideal cut out on an arbitrary
  open subset, extending `J.ideal` off the affine opens.

## Main results

- `AlgebraicGeometry.Scheme.IdealSheafData.range_toModulesι_app` — over an affine open `U`,
  the sections of `J.toModules` are exactly `J.ideal U`, which is what makes the definition
  the right one.
- `AlgebraicGeometry.Scheme.IdealSheafData.injective_toModulesι_app` — the inclusion is
  injective on sections over every open, affine or not.

## TODO

Local freeness of rank one for an invertible ideal sheaf. What is missing is a criterion for
a morphism in `X.Modules` to be an isomorphism that can be checked on a basis of opens or on
stalks: `Scheme.Modules.Hom.isIso_iff_isIso_app` quantifies over *all* opens, which is not
usable directly, and Mathlib has no stalkwise criterion phrased for `X.Modules` (only
`Scheme.Modules.restrictStalkNatIso`). Note also that Mathlib's
`SheafOfModules.IsLocallyFree` carries no rank information, so "rank one" has to be spelled
out separately.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X : Scheme.{u}} (J : X.IdealSheafData)

/-- The comparison morphism `𝒪_X ⟶ (ι_J)_* 𝒪_{V(J)}` of `𝒪_X`-modules attached to the closed
immersion `J.subschemeι` of the closed subscheme cut out by `J`. Its kernel is the ideal
sheaf; see `AlgebraicGeometry.Scheme.IdealSheafData.toModules`. -/
noncomputable def toPushforwardSubscheme :
    SheafOfModules.unit X.ringCatSheaf ⟶
      (SheafOfModules.pushforward J.subschemeι.toRingCatSheafHom).obj
        (SheafOfModules.unit J.subscheme.ringCatSheaf) :=
  SheafOfModules.unitToPushforwardObjUnit _

@[simp]
lemma map_toPushforwardSubscheme (U : X.Opens)
    (x : Γ((SheafOfModules.unit X.ringCatSheaf : X.Modules), U)) :
    (SheafOfModules.evaluation X.ringCatSheaf (op U)).map J.toPushforwardSubscheme x =
      J.subschemeι.app U x :=
  rfl

/-- **The ideal sheaf attached to a `Scheme.IdealSheafData`**, as a sheaf of `𝒪_X`-modules:
the kernel of `𝒪_X ⟶ (ι_J)_* 𝒪_{V(J)}`.

Over an affine open `U` its sections are `J.ideal U`
(`AlgebraicGeometry.Scheme.IdealSheafData.range_toModulesι_app`). -/
noncomputable def toModules : X.Modules := kernel J.toPushforwardSubscheme

/-- The inclusion of the ideal sheaf into the structure sheaf. -/
noncomputable def toModulesι :
    J.toModules ⟶ (SheafOfModules.unit X.ringCatSheaf : X.Modules) :=
  kernel.ι _

lemma map_kernelι_eq_toModulesι_app (U : X.Opens) (x : Γ(J.toModules, U)) :
    (SheafOfModules.evaluation X.ringCatSheaf (op U)).map (kernel.ι J.toPushforwardSubscheme) x =
      J.toModulesι.app U x :=
  rfl


/-- The ideal cut out by `J` on an **arbitrary** open subset, not just an affine one: the
kernel of the restriction map to the closed subscheme.

`Scheme.IdealSheafData` itself only records ideals on affine opens, so this is the extension
of `J.ideal` to all of `X.Opens`, and `idealOfOpens_eq_ideal` says the extension is
compatible. -/
noncomputable def idealOfOpens (U : X.Opens) : Ideal Γ(X, U) :=
  RingHom.ker (J.subschemeι.app U).hom

@[simp]
lemma idealOfOpens_eq_ideal (U : X.affineOpens) : J.idealOfOpens U.1 = J.ideal U :=
  J.ker_subschemeι_app U

lemma mem_idealOfOpens_iff {U : X.Opens} {x : Γ(X, U)} :
    x ∈ J.idealOfOpens U ↔ J.subschemeι.app U x = 0 :=
  RingHom.mem_ker

/-- Over any open subset, the sections of the ideal sheaf are exactly the sections of `𝒪_X`
killed by the restriction to the closed subscheme cut out by `J`. -/
lemma range_toModulesι_app_eq (U : X.Opens) :
    Set.range (J.toModulesι.app U) = { x | J.subschemeι.app U x = 0 } :=
  Scheme.Modules.range_map_kernelι U J.toPushforwardSubscheme

lemma range_toModulesι_app_eq_idealOfOpens (U : X.Opens) :
    Set.range (J.toModulesι.app U) = (J.idealOfOpens U : Set Γ(X, U)) :=
  J.range_toModulesι_app_eq U

/-- **Over an affine open the sections of the ideal sheaf are the given ideal.** This is what
identifies `J.toModules` with the ideal sheaf that `J` is intended to describe: `J` only
records `J.ideal U` for affine `U`, and that is exactly what `J.toModules` gives back. -/
lemma range_toModulesι_app (U : X.affineOpens) :
    Set.range (J.toModulesι.app U.1) = (J.ideal U : Set Γ(X, U.1)) := by
  rw [range_toModulesι_app_eq_idealOfOpens, idealOfOpens_eq_ideal]

instance : Mono J.toModulesι := by
  unfold toModulesι
  infer_instance

/-- The ideal sheaf really is a subsheaf of `𝒪_X`: the inclusion is injective on sections
over every open subset, not merely a categorical monomorphism. -/
lemma injective_toModulesι_app (U : X.Opens) : Function.Injective (J.toModulesι.app U) :=
  Scheme.Modules.injective_map_kernelι U J.toPushforwardSubscheme


/-- If the global sections are mapped injectively to the closed subscheme cut out by `J`, then
`J` has no nonzero global sections. -/
lemma subsingleton_sections_toModules_of_injective
    (h : Function.Injective (J.subschemeι.app ⊤)) : Subsingleton Γ(J.toModules, ⊤) := by
  refine ⟨fun a b ↦ J.injective_toModulesι_app ⊤ ?_⟩
  have ha : J.subschemeι.app ⊤ (J.toModulesι.app ⊤ a) = 0 :=
    (J.range_toModulesι_app_eq ⊤).subset ⟨a, rfl⟩
  have hb : J.subschemeι.app ⊤ (J.toModulesι.app ⊤ b) = 0 :=
    (J.range_toModulesι_app_eq ⊤).subset ⟨b, rfl⟩
  exact h (ha.trans hb.symm)

/-- If `Γ(X, 𝒪_X)` is a field (for instance if `X` is proper and geometrically integral over a
field), and the closed subscheme cut out by `J` is nonempty, then `J` has no nonzero global
sections. -/
lemma subsingleton_sections_toModules_of_isField (hX : IsField Γ(X, ⊤)) [Nonempty J.subscheme] :
    Subsingleton Γ(J.toModules, ⊤) := by
  let := hX.toField
  have : Nonempty ↥(J.subschemeι ⁻¹ᵁ ⊤) := ⟨⟨Classical.arbitrary J.subscheme, trivial⟩⟩
  exact J.subsingleton_sections_toModules_of_injective (J.subschemeι.app ⊤).hom.injective
end AlgebraicGeometry.Scheme.IdealSheafData
