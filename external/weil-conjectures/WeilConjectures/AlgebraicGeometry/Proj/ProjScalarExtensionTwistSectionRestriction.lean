/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Proj.ProjScalarExtensionTwistData

/-! Restriction compatibility for normalized scalar-extension twist sections. -/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory Opposite TopologicalSpace
open AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Proj

private theorem section_unit {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : Y.Modules) (U : Y.Opens) (s : Γ(M, U)) :
    ((tensorPullbackSectionAdjunction f).unit.app M).app U s =
      tensorPullbackSection f M U s :=
  (Classical.choose_spec (existsUnique_tensorPullbackSectionAdjunction f)).1 M U s

private theorem tensorPullbackSection_map {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : Y.Modules) {U V : Y.Opens} (h : V ≤ U) (s : Γ(M, U)) :
    tensorPullbackSection f M V (M.presheaf.map (homOfLE h).op s) =
      ((tensorPullback f).obj M).presheaf.map (homOfLE (f.preimage_mono h)).op
        (tensorPullbackSection f M U s) := by
  rw [← section_unit, ← section_unit]
  exact Hom.app_presheaf_map ((tensorPullbackSectionAdjunction f).unit.app M)
    (homOfLE h) s

/-- The normalized scalar-extension section commutes with restriction to a smaller open. -/
theorem scalarExtensionTwistSection_restrict
    {A B : Type u} [CommRing A] [CommRing B]
    {σ τ : Type u} [SetLike σ A] [AddSubgroupClass σ A]
    [SetLike τ B] [AddSubgroupClass τ B]
    {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ]
    (r : Proj ℬ ⟶ Proj 𝒜)
    (θ : ∀ j : ℤ, (tensorPullback r).obj (twist 𝒜 j) ≅ twist ℬ j)
    (j : ℤ) (U V : (Proj 𝒜).Opens) (e : V ≤ U)
    (s : Γ(twist 𝒜 j, U)) (x : r ⁻¹ᵁ V) :
    (scalarExtensionTwistSection r θ j V
      ((twist 𝒜 j).presheaf.map (homOfLE e).op s)).1 x =
      (scalarExtensionTwistSection r θ j U s).1
        ⟨x.1, Scheme.Hom.preimage_mono r e x.2⟩ := by
  unfold scalarExtensionTwistSection
  have hsec := tensorPullbackSection_map r (twist 𝒜 j) e s
  have hnat := Hom.app_presheaf_map (θ j).hom (homOfLE (r.preimage_mono e))
    (tensorPullbackSection r (twist 𝒜 j) U s)
  rw [hsec, hnat]
  rfl

end AlgebraicGeometry.Proj
