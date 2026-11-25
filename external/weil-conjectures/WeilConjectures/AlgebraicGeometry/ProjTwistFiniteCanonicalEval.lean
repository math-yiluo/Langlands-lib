/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
public import Mathlib.Algebra.Module.LocalizedModule.Basic

/-! # Canonical evaluation of twist fractions

The canonical evaluation map from a further localization of `A_f` to the localization at a
homogeneous prime, obtained from the universal property of module localization (Stacks
Project, Section 27.8). -/

@[expose] public section
universe v
open CategoryTheory Opposite LocalizedModule
namespace AlgebraicGeometry.Proj
/-- Canonical evaluation on a further localization.
Source: Stacks Project, Section 27.8, localization maps preceding Tag 01M7;
Mathlib `LocalizedModule.lift`. (blueprint: new-canonical-eval)

Proof: give the prime localization T its B-module structure through the composite
B → A_f → T. The canonical ring map F : A_f → T is B-linear. Every power of g
maps to a unit of T by the hypothesis; its multiplication endomorphism is therefore
also a unit. Apply `LocalizedModule.lift` to this linear map. `lift_comp` gives the
identity on z/1, and linearity of the lift gives the scalar identity. No choice of
an unproved existence witness is used. -/
theorem twist_finiteLocal_canonical_eval
    {A σ : Type v} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
    (𝒜 : ℕ → σ) [GradedRing 𝒜] (f : A) (g : HomogeneousLocalization.Away 𝒜 f)
    (p : basicOpen 𝒜 f)
    (hunit : IsUnit ((IsLocalization.map (M := Submonoid.powers f)
      (T := p.1.asHomogeneousIdeal.toIdeal.primeCompl)
      (Localization.AtPrime p.1.asHomogeneousIdeal.toIdeal) (RingHom.id A)
      (Submonoid.powers_le.mpr p.2))
      (algebraMap (HomogeneousLocalization.Away 𝒜 f) (Localization.Away f) g))) :
    let M := LocalizedModule.Away f A
    letI : Module (HomogeneousLocalization.Away 𝒜 f) M :=
      Module.compHom M (algebraMap _ (Localization.Away f))
    ∃ e : LocalizedModule.Away g M →+
        Localization.AtPrime p.1.asHomogeneousIdeal.toIdeal,
      (∀ z : M, e (LocalizedModule.mkLinearMap (Submonoid.powers g) M z) =
        IsLocalization.map (M := Submonoid.powers f)
          (T := p.1.asHomogeneousIdeal.toIdeal.primeCompl)
          (Localization.AtPrime p.1.asHomogeneousIdeal.toIdeal) (RingHom.id A)
          (Submonoid.powers_le.mpr p.2) z) ∧
      (∀ (a : HomogeneousLocalization.Away 𝒜 f)
        (x : LocalizedModule.Away g M),
        e (a • x) =
          (IsLocalization.map (M := Submonoid.powers f)
            (T := p.1.asHomogeneousIdeal.toIdeal.primeCompl)
            (Localization.AtPrime p.1.asHomogeneousIdeal.toIdeal) (RingHom.id A)
            (Submonoid.powers_le.mpr p.2)
            (algebraMap (HomogeneousLocalization.Away 𝒜 f)
              (Localization.Away f) a)) * e x) := by
  classical
  let B := HomogeneousLocalization.Away 𝒜 f
  let M := LocalizedModule.Away f A
  let T := Localization.AtPrime p.1.asHomogeneousIdeal.toIdeal
  let F : Localization.Away f →+* T :=
    IsLocalization.map (M := Submonoid.powers f)
      (T := p.1.asHomogeneousIdeal.toIdeal.primeCompl) T (RingHom.id A)
      (Submonoid.powers_le.mpr p.2)
  let φ : B →+* T := F.comp (algebraMap B (Localization.Away f))
  let : Module B M := Module.compHom M (algebraMap B (Localization.Away f))
  let : Algebra B T := φ.toAlgebra
  let l : M →ₗ[B] T :=
    { toFun := F
      map_add' := F.map_add
      map_smul' := fun a z => F.map_mul _ _ }
  have hu : ∀ x : Submonoid.powers g,
      IsUnit (algebraMap B (Module.End B T) x) := by
    intro x
    obtain ⟨n, hn⟩ := x.2
    have hx : IsUnit (φ x) := by
      rw [← hn, map_pow]
      exact hunit.pow n
    have heq : algebraMap B (Module.End B T) x =
        (Algebra.lsmul B B T).toRingHom (φ x) := by
      ext y
      rfl
    exact (congrArg IsUnit heq).mpr (hx.map (Algebra.lsmul B B T).toRingHom)
  let e := LocalizedModule.lift (Submonoid.powers g) l hu
  refine ⟨e.toAddMonoidHom, ?_, ?_⟩
  · intro z
    exact LinearMap.congr_fun (LocalizedModule.lift_comp (Submonoid.powers g) l hu) z
  · intro a x
    exact e.map_smul a x

end AlgebraicGeometry.Proj
