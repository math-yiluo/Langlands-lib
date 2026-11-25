/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Cohomology.Defs
import WeilConjectures.AlgebraicGeometry.Cohomology.LongExact
public import Mathlib.RingTheory.Noetherian.Basic

/-! # Finiteness of cohomology under extensions

Source: Stacks Project, Tag 02O5.
(blueprint: lem-pc-e2-cohomology-finite-extension)
 -/

@[expose] public section

universe u v

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.Modules

/-- Finiteness in a fixed degree is preserved under a short exact extension, with
scalars restricted from global functions to a Noetherian ring.
Source: Stacks Project, Cohomology of Schemes, proof of Proposition 30.19.1, Tag 02O5:
the long exact sequence and closure of finite modules under submodules and extensions.
(blueprint: lem-pc-e2-cohomology-finite-extension) -/
theorem finite_H_of_shortExact_extension {X : Scheme.{u}} (R : Type v) [CommRing R]
    [IsNoetherianRing R] (σ : R →+* Γ(X, ⊤))
    (S : ShortComplex X.Modules) (hS : S.ShortExact) (q : ℕ) :
    letI : Module R (S.X₁.H q) := Module.compHom _ σ
    letI : Module R (S.X₂.H q) := Module.compHom _ σ
    letI : Module R (S.X₃.H q) := Module.compHom _ σ
    Module.Finite R (S.X₁.H q) → Module.Finite R (S.X₃.H q) →
      Module.Finite R (S.X₂.H q) := by
  let : Module R (S.X₁.H q) := Module.compHom _ σ
  let : Module R (S.X₂.H q) := Module.compHom _ σ
  let : Module R (S.X₃.H q) := Module.compHom _ σ
  intro h₁ h₃
  let a : S.X₁.H q →ₗ[R] S.X₂.H q :=
    { H.map S.f q with map_smul' := fun r x ↦ H.map_smul S.f q (σ r) x }
  let b : S.X₂.H q →ₗ[R] S.X₃.H q :=
    { H.map S.g q with map_smul' := fun r x ↦ H.map_smul S.g q (σ r) x }
  have hab : LinearMap.ker b = LinearMap.range a := by
    ext x
    exact SetLike.ext_iff.mp (H.ker_map_g_eq_range_map_f hS q) x
  refine ⟨(⊤ : Submodule R (S.X₂.H q)).fg_of_fg_map_of_fg_inf_ker b ?_ ?_⟩
  · exact IsNoetherian.noetherian _
  · rw [top_inf_eq, hab]
    exact Submodule.fg_range a

end AlgebraicGeometry.Scheme.Modules
