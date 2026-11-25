/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Fiber
import WeilConjectures.AlgebraicGeometry.ProperFibreIdempotentImage
import WeilConjectures.AlgebraicGeometry.SchemeClopenIdempotent
import WeilConjectures.AlgebraicGeometry.SteinUniversallyClosedFactor

/-!
# Connected fibres of a normalized proper morphism to an affine scheme

Source: Stacks Project, More on Morphisms, Theorem 37.53.5 (Tag 03H2), normalized
 affine reduction (blueprint: lem-weil-pbc-stein-normalized-fibre-idempotent).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- Source: Stacks Project, Theorem 37.53.5 (Tag 03H2), normalized affine reduction.
(blueprint: lem-weil-pbc-stein-normalized-fibre-idempotent)
If the canonical map from the base ring to global sections is an isomorphism, every fibre
of a proper morphism is nonempty and connected; `ConnectedSpace` includes nonemptiness.

Proof: The Stein factorization theorem
`lem-weil-pbc-stein-universally-closed-factor` makes `X.toSpecΓ` surjective and its sharp
map an isomorphism. The hypothesis makes `f.steinFactorizationBase` an isomorphism, so
`f` is surjective and every section map `f.app U` is an isomorphism. Surjectivity gives
nonempty fibres. For a clopen subset of a fibre, take its characteristic idempotent using
`lem-weil-pbc-scheme-clopen-idempotent`. Lift this idempotent to a section over the inverse
image of a neighbourhood using `lem-weil-pbc-stein-fibre-idempotent-image`, then use the
inverse of `f.app U` to obtain a section on the base. The fibre square shows its restriction
to the fibre is pulled back from a global section of the spectrum of the residue field.
Such a section is zero or a unit; its idempotent image is therefore zero or one. The
characteristic locus is consequently empty or the whole fibre, proving connectedness. -/
theorem Scheme.Hom.connectedSpace_fiber_of_isProper_of_globalSections_iso
    {R : Type u} [CommRing R] {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) [IsProper f]
    [IsIso ((Scheme.ΓSpecIso (.of R)).inv ≫ f.appTop)] (s : Spec (.of R)) :
    ConnectedSpace (f.fiber s) := by
  classical
  have hstein := stein_universally_closed_factor f
  have : Surjective X.toSpecΓ := hstein.2.2.2.1
  have : IsIso X.toSpecΓ.c := hstein.2.2.2.2.2.1
  have : IsIso f.steinFactorizationBase := by
    unfold Scheme.Hom.steinFactorizationBase
    infer_instance
  have : Surjective f := by
    rw [← Scheme.toSpecΓ_steinFactorizationBase f]
    infer_instance
  have happ (U : (Spec (.of R)).Opens) : IsIso (f.app U) := by
    rw [← Scheme.toSpecΓ_steinFactorizationBase f, Scheme.Hom.comp_app]
    have : IsIso (X.toSpecΓ.app (f.steinFactorizationBase ⁻¹ᵁ U)) :=
      NatIso.isIso_app_of_isIso _ _
    infer_instance
  have hnonempty : Nonempty (f.fiber s) := by
    obtain ⟨x, hx⟩ := f.surjective s
    exact ⟨(f.fiberHomeo s).symm ⟨x, hx⟩⟩
  refine connectedSpace_iff_clopen.mpr ⟨hnonempty, ?_⟩
  intro V hV
  obtain ⟨e, he, hVe⟩ := (scheme_clopen_idempotent (f.fiber s)).2.1.2 V
    ⟨hV.isOpen, hV.isClosed⟩
  obtain ⟨U, hsU, h, t, ht⟩ := f.exists_section_restricting_to_fiber_idempotent s e he
  have : IsIso (f.app U) := happ U
  let a : Γ(Spec (.of R), U) := inv (f.app U) t
  have hat : f.app U a = t := by
    change (f.app U) (inv (f.app U) t) = t
    rw [← CommRingCat.comp_apply, IsIso.inv_hom_id]
    rfl
  let k := (Spec (.of R)).fromSpecResidueField s
  let g := f.fiberToSpecResidueField s
  have hU : (⊤ : (Spec ((Spec (.of R)).residueField s)).Opens) ≤ k ⁻¹ᵁ U := by
    intro x _
    change k x ∈ U
    simpa [k, Scheme.fromSpecResidueField_apply] using hsU
  let b := k.appLE U ⊤ hU a
  have hmaps : f.app U ≫ (f.fiberι s).appLE (f ⁻¹ᵁ U) ⊤ h =
      k.appLE U ⊤ hU ≫ g.appTop := by
    change f.app U ≫ (f.fiberι s).appLE (f ⁻¹ᵁ U) ⊤ h =
      k.appLE U ⊤ hU ≫ g.app ⊤
    rw [g.app_eq_appLE, Scheme.Hom.appLE_comp_appLE, ← Scheme.Hom.comp_appLE]
    simp only [g, k, Scheme.Hom.fiber_fac]
    rfl
  have hbe : g.appTop b = e := by
    rw [← ht, ← hat]
    exact congrArg (fun φ : Γ(Spec (.of R), U) ⟶ Γ(f.fiber s, ⊤) ↦ φ a) hmaps.symm
  have hb : b = 0 ∨ IsUnit b := by
    let K := (Spec (.of R)).residueField s
    let c : K := (Scheme.ΓSpecIso K).hom b
    have hbc : (Scheme.ΓSpecIso K).inv c = b := by
      change (Scheme.ΓSpecIso K).inv ((Scheme.ΓSpecIso K).hom b) = b
      rw [← CommRingCat.comp_apply, Iso.hom_inv_id]
      rfl
    by_cases hc : c = 0
    · left
      rw [← hbc, hc, map_zero]
    · right
      rw [← hbc]
      exact (isUnit_iff_ne_zero.mpr hc).map (Scheme.ΓSpecIso K).inv.hom
  have he01 : e = 0 ∨ e = 1 := by
    rcases hb with hb | hb
    · left
      rw [← hbe, hb, map_zero]
    · right
      exact (IsIdempotentElem.iff_eq_one_of_isUnit
        (hbe ▸ hb.map g.appTop.hom)).mp he
  rcases he01 with h0 | h1
  · left
    rw [← hVe, h0]
    ext x
    simp [idempotentOpen]
  · right
    rw [← hVe, h1]
    ext x
    simp [idempotentOpen]


end AlgebraicGeometry
