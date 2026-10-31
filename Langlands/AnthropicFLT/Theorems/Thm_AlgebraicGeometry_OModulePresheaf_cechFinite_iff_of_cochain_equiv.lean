/-
Ported from `Theorems/Thm_AlgebraicGeometry_OModulePresheaf_cechFinite_iff_of_cochain_equiv.lean` of the Anthropic Lean formalization of Fermat's Last Theorem
(commit 6e837e75355538c7f80bab5b956861e86c4eacc2), Copyright 2026 Anthropic, PBC, licensed under the Apache
License, Version 2.0; see `licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`.
The paired Markdown file lists the changes made by the port.
-/
import Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Mathlib.RingTheory.Finiteness.Basic
import Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_cechFinite_iff_of_cochain_equiv
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false


universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.OModulePresheaf.cechFinite_iff_of_cochain_equiv
    {R : Type u} [CommRing R] {V V' : Scheme.{u}} {π : V ⟶ Spec (.of R)} {π' : V' ⟶ Spec (.of R)}
    (F : OModulePresheaf π) (G : OModulePresheaf π') (K : V.OrderedAffineCover) (K' : V'.OrderedAffineCover)
    (e : ∀ q, F.cochain K q ≃ₗ[R] G.cochain K' q) (he : ∀ q x, e (q + 1) (F.d K q x) = G.d K' q (e q x)) :
    F.CechFinite K ↔ G.CechFinite K' := by exact @_root_.P2MW.S_AlgebraicGeometry_OModulePresheaf_cechFinite_iff_of_cochain_equiv.solution R _ V V' π π' F G K K' e he
