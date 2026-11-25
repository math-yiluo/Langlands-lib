/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import WeilConjectures.AlgebraicGeometry.Sites.EtaleTopologicalInvariance.GlobalSections
public import WeilConjectures.Mathlib.AlgebraicGeometry.Scheme
public import WeilConjectures.Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
public import WeilConjectures.Mathlib.RingTheory.TensorProduct.Maps

/-!
# Complete connected schemes with a rational point are geometrically connected

A connected scheme over a field `k` with a `k`-rational point is geometrically connected
(Stacks 04KV). We prove this for universally closed quasi-separated `k`-schemes `X`, such as
proper ones, by computing global sections: `Γ(X)` is integral over `k`, so connectedness and the
rational point make it a local ring with nil maximal ideal and residue field `k`; by flat base
change `Γ(X_L) = Γ(X) ⊗_k L` for every field `L ⊇ k`, which therefore has no idempotents other
than `0` and `1`.

## Main statements

- `AlgebraicGeometry.GeometricallyConnected.of_universallyClosed_of_section`: a connected
  universally closed quasi-separated scheme over a field with a rational point is geometrically
  connected.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

/-- A connected universally closed quasi-separated scheme `X` (e.g. a connected proper scheme)
over a field `k` with a `k`-rational point, that is, a section `s` of its structure morphism
`f`, is geometrically connected over `k` (the proper case of Stacks 04KV).

For a field `L` over `k`, the global sections of `X_L` are `Γ(X) ⊗_k L` (flat base change).
Since `Γ(X)` is integral over `k` (`isIntegral_appTop_of_universallyClosed`) and has no
nontrivial idempotents, the kernel of the evaluation `Γ(X) → k` at the rational point is nil
(`RingHom.IsIntegral.isNilpotent_of_eq_zero`), hence `Γ(X) ⊗_k L` has no nontrivial idempotents
(`Algebra.TensorProduct.eq_zero_or_eq_one_of_isIdempotentElem`), and `X_L` is connected.

This is the step "a connected group scheme is geometrically connected" in the proof of blueprint
`lemma-abelian-variety-commutative--1`. -/
@[stacks 04KV "The universally closed case."]
theorem GeometricallyConnected.of_universallyClosed_of_section {k : Type u} [Field k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [UniversallyClosed f] [QuasiSeparated f]
    [ConnectedSpace X] (s : Spec (.of k) ⟶ X) (hs : s ≫ f = 𝟙 _) : GeometricallyConnected f where
  geometrically_connectedSpace L _ y Z fst snd h := by
    have : CompactSpace X := (quasiCompact_iff_compactSpace f).mp inferInstance
    have : QuasiSeparatedSpace X := (quasiSeparated_iff_quasiSeparatedSpace f).mp inferInstance
    have : Flat y := by
      rw [← Spec.map_preimage y, Flat.SpecMap_iff]
      algebraize [(Spec.preimage y).hom]
      exact (inferInstance : Module.Flat k L)
    suffices ConnectedSpace ↥(pullback f y) from
      (Scheme.homeoOfIso h.isoPullback).symm.surjective.connectedSpace
        (Scheme.homeoOfIso h.isoPullback).symm.continuous
    have : Nonempty ↥(pullback f y) :=
      ⟨pullback.lift (y ≫ s) (𝟙 _) (by simp [hs]) (Nonempty.some inferInstance)⟩
    rw [Scheme.connectedSpace_iff_isIdempotentElem]
    let : Algebra Γ(Spec (.of k), ⊤) Γ(X, ⊤) := f.appTop.hom.toAlgebra
    let : Algebra Γ(Spec (.of k), ⊤) Γ(Spec (.of L), ⊤) := y.appTop.hom.toAlgebra
    have hsf (r : Γ(Spec (.of k), ⊤)) : s.appTop (f.appTop r) = r := by
      rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, hs]
      rfl
    let φ : Γ(X, ⊤) →ₐ[Γ(Spec (.of k), ⊤)] Γ(Spec (.of k), ⊤) :=
      { s.appTop.hom with commutes' := hsf }
    have hX := (Scheme.connectedSpace_iff_isIdempotentElem X).mp inferInstance
    have hL := (Scheme.connectedSpace_iff_isIdempotentElem (Spec (.of L))).mp inferInstance
    have hnil (a : Γ(X, ⊤)) (ha : φ a = 0) : IsNilpotent a := by
      let e := Scheme.ΓSpecIso (.of k)
      refine RingHom.IsIntegral.isNilpotent_of_eq_zero (g := (e.inv ≫ f.appTop).hom)
        ?_ (s.appTop ≫ e.hom).hom ?_ hX (a := a) ?_
      · exact RingHom.IsIntegral.trans _ _ (RingHom.isIntegral_of_surjective _
          e.commRingCatIsoToRingEquiv.symm.surjective) (isIntegral_appTop_of_universallyClosed f)
      · ext r
        simp [hsf]
      · simp only [CommRingCat.hom_comp, RingHom.comp_apply]
        change e.hom (φ a) = 0
        rw [ha, map_zero]
    let ε := (isPushout_appTop_of_flat y f).flip.tensorEquiv rfl rfl
    intro t ht
    simpa using Algebra.TensorProduct.eq_zero_or_eq_one_of_isIdempotentElem φ hnil hL
      (ht.map ε.symm)

end AlgebraicGeometry
