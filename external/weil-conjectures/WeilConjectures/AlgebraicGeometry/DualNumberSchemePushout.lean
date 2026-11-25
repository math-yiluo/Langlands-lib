/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.DualNumber
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.AlgebraicGeometry.Stalk

/-!
# The finite pushout of dual-number schemes

Source: Stacks Project, Tag 0B2B, proof of Lemma 33.16.2, with the same local-ring
argument for any positive finite number of copies
(blueprint: lem-sc-dual-number-scheme-pushout).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

private theorem squareZeroLocal (K M : Type u) [Field K] [AddCommGroup M]
    [Module K M] [Module Kᵐᵒᵖ M] [IsCentralScalar K M] : IsLocalRing (TrivSqZeroExt K M) := by
  apply IsLocalRing.of_isUnit_or_isUnit_one_sub_self
  intro a
  simp only [TrivSqZeroExt.isUnit_iff_isUnit_fst, TrivSqZeroExt.fst_sub,
    TrivSqZeroExt.fst_one]
  exact IsLocalRing.isUnit_or_isUnit_one_sub_self a.fst

private theorem squareZeroFstLocal (K M : Type u) [Field K] [AddCommGroup M]
    [Module K M] [Module Kᵐᵒᵖ M] [IsCentralScalar K M] :
    IsLocalHom (TrivSqZeroExt.fstHom K K M).toRingHom :=
  ⟨fun _a h ↦ TrivSqZeroExt.isUnit_iff_isUnit_fst.mpr h⟩

private theorem squareZeroProjLocal (K : Type u) [Field K] (n : ℕ) (i : Fin n) :
    IsLocalHom
      (TrivSqZeroExt.map (LinearMap.proj i : (Fin n → K) →ₗ[K] K)).toRingHom := by
  refine ⟨fun a h ↦ ?_⟩
  apply TrivSqZeroExt.isUnit_iff_isUnit_fst.mpr
  simpa using TrivSqZeroExt.isUnit_iff_isUnit_fst.mp h

set_option backward.isDefEq.respectTransparency.types false in
private lemma localSpec_injective (X : Scheme.{u}) (R : CommRingCat.{u}) [IsLocalRing R]
    (x : X) (f g : X.presheaf.stalk x ⟶ R) [IsLocalHom f.hom] [IsLocalHom g.hom]
    (h : Spec.map f ≫ X.fromSpecStalk x = Spec.map g ≫ X.fromSpecStalk x) : f = g := by
  have hh : (⟨x, f, inferInstance⟩ :
      Σ y, { k : X.presheaf.stalk y ⟶ R // IsLocalHom k.hom }) =
      ⟨x, g, inferInstance⟩ := (SpecToEquivOfLocalRing X R).symm.injective h
  obtain ⟨hx, hf⟩ := SpecToEquivOfLocalRing_eq_iff.mp hh
  simpa using hf

set_option backward.isDefEq.respectTransparency.types false in
/-- Stacks Project, Tag 0B2B (finite-copy extension of its two-copy pushout calculation).
(blueprint: lem-sc-dual-number-scheme-pushout)

The algebra `TrivSqZeroExt K (Fin n → K)` has basis the constant `1` and the `n` coordinate
infinitesimals, all products of infinitesimals being zero. The map induced by
`TrivSqZeroExt.map (LinearMap.proj i)` keeps the `i`th infinitesimal coefficient and kills the
others. The common point is induced by `TrivSqZeroExt.fstHom K K K`.

Proof:
1. Identify this algebra with the tuples of dual numbers having the same constant coefficient:
   send `(a, b)` to the tuple `(a, b i)`. Coordinatewise multiplication agrees with the
   square-zero multiplication. Both this algebra and the dual numbers are local: their
   square-zero infinitesimal ideals have quotient the field `K` (def-sc-dual-numbers).
2. By lem-weil-pbc-morphism-from-spec-local-ring (Stacks Tag 01J6), the common restriction
   gives a point `x` of `X` and a local map from its stalk to `K`. Each `θ i` gives the same
   point and a local map to the dual numbers with that residue map. The tuple of these maps
   defines a unique map from the stalk to the square-zero algebra. It is local since its
   residue map is local, and Tag 01J6 produces `Θ`.
3. Under the same correspondence, restriction along the `i`th map is the `i`th projection
   of the stalk map, so it equals `θ i`. Any other extension has the same point (use `n ≥ 1`)
   and all the same projections. These determine its stalk map, proving uniqueness.
-/
theorem existsUnique_dualNumberScheme_extension
    (K : Type u) [Field K] (n : ℕ) (hn : 1 ≤ n) (X : Scheme.{u})
    (θ : Fin n → (Spec (.of (DualNumber K)) ⟶ X))
    (hθ : ∀ i j : Fin n,
      Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom K K K).toRingHom) ≫ θ i =
      Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom K K K).toRingHom) ≫ θ j) :
    ∃! Θ : Spec (.of (TrivSqZeroExt K (Fin n → K))) ⟶ X,
      ∀ i : Fin n,
        Spec.map (CommRingCat.ofHom
          (TrivSqZeroExt.map (LinearMap.proj i : (Fin n → K) →ₗ[K] K)).toRingHom) ≫ Θ =
          θ i := by
  classical
  have : IsLocalRing (DualNumber K) := squareZeroLocal K K
  have : IsLocalRing (TrivSqZeroExt K (Fin n → K)) :=
    squareZeroLocal K (Fin n → K)
  have : IsLocalHom (CommRingCat.ofHom
    (TrivSqZeroExt.fstHom K K K).toRingHom).hom := squareZeroFstLocal K K
  let i₀ : Fin n := ⟨0, hn⟩
  let x : X := θ i₀ (IsLocalRing.closedPoint (DualNumber K))
  have hx (i : Fin n) : θ i (IsLocalRing.closedPoint (DualNumber K)) = x := by
    have h := congrArg (fun f : Spec (.of K) ⟶ X ↦ f (IsLocalRing.closedPoint K))
      (hθ i i₀)
    simp only [Scheme.Hom.comp_apply] at h
    rw [Spec_closedPoint] at h
    exact h
  have hrep (i : Fin n) : ∃ f : X.presheaf.stalk x ⟶ .of (DualNumber K),
      IsLocalHom f.hom ∧ Spec.map f ≫ X.fromSpecStalk x = θ i := by
    rw [← hx i]
    exact ⟨Scheme.stalkClosedPointTo (θ i), inferInstance,
      Scheme.Spec_stalkClosedPointTo_fromSpecStalk (θ i)⟩
  choose f hf hrep using hrep
  have (i : Fin n) : IsLocalHom (f i).hom := hf i
  let q : CommRingCat.of (DualNumber K) ⟶ CommRingCat.of K :=
    CommRingCat.ofHom (TrivSqZeroExt.fstHom K K K).toRingHom
  have : IsLocalHom q.hom := squareZeroFstLocal K K
  have (i : Fin n) : IsLocalHom (f i ≫ q).hom :=
    CommRingCat.isLocalHom_comp (f i) q
  have hq (i : Fin n) : f i ≫ q = f i₀ ≫ q := by
    apply localSpec_injective X (.of K) x
    simpa only [Spec.map_comp, Category.assoc, hrep] using hθ i i₀
  have hfst (i : Fin n) (a : X.presheaf.stalk x) :
      ((f i).hom a).fst = ((f i₀).hom a).fst := by
    exact congrArg (fun k : X.presheaf.stalk x ⟶ .of K ↦ k.hom a) (hq i)
  let φ : X.presheaf.stalk x →+* TrivSqZeroExt K (Fin n → K) :=
    { toFun := fun a ↦ ⟨((f i₀).hom a).fst, fun i ↦ ((f i).hom a).snd⟩
      map_one' := by
        apply TrivSqZeroExt.ext <;> simp [funext_iff]
      map_zero' := by
        apply TrivSqZeroExt.ext <;> simp [funext_iff]
      map_add' := by
        intro a b
        apply TrivSqZeroExt.ext <;> simp [map_add, funext_iff]
      map_mul' := by
        intro a b
        apply TrivSqZeroExt.ext
        · simp
        · funext i
          simp only [map_mul, TrivSqZeroExt.fst_mul, TrivSqZeroExt.snd_mul,
            smul_eq_mul, MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op,
            TrivSqZeroExt.snd_mk, TrivSqZeroExt.fst_mk, op_smul_eq_smul,
            Pi.add_apply, Pi.smul_apply, hfst]
          congr 1
          exact mul_comm _ _ }
  let p (i : Fin n) : CommRingCat.of (TrivSqZeroExt K (Fin n → K)) ⟶
      CommRingCat.of (DualNumber K) := CommRingCat.ofHom
    (TrivSqZeroExt.map (LinearMap.proj i : (Fin n → K) →ₗ[K] K)).toRingHom
  have (i : Fin n) : IsLocalHom (p i).hom := squareZeroProjLocal K n i
  have hφ (i : Fin n) : CommRingCat.ofHom φ ≫ p i = f i := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro a
    apply TrivSqZeroExt.ext
    · simpa [φ, p] using (hfst i a).symm
    · simp [φ, p]
  have : IsLocalHom φ := ⟨fun a ha ↦ by
    have hu := TrivSqZeroExt.isUnit_iff_isUnit_fst.mp ha
    apply IsUnit.of_map (f i₀).hom a
    apply TrivSqZeroExt.isUnit_iff_isUnit_fst.mpr
    exact hu⟩
  refine ⟨Spec.map (CommRingCat.ofHom φ) ≫ X.fromSpecStalk x, ?_, ?_⟩
  · intro i
    rw [← Category.assoc, ← Spec.map_comp, hφ, hrep]
  · intro Θ hΘ
    have hxΘ : Θ (IsLocalRing.closedPoint (TrivSqZeroExt K (Fin n → K))) = x := by
      have h := congrArg (fun k : Spec (.of (DualNumber K)) ⟶ X ↦
        k (IsLocalRing.closedPoint (DualNumber K))) (hΘ i₀)
      change (Spec.map (p i₀) ≫ Θ) _ = (θ i₀) _ at h
      simp only [Scheme.Hom.comp_apply] at h
      rw [Spec_closedPoint] at h
      exact h
    have hg : ∃ g : X.presheaf.stalk x ⟶ .of (TrivSqZeroExt K (Fin n → K)),
        IsLocalHom g.hom ∧ Spec.map g ≫ X.fromSpecStalk x = Θ := by
      rw [← hxΘ]
      exact ⟨Scheme.stalkClosedPointTo Θ, inferInstance,
        Scheme.Spec_stalkClosedPointTo_fromSpecStalk Θ⟩
    obtain ⟨g, hgLocal, hgRep⟩ := hg
    have : IsLocalHom g.hom := hgLocal
    have (i : Fin n) : IsLocalHom (g ≫ p i).hom :=
      CommRingCat.isLocalHom_comp g (p i)
    have hgp (i : Fin n) : g ≫ p i = CommRingCat.ofHom φ ≫ p i := by
      rw [hφ]
      apply localSpec_injective X (.of (DualNumber K)) x
      rw [Spec.map_comp, Category.assoc, hgRep, hΘ, hrep]
    have hgφ : g = CommRingCat.ofHom φ := by
      apply CommRingCat.hom_ext
      apply RingHom.ext
      intro a
      apply TrivSqZeroExt.ext
      · have h := congrArg (fun k : X.presheaf.stalk x ⟶ .of (DualNumber K) ↦
          (k.hom a).fst) (hgp i₀)
        simpa [p] using h
      · funext i
        have h := congrArg (fun k : X.presheaf.stalk x ⟶ .of (DualNumber K) ↦
          (k.hom a).snd) (hgp i)
        simpa [p] using h
    rw [← hgRep, hgφ]

end AlgebraicGeometry
