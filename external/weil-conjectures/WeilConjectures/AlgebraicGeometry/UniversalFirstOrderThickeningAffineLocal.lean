/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified
public import WeilConjectures.AlgebraicGeometry.UniversalFirstOrderThickening

import WeilConjectures.AlgebraicGeometry.UniversalThickeningAffineCase
import WeilConjectures.AlgebraicGeometry.UniversalFirstOrderThickeningCoverGluing
import WeilConjectures.RingTheory.UniversalFirstOrderThickening
import WeilConjectures.AlgebraicGeometry.UniversalThickeningOpenPieces

/-!
# Affine-local construction of universal first order thickenings

The affine-open construction in Stacks, More on Morphisms, Lemma 37.7.1 (Tag 04F3),
first produces a thickening with the lifting property for affine test schemes.
(blueprint: lem-weil-pbc-universal-first-order-thickening-affine-local)
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- Enlarge an open base using the existing open-pieces theorem, after identifying
an open immersion's source with its open image. -/
private theorem universal_over_openImmersion
    {Z Z' U X : Scheme.{u}} (g : Z ⟶ U) (i : Z ⟶ Z') (g' : Z' ⟶ U)
    (s : U ⟶ X) [IsOpenImmersion s]
    (H : IsUniversalFirstOrderThickening g i g') :
    IsUniversalFirstOrderThickening (g ≫ s) i (g' ≫ s) := by
  let e := s.isoOpensRange
  have Hr : IsUniversalFirstOrderThickening (g ≫ e.hom) i (g' ≫ e.hom) := by
    refine ⟨H.1, ?_, ?_⟩
    · rw [← Category.assoc, H.2.1]
    · intro T T' j b a hj hab
      have habU : j ≫ (b ≫ e.inv) = a ≫ g := by
        simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id] using
          congrArg (fun f ↦ f ≫ e.inv) hab
      obtain ⟨c, hc, huniq⟩ := H.2.2 j (b ≫ e.inv) a hj habU
      refine ⟨c, ⟨?_, hc.2⟩, ?_⟩
      · rw [← Category.assoc, hc.1, Category.assoc, Iso.inv_hom_id, Category.comp_id]
      · intro c' hc'
        apply huniq c'
        refine ⟨?_, hc'.2⟩
        simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id] using
          congrArg (fun f ↦ f ≫ e.inv) hc'.1
  have hh : (g ≫ e.hom) ≫ s.opensRange.ι = g ≫ s := by
    rw [Category.assoc, Scheme.Hom.isoOpensRange_hom_ι]
  have Hx := (universalFirstOrderThickening_open_pieces (g ≫ s)).2.2
    s.opensRange (g ≫ e.hom) hh i (g' ≫ e.hom) Hr
  simpa only [e, Category.assoc, Scheme.Hom.isoOpensRange_hom_ι] using Hx

/-- The affine construction, transported from spectra along the canonical affine isomorphisms. -/
private theorem exists_affine_thickening {Z X : Scheme.{u}}
    [IsAffine Z] [IsAffine X] (h : Z ⟶ X) [FormallyUnramified h] :
    ∃ (Z' : Scheme.{u}) (i : Z ⟶ Z') (h' : Z' ⟶ X),
      IsUniversalFirstOrderThickening h i h' := by
  let : Algebra Γ(X, ⊤) Γ(Z, ⊤) := h.appTop.hom.toAlgebra
  have hring : Algebra.FormallyUnramified Γ(X, ⊤) Γ(Z, ⊤) :=
    HasRingHomProperty.appTop (P := @FormallyUnramified) (f := h) inferInstance
  obtain ⟨S', instCR, instAlg, π, hsurj, hker, hprop, _⟩ :=
    Algebra.exists_universalFirstOrderThickening Γ(X, ⊤) Γ(Z, ⊤)
  let : CommRing S' := instCR
  let : Algebra Γ(X, ⊤) S' := instAlg
  have H := isUniversalFirstOrderThickening_spec Γ(X, ⊤) Γ(Z, ⊤) S'
    h.appTop.hom π rfl hsurj hker hprop
  let i := Z.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom π.toRingHom)
  let h' := Spec.map (CommRingCat.ofHom (algebraMap Γ(X, ⊤) S')) ≫ X.isoSpec.inv
  have : IsClosedImmersion (Spec.map (CommRingCat.ofHom π.toRingHom)) := H.1.1
  refine ⟨Spec (.of S'), i, h', ⟨inferInstance, ?_⟩, ?_, ?_⟩
  · simpa only [i, Scheme.Hom.ker_comp_of_isIso] using H.1.2
  · dsimp only [i, h']
    rw [Category.assoc, ← Category.assoc _ _ X.isoSpec.inv, H.2.1]
    change Z.isoSpec.hom ≫ Spec.map h.appTop ≫ X.isoSpec.inv = h
    rw [Scheme.isoSpec_hom_naturality_assoc]
    simp
  · intro T T' j b a hj hab
    have habSpec : j ≫ (b ≫ X.isoSpec.hom) =
        (a ≫ Z.isoSpec.hom) ≫ Spec.map h.appTop := by
      rw [Category.assoc, Scheme.isoSpec_hom_naturality,
        ← Category.assoc, ← Category.assoc, hab]
    obtain ⟨c, hc, huniq⟩ := H.2.2 j (b ≫ X.isoSpec.hom) (a ≫ Z.isoSpec.hom) hj habSpec
    refine ⟨c, ⟨?_, ?_⟩, ?_⟩
    · dsimp only [h']
      rw [← Category.assoc, hc.1]
      simp
    · simpa only [i, Category.assoc] using hc.2
    · intro c' hc'
      apply huniq c'
      refine ⟨?_, ?_⟩
      · apply (cancel_mono X.isoSpec.inv).mp
        simpa only [h', Category.assoc, Iso.hom_inv_id, Category.comp_id] using hc'.1
      · simpa only [i, Category.assoc] using hc'.2

/-- The affine pieces of the square-zero construction and their gluing produce a
first-order thickening which has the universal lifting property for affine tests.
Source: Stacks, More on Morphisms, Lemma 37.7.1 (Tag 04F3), affine construction.
(blueprint: lem-weil-pbc-universal-first-order-thickening-affine-local)
Proof: choose an affine open cover, apply the affine square-zero construction, glue
the pieces using uniqueness on overlaps, and verify the lifting property whenever
both the test schemes are affine. -/
theorem FormallyUnramified.exists_affine_local_universalFirstOrderThickening
    {Z X : Scheme.{u}} (h : Z ⟶ X) [FormallyUnramified h] :
    ∃ (Z' : Scheme.{u}) (i : Z ⟶ Z') (h' : Z' ⟶ X),
      IsFirstOrderThickening i ∧ i ≫ h' = h ∧
        ∀ {T T' : Scheme.{u}} [IsAffine T] [IsAffine T']
          (j : T ⟶ T') (b : T' ⟶ X) (a : T ⟶ Z),
          IsFirstOrderThickening j → j ≫ b = a ≫ h →
            ∃! a' : T' ⟶ Z', a' ≫ h' = b ∧ j ≫ a' = a ≫ i := by
  classical
  let B := X.affineCover
  let D := B.pullback₁ h
  let C := D.bind fun k ↦ (D.X k).affineCover
  have hlocal (k : C.I₀) :
      ∃ (Z' : Scheme.{u}) (i : C.X k ⟶ Z') (h' : Z' ⟶ X),
        IsUniversalFirstOrderThickening (C.f k ≫ h) i h' := by
    let g := (D.X k.1).affineCover.f k.2 ≫ B.pullbackHom h k.1
    have hp : FormallyUnramified (B.pullbackHom h k.1) := by
      change FormallyUnramified (Limits.pullback.snd h (B.f k.1))
      exact MorphismProperty.pullback_snd (P := @FormallyUnramified) _ _ inferInstance
    have : FormallyUnramified g :=
      MorphismProperty.comp_mem @FormallyUnramified _ _ inferInstance hp
    obtain ⟨Z', i, g', H⟩ := exists_affine_thickening g
    refine ⟨Z', i, g' ≫ B.f k.1, ?_⟩
    have hg : g ≫ B.f k.1 = C.f k ≫ h := by
      dsimp only [g, C]
      rw [Category.assoc, B.pullbackHom_map]
      rfl
    rw [← hg]
    exact universal_over_openImmersion g i g' (B.f k.1) H
  choose Z' i h' H using hlocal
  obtain ⟨W, j, p, HW⟩ := universalFirstOrderThickening_glue h C Z' i h' H
  refine ⟨W, j, p, HW.1, HW.2.1, ?_⟩
  intro T T' _ _ jT b a hj hab
  exact HW.2.2 jT b a hj hab

end AlgebraicGeometry
