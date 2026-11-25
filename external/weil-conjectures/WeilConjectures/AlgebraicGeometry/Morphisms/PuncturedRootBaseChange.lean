/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.RingTheory.AdjoinRoot

/-! # Base change of a punctured root chart

## References

* Stacks Project, Tags 05N9 and 01YW
-/

@[expose] public section

universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

private theorem root_pushout (R S : CommRingCat.{u}) (b : R ⟶ S)
    (p : Polynomial R) (q : Polynomial S) (hp : p.map b.hom = q) :
    let i := CommRingCat.ofHom (AdjoinRoot.of p)
    let j := CommRingCat.ofHom (AdjoinRoot.of q)
    let m := CommRingCat.ofHom (AdjoinRoot.map b.hom p q (hp ▸ dvd_refl q))
    IsPushout b i j m := by
  dsimp only
  let i := CommRingCat.ofHom (AdjoinRoot.of p)
  let j := CommRingCat.ofHom (AdjoinRoot.of q)
  let m := CommRingCat.ofHom (AdjoinRoot.map b.hom p q (hp ▸ dvd_refl q))
  have w : b ≫ j = i ≫ m := by ext r; simp [i, j, m]
  let desc (s : PushoutCocone b i) : CommRingCat.of (AdjoinRoot q) ⟶ s.pt :=
    CommRingCat.ofHom (AdjoinRoot.lift s.inl.hom
      (s.inr.hom (AdjoinRoot.root p)) (by
        rw [← hp, Polynomial.eval₂_map]
        have h : s.inl.hom.comp b.hom = s.inr.hom.comp (AdjoinRoot.of p) :=
          congrArg CommRingCat.Hom.hom s.condition
        rw [h, ← Polynomial.hom_eval₂, AdjoinRoot.eval₂_root, map_zero]))
  apply IsPushout.of_isColimit (c := PushoutCocone.mk j m w)
  refine PushoutCocone.IsColimit.mk w desc ?_ ?_ ?_
  · intro s
    ext r
    simp [j, desc]
  · intro s
    ext r
    · simp only [CommRingCat.hom_comp, ConcreteCategory.hom_ofHom, RingHom.coe_comp,
        Function.comp_apply, AdjoinRoot.map_of, AdjoinRoot.lift_of, i, m, desc]
      exact congrArg (fun h : R ⟶ s.pt => h.hom r) s.condition
    · simp [m, desc]
  · intro s m' hl hr
    ext r
    · simpa [j, desc] using congrArg (fun h : S ⟶ s.pt => h.hom r) hl
    · simpa [m, desc] using
        congrArg (fun h : CommRingCat.of (AdjoinRoot p) ⟶ s.pt =>
          h.hom (AdjoinRoot.root p)) hr

/-- A punctured root chart over S is the base change of the chart over R. -/
theorem punctured_root_base_change
    (R S : CommRingCat.{u}) (f : R) (n : ℕ) (b : R ⟶ S) :
    let A₀ := AdjoinRoot ((Polynomial.X : Polynomial R) ^ n - Polynomial.C f)
    let N₀ := Spec (CommRingCat.of A₀)
    let q₀ := Spec.map (CommRingCat.ofHom (algebraMap R A₀))
    let V₀ : N₀.Opens := PrimeSpectrum.basicOpen (algebraMap R A₀ f)
    let A := AdjoinRoot ((Polynomial.X : Polynomial S) ^ n - Polynomial.C (b.hom f))
    let N := Spec (CommRingCat.of A)
    let q := Spec.map (CommRingCat.ofHom (algebraMap S A))
    let V : N.Opens := PrimeSpectrum.basicOpen (algebraMap S A (b.hom f))
    ∃ e : V.toScheme ≅ pullback (Spec.map b) (V₀.ι ≫ q₀),
      e.hom ≫ pullback.fst (Spec.map b) (V₀.ι ≫ q₀) = V.ι ≫ q  := by
  let p := (Polynomial.X : Polynomial R) ^ n - Polynomial.C f
  let q := (Polynomial.X : Polynomial S) ^ n - Polynomial.C (b.hom f)
  have hp : p.map b.hom = q := by simp [p, q]
  let i := CommRingCat.ofHom (AdjoinRoot.of p)
  let j := CommRingCat.ofHom (AdjoinRoot.of q)
  let m := CommRingCat.ofHom (AdjoinRoot.map b.hom p q (hp ▸ dvd_refl q))
  have hr : IsPushout b i j m := root_pushout R S b p q hp
  let h := Spec.map m
  let N := Spec (CommRingCat.of (AdjoinRoot q))
  let N₀ := Spec (CommRingCat.of (AdjoinRoot p))
  let V₀ : N₀.Opens := PrimeSpectrum.basicOpen (AdjoinRoot.of p f)
  let V : N.Opens := PrimeSpectrum.basicOpen (AdjoinRoot.of q (b.hom f))
  have hpre : h ⁻¹ᵁ V₀ = V := by
    change PrimeSpectrum.basicOpen
      (AdjoinRoot.map b.hom p q (hp ▸ dvd_refl q) (AdjoinRoot.of p f)) = _
    rw [AdjoinRoot.map_of]
  have hs := isPullback_SpecMap_of_isPushout b i j m hr
  have ht := ((isPullback_morphismRestrict h V₀).paste_vert hs.flip).flip
  let e₀ := N.isoOfEq hpre.symm
  refine ⟨e₀ ≪≫ ht.isoPullback, ?_⟩
  change (e₀ ≪≫ ht.isoPullback).hom ≫
    pullback.fst (Spec.map b) (V₀.ι ≫ Spec.map i) = V.ι ≫ Spec.map j
  simp only [Iso.trans_hom, Category.assoc, ht.isoPullback_hom_fst]
  rw [← Category.assoc, Scheme.isoOfEq_hom_ι]

end AlgebraicGeometry.Scheme
