/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.Localization.AtPrime.Basic

import Mathlib.AlgebraicGeometry.PullbackCarrier
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified
import WeilConjectures.AlgebraicGeometry.Morphisms.RootProductChartCore

/-! Stalk localization of a root product chart.

## References

* Stacks Project, Tags 0EYH, 0EYI and 0EYJ
* Stacks Project, Tag 0EYH, its etale local description
* Tag 0EYI, the choice of a pointed etale neighbourhood
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

private theorem maximalIdeal_stalkMap_comp {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) :
    ((IsLocalRing.maximalIdeal (Z.presheaf.stalk (g (f x)))).map
      (g.stalkMap (f x)).hom).map (f.stalkMap x).hom =
    (IsLocalRing.maximalIdeal (Z.presheaf.stalk ((f ≫ g) x))).map
      ((f ≫ g).stalkMap x).hom := by
  rw [Scheme.Hom.stalkMap_comp, CommRingCat.hom_comp, Ideal.map_map]
  rfl

/-- Extract a localized root factor from an affine etale product chart. -/
theorem rootProductChart_stalk_localization {L N : Scheme.{u}} (n : N ⟶ L)
    (R : CommRingCat.{u}) (φ : Spec R ⟶ L) (y : Spec R) (hφ : Etale φ)
    (x : N) (hy : φ y = n x) (f : R) (hf : f ∈ y.asIdeal)
    (m : ℕ) (e : Fin m → ℕ) (he : ∀ k, 0 < e k)
    (α : pullback n φ ≅ Spec (CommRingCat.of (∀ k : Fin m,
      AdjoinRoot ((Polynomial.X : Polynomial R) ^ e k - Polynomial.C f))))
    (hα : α.hom ≫ Spec.map (CommRingCat.ofHom
      (algebraMap R (∀ k : Fin m,
        AdjoinRoot ((Polynomial.X : Polynomial R) ^ e k - Polynomial.C f)))) =
        pullback.snd n φ) :
    let B := N.presheaf.stalk x
    let J := (IsLocalRing.maximalIdeal (L.presheaf.stalk (n x))).map (n.stalkMap x).hom
    ∃ (k : Fin m) (R₀ : CommRingCat.{u}) (_ : IsLocalRing R₀) (f₀ : R₀),
      f₀ ∈ IsLocalRing.maximalIdeal R₀ ∧
      let p := (Polynomial.X : Polynomial R₀) ^ e k - Polynomial.C f₀
      let D := AdjoinRoot p
      ∃ (P : Ideal D) (hP : P.IsMaximal),
        letI : P.IsPrime := hP.isPrime
        let E := Localization.AtPrime P
        ∃ β : B →+* E, IsLocalHom β ∧ β.Flat ∧
          J.map β = (IsLocalRing.maximalIdeal R₀).map
            ((algebraMap D E).comp (AdjoinRoot.of p))  := by
  classical
  let : Etale φ := hφ
  dsimp only
  obtain ⟨z, hx, hz⟩ := Pullback.exists_preimage_pullback (f := n) (g := φ) x y hy.symm
  have hfz : f ∈ ((pullback.snd n φ) z).asIdeal := by simpa only [hz] using hf
  obtain ⟨k, f₀, hf₀, P, hP, θ, hθ⟩ := rootProductChart_stalk_localization_core
    R (pullback.snd n φ) z f hfz m e he α hα
  subst x
  let R₀ := (Spec R).presheaf.stalk ((pullback.snd n φ) z)
  let p := (Polynomial.X : Polynomial R₀) ^ e k - Polynomial.C f₀
  let D := AdjoinRoot p
  let : P.IsPrime := hP.isPrime
  let E := Localization.AtPrime P
  let β : N.presheaf.stalk ((pullback.fst n φ) z) →+* E :=
    θ.toRingHom.comp ((pullback.fst n φ).stalkMap z).hom
  let : IsLocalHom θ.toRingHom := ⟨fun a ha ↦ (isUnit_map_iff θ a).mp ha⟩
  have hβ : IsLocalHom β := by dsimp only [β]; infer_instance
  have hflat : β.Flat :=
    (Flat.stalkMap (pullback.fst n φ) z).comp (RingHom.Flat.of_bijective θ.bijective)
  have hcomm := congrArg (fun (q : pullback n φ ⟶ L) =>
    (IsLocalRing.maximalIdeal (L.presheaf.stalk (q z))).map (q.stalkMap z).hom)
      (pullback.condition (f := n) (g := φ))
  rw [← maximalIdeal_stalkMap_comp, ← maximalIdeal_stalkMap_comp] at hcomm
  have hbase := FormallyUnramified.map_maximalIdeal_stalkMap φ ((pullback.snd n φ) z)
  rw [hbase] at hcomm
  have hJ :
      ((IsLocalRing.maximalIdeal (L.presheaf.stalk (n ((pullback.fst n φ) z)))).map
        (n.stalkMap ((pullback.fst n φ) z)).hom).map β =
      (IsLocalRing.maximalIdeal R₀).map ((algebraMap D E).comp (AdjoinRoot.of p)) := by
    dsimp only [β]
    rw [← Ideal.map_map, hcomm, Ideal.map_map, hθ]
  exact ⟨k, R₀, inferInstance, f₀, hf₀, P, hP, β, hβ, hflat, hJ⟩

end AlgebraicGeometry.Scheme
