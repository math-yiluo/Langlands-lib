/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.RingTheory.Localization.AtPrime.Basic
import WeilConjectures.AlgebraicGeometry.FilteredColimitLocalizationAtPrimeData


/-!
# Localization at a prime commutes with filtered colimits

Source: Stacks Project, Algebra, proof of Lemma Tag 037D (blueprint:
lemma-quasi-finite-coordinates--1).
-/

@[expose] public section

universe v

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry



/-- Stacks Project, Algebra, proof of Tag 037D (`lemma-colimit-normal-ring`),
(blueprint: lemma-quasi-finite-coordinates--1).
Localization at a prime of a filtered colimit is the colimit of the localizations
at the contracted primes, with the canonical maps.

1. Contract the prime along the coprojections. The cocone identity implies that
   each transition map contracts the later prime to the earlier prime. Thus it
   sends denominators outside the earlier prime outside the later prime, induces
   the fraction map, and these maps form a functor
   (def-weil-pbc-category-colimit; def-weil-pbc-localization-at-prime).
2. The coprojections likewise induce fraction maps to the localization of the
   colimit. Their compatibility on fractions gives a cocone (the same two nodes).
3. Lift the numerator and denominator to a common stage using
   lem-weil-pbc-filtered-colimit-algebras-elementwise over the integers and
   filteredness. The lifted denominator avoids the contracted prime. Hence every
   fraction, and every finite family of fractions, comes from a common stage.
4. For equal fractions, lift the multiplier witnessing their equality to a
   common stage, using lem-weil-pbc-filtered-colimit-algebras-elementwise.
   By lem-weil-pbc-filtered-colimit-rings-zero the resulting zero relation holds
   at a later stage. The multiplier still avoids the prime, so the fractions
   become equal there (def-weil-pbc-localization-at-prime).
5. For any cocone define its factorization on a fraction by choosing a stage
   representative. Step 4 makes this well defined. Common-stage representatives
   show that it respects addition, multiplication and one; step 3 gives
   uniqueness. This is the universal property in def-weil-pbc-category-colimit.

The compatibility equations on the original rings uniquely determine the
localized maps: denominators are units, so they imply the stated fraction formulas. -/
theorem filteredColimitLocalizationAtPrime
    {I : Type v} [SmallCategory I] [IsFiltered I]
    (F : I ⥤ CommRingCat.{v}) [HasColimit F]
    (p : Ideal ((colimit F : CommRingCat) : Type v)) [hp : p.IsPrime] :
    let ι : ∀ i : I, (F.obj i) ⟶ colimit F := fun i => colimit.ι F i
    let pᵢ : ∀ i : I, Ideal ((F.obj i : CommRingCat) : Type v) :=
      fun i => Ideal.comap (ι i).hom p
    (∀ i : I, (pᵢ i).IsPrime) ∧
    (∀ (i j : I) (a : i ⟶ j), Ideal.comap (F.map a).hom (pᵢ j) = pᵢ i) ∧
    ∃ (D : I ⥤ CommRingCat.{v})
      (hD : ∀ i : I, D.obj i = CommRingCat.of (Localization.AtPrime (pᵢ i))),
      (∀ (i j : I) (a : i ⟶ j),
        CommRingCat.ofHom (algebraMap (F.obj i) (Localization.AtPrime (pᵢ i))) ≫
            eqToHom (hD i).symm ≫ D.map a =
          F.map a ≫
            CommRingCat.ofHom (algebraMap (F.obj j) (Localization.AtPrime (pᵢ j))) ≫
            eqToHom (hD j).symm) ∧
      ∃ (c : Cocone D) (hc : c.pt = CommRingCat.of (Localization.AtPrime p)),
        (∀ i : I,
          CommRingCat.ofHom (algebraMap (F.obj i) (Localization.AtPrime (pᵢ i))) ≫
              eqToHom (hD i).symm ≫ c.ι.app i ≫ eqToHom hc =
            ι i ≫ CommRingCat.ofHom
              (algebraMap ((colimit F : CommRingCat) : Type v) (Localization.AtPrime p))) ∧
        Nonempty (IsColimit c) := by
  dsimp
  let ι : ∀ i : I, (F.obj i) ⟶ colimit F := fun i => colimit.ι F i
  let pᵢ : ∀ i : I, Ideal ((F.obj i : CommRingCat) : Type v) :=
    fun i => Ideal.comap (ι i).hom p
  have hprime : ∀ i : I, (pᵢ i).IsPrime := by
    intro i
    exact Ideal.IsPrime.comap _
  have hcompat : ∀ (i j : I) (a : i ⟶ j),
      Ideal.comap (F.map a).hom (pᵢ j) = pᵢ i := by
    intro i j a
    ext x
    change (ι j).hom ((F.map a).hom x) ∈ p ↔ (ι i).hom x ∈ p
    have heq : (ι j).hom ((F.map a).hom x) = (ι i).hom x := by
      change (F.map a ≫ ι j).hom x = (ι i).hom x
      rw [colimit.w]
    exact heq ▸ Iff.rfl
  have hdata := filteredColimitLocalizationAtPrime_data (F := F) (p := p)
  exact ⟨hprime, hcompat, hdata⟩

end AlgebraicGeometry
