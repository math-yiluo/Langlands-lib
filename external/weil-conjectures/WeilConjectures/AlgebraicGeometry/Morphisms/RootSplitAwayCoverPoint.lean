/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.RingTheory.AdjoinRoot
import WeilConjectures.Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra

/-!
# Points of the punctured root cover

## References

* Stacks Project, Tag 0EYG, off-divisor branch
-/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- A point off g lifts to the punctured monic root cover. -/
theorem root_split_away_cover_point
    (R : CommRingCat.{u}) (g : R) (n : ℕ) (hn : 0 < n)
    (y : Spec R) (hy : g ∉ y.asIdeal) :
    let A := AdjoinRoot ((Polynomial.X : Polynomial R) ^ n - Polynomial.C g)
    let N := Spec (CommRingCat.of A)
    let q := Spec.map (CommRingCat.ofHom (algebraMap R A))
    let V : N.Opens := PrimeSpectrum.basicOpen (algebraMap R A g)
    ∃ v : V.toScheme, (V.ι ≫ q) v = y := by
  dsimp
  have : Nontrivial R := nontrivial_of_ne g 0 (fun h ↦ hy (h ▸ y.asIdeal.zero_mem))
  let f : Polynomial R := Polynomial.X ^ n - Polynomial.C g
  let A := AdjoinRoot f
  have hm : f.Monic := Polynomial.monic_X_pow_sub_C g (Nat.ne_of_gt hn)
  have hd : f.degree ≠ 0 := by
    rw [Polynomial.degree_X_pow_sub_C hn]
    exact_mod_cast Nat.ne_of_gt hn
  have : Module.FaithfullyFlat R A := AdjoinRoot.faithfullyFlat_of_monic hm hd
  obtain ⟨v, hv⟩ := PrimeSpectrum.comap_surjective_of_faithfullyFlat (A := R) (B := A) y
  have hg : algebraMap R A g ∉ v.asIdeal := by
    change g ∉ (PrimeSpectrum.comap (algebraMap R A) v).asIdeal
    rwa [hv]
  exact ⟨⟨v, hg⟩, hv⟩

end AlgebraicGeometry.Scheme
