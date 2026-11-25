/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.RingTheory.AdjoinRoot
import WeilConjectures.AlgebraicGeometry.Morphisms.RootSplitAwayLocalizationChart
import WeilConjectures.AlgebraicGeometry.Morphisms.RootSplitAwayCoverEtale
import WeilConjectures.AlgebraicGeometry.Morphisms.RootSplitAwayCoverPoint

/-! # Étale affine charts of the punctured root cover

## References

* Stacks Project, Tag 0EYG, off-divisor case
-/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- For `y ∉ V(g)`, the punctured root cover `D(g) ⊆ Spec R[X] ⧸ (X ^ n - g)` is isomorphic to an
affine scheme `Spec S`, étale over `Spec R` and with `g` a unit in `S`, containing a lift of
`y`. -/
theorem root_split_away_localization_point
    (R : CommRingCat.{u}) (g : R) (n : ℕ) (hn : 0 < n ∧ IsUnit (n : R))
    (y : Spec R) (hy : g ∉ y.asIdeal) :
    let A := AdjoinRoot ((Polynomial.X : Polynomial R) ^ n - Polynomial.C g)
    let N := Spec (CommRingCat.of A)
    let q := Spec.map (CommRingCat.ofHom (algebraMap R A))
    let V : N.Opens := PrimeSpectrum.basicOpen (algebraMap R A g)
    ∃ (S : CommRingCat.{u}) (φ : R →+* S) (z : Spec S) (e : Spec S ≅ V.toScheme),
      e.hom ≫ V.ι ≫ q = Spec.map (CommRingCat.ofHom φ) ∧
      Etale (Spec.map (CommRingCat.ofHom φ)) ∧
      (Spec.map (CommRingCat.ofHom φ)) z = y ∧ IsUnit (φ g) := by
  intro A N q V
  obtain ⟨S, φ, e, he, hunit⟩ := root_split_away_localization_chart R g n
  have het : Etale (V.ι ≫ q) := root_split_away_cover_etale R g n hn
  obtain ⟨v, hv⟩ : ∃ v : V.toScheme, (V.ι ≫ q) v = y :=
    root_split_away_cover_point R g n hn.1 y hy
  have hz : (Spec.map (CommRingCat.ofHom φ)) (e.inv v) = y := by
    rw [← he]
    change q (V.ι (e.hom (e.inv v))) = y
    rw [Scheme.inv_hom_apply e v]
    exact hv
  have hφ : Etale (Spec.map (CommRingCat.ofHom φ)) := by
    rw [← he]
    infer_instance
  exact ⟨S, φ, e.inv v, e, he, hφ, hz, hunit⟩

end AlgebraicGeometry.Scheme
