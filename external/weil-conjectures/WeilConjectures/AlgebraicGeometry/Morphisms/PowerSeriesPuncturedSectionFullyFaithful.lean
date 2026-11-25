/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.Functoriality
public import WeilConjectures.RingTheory.Depth
import WeilConjectures.AlgebraicGeometry.Morphisms.PowerSeriesPuncturedSectionSurjective
import WeilConjectures.AlgebraicGeometry.Morphisms.PowerSeriesPuncturedSectionInjective

/-!
# Full faithfulness on the punctured zero section of a power-series open

## References

* Stacks Project, Tag 0EY9 (Lemma 58.26.1)
* Stacks Project, Tags 0BK0, 0EKP and 0EL8
-/

@[expose] public section

universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme

/-- Restricting finite etale covers to the punctured zero section is fully faithful.
The hypothesis on V says exactly that its intersection with the zero section is
Spec A minus its closed point. Bijectivity on every morphism set expresses full
faithfulness of the actual finite-etale pullback functor, without choosing lifts. -/
theorem finiteEtale_powerSeries_punctured_section_fully_faithful
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (hdepth : (2 : ℕ∞) ≤ IsLocalRing.depth (R := A) A)
    (d : ℕ) (hd : 0 < d)
    (V : (Spec (.of (MvPowerSeries (Fin d) A))).Opens)
    (hV : ∀ x : Spec (.of A),
      (Spec.map (CommRingCat.ofHom (MvPowerSeries.constantCoeff (σ := Fin d)))) x ∈ V ↔
        x ≠ IsLocalRing.closedPoint A) :
    let z := Spec.map (CommRingCat.ofHom (MvPowerSeries.constantCoeff (σ := Fin d)))
    ∀ P Q : V.toScheme.FiniteEtale,
      Function.Bijective ((FiniteEtale.pullback (z ∣_ V)).map (X := P) (Y := Q)) := by
  dsimp
  intro P Q
  exact ⟨finiteEtale_powerSeries_punctured_section_restriction_injective
      A hdepth d hd V hV P Q,
    finiteEtale_powerSeries_punctured_section_restriction_surjective
      A hdepth d hd V hV P Q⟩

end AlgebraicGeometry.Scheme
