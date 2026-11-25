/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.GrothendieckAbelian.ConcreteCoefficients
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
import WeilConjectures.AlgebraicGeometry.EtaleChartSectionsObjectComparison

/-!
# Restricting inverse-image sections to an etale chart

Source: Stacks Project, Etale Cohomology, Tag 0EZX, proof, and Tag 0A3H;
composition of inverse images and restriction to an etale object.
(blueprint: lem-sbc-etale-chart-sections-arrow-comparison).
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite
open scoped AlgebraicGeometry.Etale

namespace AlgebraicGeometry.Etale

/-- The sections map on a chart is the terminal-object unit map of the induced
morphism to its etale base, up to isomorphism of arrows. No flatness or connectedness
assumption is needed for this comparison.

Source: Stacks Project, Etale Cohomology, Tag 0EZX, proof, first displayed formula;
Tag 0A3H, applied after restriction to the etale base.
(blueprint: lem-sbc-etale-chart-sections-arrow-comparison).

Proof:
1. Write `j = W.hom`, `r = V.hom`, and `q = φ.left ≫ pullback.fst V.hom p`.
   The defining equation of the chart and the pullback condition give `j ≫ p = q ≫ r`.
2. The etale localization comparisons identify `G(V)` with terminal sections of
   `r^* G`, and `(p^* G)(W)` with terminal sections of `j^* p^* G`.
   Compose the inverse-image composition comparisons for `(j,p)` and `(q,r)`
   with the equality from Step 1. This identifies the latter sheaf with `q^* r^* G`.
3. Identify the base change of the terminal object of `V` along `q` with the terminal
   object of `W` using its canonical pullback isomorphism. The two comparisons of
   section objects are isomorphisms.
4. The unit equation for composition of inverse-image adjunctions, followed by
   restriction along `φ`, identifies the chart sections map with the unit for `q`
   on terminal sections of `r^* G`. The restriction/localization unit equations
   ensure that the source comparison in Step 2 carries the original section to
   its restriction. These equations give a commutative square with the object
   isomorphisms of Steps 2 and 3. Apply `Arrow.isoMk`. -/
theorem nonempty_etaleChartSections_arrowIso
    (Λ : Type (u + 1)) [CommRing Λ] {X S : Scheme.{u}} (p : X ⟶ S)
    (G : Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    {V : S.Etale} {W : X.Etale}
    (φ : W ⟶ (MorphismProperty.Over.pullback @AlgebraicGeometry.Etale ⊤ p).obj V) :
    Nonempty (Arrow.mk
      (((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) p).unit.app G).hom.app (op V) ≫
        ((p)^*[ModuleCat.{u + 1} Λ].obj G).obj.map φ.op) ≅
      Arrow.mk
        (((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ)
          (φ.left ≫ pullback.fst V.hom p)).unit.app
            ((V.hom)^*[ModuleCat.{u + 1} Λ].obj G)).hom.app
              (op (Scheme.Etale.mk (𝟙 V.left))))) := by
  obtain ⟨e₁, e₂, h⟩ :=
    (etaleChartSections_objectComparison Λ p G φ).some
  exact ⟨Arrow.isoMk e₁ e₂ h⟩

end AlgebraicGeometry.Etale
