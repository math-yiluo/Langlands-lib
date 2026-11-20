import Langlands.Geometry.Analytic.QuasiEtaleRigidity.EtaleRigidity
import Langlands.Geometry.Analytic.GlobalChartSourceMaps

/-! # Charts over which near lifts exist -/

noncomputable section

universe u v

namespace Langlands.Analytic.SaturatedAtlasPresentation

open CategoryTheory Set

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable {A B : AffinoidAtlasPresentation.{u, v, v} K}

/-- A chart `c` of the saturation of `A` over which near lifts along `g` exist, with uniform
tests: `g` maps `c` into the target chart `w`, and for finitely many functions `F` on `c` and a
bound `ε` there are finitely many functions `G` on `w` and a bound `δ` such that, for every strong
map `x` into the saturation of `A` sending a source chart `P` into `c` and every strong map `y`
into the saturation of `B` sending `P` into `w` whose pullbacks of `G` differ from those of
`x ≫ g` by at most `δ`, there is a bounded map `a : O(c) → O(P)` with `a ∘ g* = y*` whose values on
`F` differ from those of `x*` by at most `ε`. -/
def IsLiftChart (g : ofSaturation A ⟶ ofSaturation B)
    (c : (ofSaturation A).presentation.atlas.Index) : Prop :=
  ∃ (w : (ofSaturation B).presentation.atlas.Index)
    (hcw : g.baseMap '' range ((ofSaturation A).presentation.atlas.chart c) ⊆
      range ((ofSaturation B).presentation.atlas.chart w)),
    ∀ (F : Finset ((ofSaturation A).presentation.atlas.algebra c)) (ε : ℝ), 0 < ε →
      ∃ (G : Finset ((ofSaturation B).presentation.atlas.algebra w)) (δ : ℝ), 0 < δ ∧
        ∀ (S : SaturatedAtlasPresentation.{u, v, v} K) (x : S ⟶ ofSaturation A)
          (y : S ⟶ ofSaturation B) (P : S.presentation.atlas.Index)
          (hx : x.baseMap '' range (S.presentation.atlas.chart P) ⊆
            range ((ofSaturation A).presentation.atlas.chart c))
          (hxg : (x ≫ g).baseMap '' range (S.presentation.atlas.chart P) ⊆
            range ((ofSaturation B).presentation.atlas.chart w))
          (hy : y.baseMap '' range (S.presentation.atlas.chart P) ⊆
            range ((ofSaturation B).presentation.atlas.chart w)),
          (∀ h ∈ G, ∀ p : BanachSpectrum (S.presentation.atlas.algebra P),
            p (y.pullback P w hy h - (x ≫ g).pullback P w hxg h) ≤ δ) →
          ∃ a : BoundedAlgHom K ((ofSaturation A).presentation.atlas.algebra c)
              (S.presentation.atlas.algebra P),
            a.comp (g.pullback c w hcw) = y.pullback P w hy ∧
              ∀ h ∈ F, ∀ p : BanachSpectrum (S.presentation.atlas.algebra P),
                p (a h - x.pullback P c hx h) ≤ ε

end Langlands.Analytic.SaturatedAtlasPresentation
