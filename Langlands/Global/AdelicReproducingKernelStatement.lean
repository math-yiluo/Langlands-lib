import Langlands.GroupScheme.Reductive.Basic
import Langlands.Global.AdelicIwasawaStatement
import Langlands.Global.AdelicGroupHaarMeasure
import Langlands.Automorphic.GroupSchemeInvariantForms

/-! # Harish-Chandra's reproducing kernel on the adelic points of a reductive group

`AdelicReproducingKernelStatement` (Harish-Chandra 1966, §8, Theorem 1, applied at the
archimedean places, in the adelic form of Mœglin–Waldspurger I.2.17, Lemma): a left
`G(F)`-invariant, smooth, `K_∞`-finite and `𝔷`-finite function `Φ` on `G(𝔸)` satisfies
`Φ(g) = ∫ Φ(g a) A(a) da` for a continuous compactly supported function `A` on `G(𝔸)`. No growth
condition is imposed on `Φ`. -/

noncomputable section

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj

set_option autoImplicit false

namespace Langlands.Global

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints

/-- Harish-Chandra's reproducing kernel on `G(𝔸)` (Harish-Chandra 1966, §8, Theorem 1, applied at
the archimedean places; adelic form as in Mœglin–Waldspurger I.2.17, Lemma). Let `G` be a
connected reductive group over a number field `F`, `K` a maximal compact subgroup of `G(𝔸)` and
`K_∞ = K.comap (ofInfinite F G)` its archimedean part. If `Φ : G(𝔸) → ℂ` is left
`G(F)`-invariant, smooth (`IsAdelicSmoothFunction`), `K_∞`-finite and `𝔷`-finite, then there is
a continuous compactly supported `A : G(𝔸) → ℂ` with `Φ g = ∫ a, Φ (g * a) * A a` for every
`g`, the integral being taken for the Haar measure `Measure.haar` of `G(𝔸)`. No growth condition
on `Φ` is assumed. -/
def AdelicReproducingKernelStatement : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (G : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom],
    IsConnectedReductive G →
    ∀ (K : Subgroup (AdelicGroupPoints F G)) {d : ℕ}
      (hsmooth : SmoothOfRelativeDimension d G.X.hom)
      (hcalc : AdelicDifferentialCommutator F G hsmooth),
      IsMaximalCompactSubgroup F G K →
    ∀ Φ : AdelicGroupPoints F G → ℂ,
      IsLeftInvariantUnder F G (rationalSubgroup F G) Φ →
      IsAdelicSmoothFunction F G Φ →
      IsInfiniteSubgroupFiniteFunction F G (K.comap (ofInfinite F G).toMonoidHom) Φ →
      IsCenterFiniteFunction F G hsmooth hcalc Φ →
      ∃ A : AdelicGroupPoints F G → ℂ, Continuous A ∧ HasCompactSupport A ∧
        ∀ g : AdelicGroupPoints F G,
          Φ g = ∫ a, Φ (g * a) * A a ∂(Measure.haar : Measure (AdelicGroupPoints F G))

end Langlands.Global
