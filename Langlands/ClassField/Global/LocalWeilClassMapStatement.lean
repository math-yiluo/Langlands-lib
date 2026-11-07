import Langlands.ClassField.Global.LocalRelativeWeilMap

/-! # Local Weil groups mapped into completed-local class extensions

Proposition definition only. It states that the actual local Weil group of `F_v`
maps into the completed-local class extension of `Gal(E_w/F_v)` by `E_wˣ` at a
local fundamental class, compatibly with Galois projections and with the inverse
of a geometric reciprocity candidate on `W_{E_w}`. Nothing is proved here.
-/

namespace Langlands.ClassField.Global

open NumberField
open scoped NumberField Langlands.Global.AdelicFunctoriality.FiniteExtension
open Langlands.Global.AdelicFunctoriality Langlands.Global.CompletionPadic
open Langlands.ClassFieldTheory.Local

universe u

/-- For an invariant family at the residue prime of `v` satisfying the relative
class-formation laws and the arithmetic normalization, a geometrically normalized
reciprocity candidate `e` of `E_w`, and a local fundamental class `a` of the Galois
extension `E_w / F_v`, there is a continuous homomorphism
`κ : W_{F_v} → CompletionClassExtension v w a` whose `Gal(E_w/F_v)`-image of `κ g`
acts on `E_w` as the Galois image of `g` through `E_w → \bar{F_v}`, and which on
`W_{E_w}` is the inverse of `e` followed by `E_wˣ → CompletionClassExtension v w a`
(Weil–Shafarevich; Tate 1979, §1.2 and §1.4; Artin–Tate, Chapter XV). -/
def LocalWeilClassMapExistenceStatement : Prop :=
  ∀ (F E : Type u) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (v : Langlands.Global.FinitePlace F) (w : Langlands.Global.FinitePlace E)
    [w.asIdeal.LiesOver v.asIdeal]
    [IsGalois (padicField v).Carrier (w.adicCompletion E)]
    (J : InvariantFamily.{u, u} (residuePrime v)),
    J.RelativeClassFormation → J.ArithmeticNormalization →
    ∀ e : LocalFactor.RankOne.ReciprocityCandidate (towerPadicField v w),
      LocalClassField.GeometricWeilReciprocityRelation (towerPadicField v w)
          (towerPadicField v w).canonicalTopologicalData e →
      haveI : FiniteDimensional (padicField v).Carrier (w.adicCompletion E) :=
        FiniteExtension.local_finite
          (show IsDedekindDomain.HeightOneSpectrum (𝓞 F) from v)
          (show IsDedekindDomain.HeightOneSpectrum (𝓞 E) from w)
      ∀ a : CompletionH2 v w,
        IsFundamentalClass (padicField v).Carrier (w.adicCompletion E)
            (J.relative (padicField v) (w.adicCompletion E)) a →
        ∃ κ : Weil.Local.localWeilGroup (padicField v) →ₜ* CompletionClassExtension v w a,
          (∀ (g : Weil.Local.localWeilGroup (padicField v)) (x : w.adicCompletion E),
            RelativeWeilGroup.completionClosureEmbedding v w
                (CompletionClassExtension.projection v w a (κ g) x) =
              AlgEquiv.toAlgHom (Weil.Local.localProjection (padicField v) g)
                (RelativeWeilGroup.completionClosureEmbedding v w x)) ∧
          ∀ y : Weil.Local.localWeilGroup (towerPadicField v w),
            κ (RelativeWeilGroup.completionWeilMap v w y) =
              (CompletionClassExtension.inclusion v w a
                (LocalFactor.RankOne.reciprocityUnits (towerPadicField v w) e y))⁻¹

end Langlands.ClassField.Global
