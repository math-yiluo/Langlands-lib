import Langlands.AlgebraicGeometry.Picard.RelativeEffectiveDivisor
import Langlands.AlgebraicGeometry.Modules.DerivedSections
import Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Langlands.AnthropicFLT.Definitions.Def_SheafOfModules_MonoidalV2
import Mathlib.AlgebraicGeometry.Geometrically.Integral
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Noetherian

/-! # The linear system of an invertible module on a proper flat family with integral fibres -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory

namespace Langlands.AlgebraicGeometry.Picard

open Langlands.AlgebraicGeometry.Modules.DerivedSections

/-- Let `T` be locally noetherian, `g : Y ⟶ T` proper and flat with geometrically integral
fibres, and `M` an invertible module on `Y`. Then there are a proper `T`-scheme `λ : Λ ⟶ T`,
a relative effective divisor `W` on `Y ×_T Λ` over `Λ` and an invertible module `N` on `Λ`
with `O(W) ≅ M_Λ ⊗ N_Λ`, such that for every locally noetherian `T`-scheme `t' : T' ⟶ T`
(Kleiman's convention), pulling `W` back along `T'`-points of `Λ` is a bijection onto the
relative effective divisors `E` on `Y ×_T T'` over `T'` with `O(E) ≅ M_{T'} ⊗ N'_{Y_{T'}}`
for some invertible `N'` on `T'` (Kleiman's `LinSys`). If moreover `H¹(Y_t, M_t) = 0` at
every point `t` of `T`, then `λ` is flat and locally of finite presentation, and it is
surjective when also every `H⁰(Y_t, M_t)` is nonzero. -/
def ProperFlatIntegralLinearSystemStatement : Prop :=
  ∀ (T : Scheme.{u}) [IsLocallyNoetherian T] {Y : Scheme.{u}} (g : Y ⟶ T),
    IsProper g → Flat g → GeometricallyIntegral g →
    ∀ M : Y.Modules, Scheme.Modules.IsInvertible M →
      ∃ (Λ : Scheme.{u}) (l : Λ ⟶ T) (W : RelativeEffectiveDivisor (pullback.snd g l))
        (N : Λ.Modules),
        IsProper l ∧ Scheme.Modules.IsInvertible N ∧
        Nonempty (W.toEffectiveCartierDivisor.lineBundle.obj ≅
          (Scheme.Modules.pullback (pullback.fst g l)).obj M ⊗
            (Scheme.Modules.pullback (pullback.snd g l)).obj N) ∧
        (∀ (T' : Scheme.{u}) [IsLocallyNoetherian T'] (t' : T' ⟶ T)
            (E : (pullback g t').IdealSheafData),
          (∃ (k : T' ⟶ Λ) (hk : k ≫ l = t'),
              W.ideal.comap
                (pullback.map g t' g l (𝟙 Y) k (𝟙 T) (by simp) (by simp [hk])) = E) ↔
            ∃ hE : IsRelativeEffectiveCartierIdeal (pullback.snd g t') E,
              ∃ N' : T'.Modules, Scheme.Modules.IsInvertible N' ∧
                Nonempty ((EffectiveCartierDivisor.lineBundle ⟨E, hE.1⟩).obj ≅
                  (Scheme.Modules.pullback (pullback.fst g t')).obj M ⊗
                    (Scheme.Modules.pullback (pullback.snd g t')).obj N')) ∧
        (∀ (T' : Scheme.{u}) [IsLocallyNoetherian T'] (t' : T' ⟶ T) (k₁ k₂ : T' ⟶ Λ)
            (hk₁ : k₁ ≫ l = t') (hk₂ : k₂ ≫ l = t'),
          W.ideal.comap (pullback.map g t' g l (𝟙 Y) k₁ (𝟙 T) (by simp) (by simp [hk₁])) =
              W.ideal.comap (pullback.map g t' g l (𝟙 Y) k₂ (𝟙 T) (by simp) (by simp [hk₂])) →
            k₁ = k₂) ∧
        ((∀ t : T, IsZero ((relativeCohomology (pullback.snd g (T.fromSpecResidueField t)) 1).obj
            ((Scheme.Modules.pullback (pullback.fst g (T.fromSpecResidueField t))).obj M))) →
          Flat l ∧ LocallyOfFinitePresentation l ∧
            ((∀ t : T, ¬ IsZero
                ((relativeCohomology (pullback.snd g (T.fromSpecResidueField t)) 0).obj
                  ((Scheme.Modules.pullback (pullback.fst g (T.fromSpecResidueField t))).obj M))) →
              Surjective l))

end Langlands.AlgebraicGeometry.Picard
