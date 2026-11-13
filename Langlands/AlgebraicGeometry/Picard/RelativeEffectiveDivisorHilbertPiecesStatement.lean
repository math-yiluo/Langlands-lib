import Langlands.AlgebraicGeometry.HQuasiProjective
import Langlands.AlgebraicGeometry.Picard.RelativeEffectiveDivisor
import Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ModulesProjPresentation
import Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_PolarisedAbelianScheme
import Langlands.AnthropicFLT.Definitions.Def_SheafOfModules_MonoidalV2

/-! # Representability of relative effective divisors, with quasi-projective
Hilbert-polynomial pieces -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory

namespace Langlands.AlgebraicGeometry.Picard

/-- Let `A` be a noetherian ring and `f : X ⟶ Spec A` a flat morphism with an invertible module
`𝓛X` whose global sections give a closed immersion into a finite projective space over `A`.
Then there are a separated scheme `D`, locally of finite presentation over `Spec A`, and a
relative effective divisor `W` on `X ×_A D` over `D` with the following properties.

* For every scheme `T` and every `s : T ⟶ Spec A`, pulling back `W` along
  `X ×_A T ⟶ X ×_A D` gives a bijection from the morphisms `T ⟶ D` over `Spec A`
  onto the relative effective divisors on `X ×_A T` over `T`.
* `D` is the disjoint union of open subschemes `U θ`, indexed by `θ ∈ ℚ[t]`, each
  H-quasi-projective over `Spec A`. For every ring `B`, a morphism `g : Spec B ⟶ D` over
  `Spec A` lands in `U θ`
  exactly when, on every geometric fibre of the classified divisor over an algebraically closed
  field, the dimension of the global sections of the `n`-th tensor power of the pullback of
  `𝓛X` equals `θ(n)` for all large `n`. -/
def RelativeEffectiveDivisorHilbertPiecesStatement : Prop :=
  ∀ (A : Type u) [CommRing A] [IsNoetherianRing A] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of A)) (𝓛X : X.Modules),
    Flat f → Scheme.Modules.IsInvertible 𝓛X → Scheme.Modules.ClosedImmersionBySections 𝓛X f →
    ∃ (D : Scheme.{u}) (d : D ⟶ Spec (CommRingCat.of A))
      (W : RelativeEffectiveDivisor (pullback.snd f d)),
      LocallyOfFinitePresentation d ∧ IsSeparated d ∧
      (∀ (T : Scheme.{u}) (s : T ⟶ Spec (CommRingCat.of A)),
        (∀ (g : T ⟶ D) (hg : g ≫ d = s),
          IsRelativeEffectiveCartierIdeal (pullback.snd f s)
            (W.ideal.comap
              (pullback.map f s f d (𝟙 X) g (𝟙 _) (by simp) (by simp [hg])))) ∧
        ∀ I : (pullback f s).IdealSheafData,
          IsRelativeEffectiveCartierIdeal (pullback.snd f s) I →
            ∃! g : T ⟶ D, ∃ hg : g ≫ d = s,
              W.ideal.comap
                (pullback.map f s f d (𝟙 X) g (𝟙 _) (by simp) (by simp [hg])) = I) ∧
      ∃ U : Polynomial ℚ → D.Opens,
        Pairwise (Function.onFun Disjoint U) ∧ (⨆ θ, U θ) = ⊤ ∧
        ∀ θ : Polynomial ℚ, IsHQuasiProjective ((U θ).ι ≫ d) ∧
          ∀ (B : Type u) [CommRing B] (s : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of A))
            (g : Spec (CommRingCat.of B) ⟶ D) (hg : g ≫ d = s)
            (I : (pullback f s).IdealSheafData),
            W.ideal.comap
                (pullback.map f s f d (𝟙 X) g (𝟙 _) (by simp) (by simp [hg])) = I →
              (Set.range g.base ⊆ (U θ : Set D) ↔
                ∀ (k : Type u) [Field k] [IsAlgClosed k] (sk : B →+* k),
                  ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
                    ((Scheme.Modules.geomFibreH0Finrank (I.subschemeι ≫ pullback.snd f s)
                      (Nat.rec (motive := fun _ => I.subscheme.Modules) (𝟙_ I.subscheme.Modules)
                        (fun _ M => M ⊗ (Scheme.Modules.pullback
                          (I.subschemeι ≫ pullback.fst f s)).obj 𝓛X) n) k sk : ℕ) : ℚ) =
                      θ.eval (n : ℚ))

end Langlands.AlgebraicGeometry.Picard
