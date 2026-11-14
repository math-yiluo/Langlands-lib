import Langlands.AlgebraicGeometry.ProjectiveSpace
import Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ModulesProjPresentation
import Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_PolarisedAbelianScheme
import Langlands.AnthropicFLT.Definitions.Def_SheafOfModules_MonoidalV2
import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
import Mathlib.AlgebraicGeometry.Morphisms.Flat

/-! # The Hilbert scheme of a projective flat family on all test schemes, with its
universal closed subscheme and projective Hilbert-polynomial pieces -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory

namespace Langlands.AlgebraicGeometry

/-- Let `A` be a commutative ring and `f : X ⟶ Spec A` a flat morphism, locally of finite
presentation, with an invertible module `𝓛X` whose global sections give a closed immersion
into a finite projective space over `A`. Then there are a scheme `H`, separated and locally of
finite presentation over `Spec A`, and an ideal sheaf `W` on `X ×_A H` with the following
properties.

* For every scheme `T` and every `s : T ⟶ Spec A`, pulling back `W` along
  `X ×_A T ⟶ X ×_A H` gives a bijection from the morphisms `T ⟶ H` over `Spec A` onto the
  ideal sheaves on `X ×_A T` whose closed subscheme is flat and locally of finite presentation
  over `T`.
* `H` is the disjoint union of open subschemes `U θ`, indexed by `θ ∈ ℚ[t]`, each
  H-projective over `Spec A`. For every ring `B`, a morphism `g : Spec B ⟶ H` over `Spec A`
  lands in `U θ` exactly when, on every geometric fibre of the classified closed subscheme over
  an algebraically closed field, the dimension of the global sections of the `n`-th tensor
  power of the pullback of `𝓛X` equals `θ(n)` for all large `n`. -/
def HilbertSchemeUniversalFamilyStatement : Prop :=
  ∀ (A : Type u) [CommRing A] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of A)) (𝓛X : X.Modules),
    Flat f → LocallyOfFinitePresentation f →
    Scheme.Modules.IsInvertible 𝓛X → Scheme.Modules.ClosedImmersionBySections 𝓛X f →
    ∃ (H : Scheme.{u}) (πH : H ⟶ Spec (CommRingCat.of A))
      (W : (pullback f πH).IdealSheafData),
      LocallyOfFinitePresentation πH ∧ IsSeparated πH ∧
      (∀ (T : Scheme.{u}) (s : T ⟶ Spec (CommRingCat.of A)),
        (∀ (g : T ⟶ H) (hg : g ≫ πH = s),
          Flat ((W.comap (pullback.map f s f πH (𝟙 X) g (𝟙 _) (by simp)
              (by simp [hg]))).subschemeι ≫ pullback.snd f s) ∧
          LocallyOfFinitePresentation ((W.comap (pullback.map f s f πH (𝟙 X) g (𝟙 _)
              (by simp) (by simp [hg]))).subschemeι ≫ pullback.snd f s)) ∧
        ∀ I : (pullback f s).IdealSheafData,
          Flat (I.subschemeι ≫ pullback.snd f s) →
          LocallyOfFinitePresentation (I.subschemeι ≫ pullback.snd f s) →
            ∃! g : T ⟶ H, ∃ hg : g ≫ πH = s,
              W.comap (pullback.map f s f πH (𝟙 X) g (𝟙 _) (by simp) (by simp [hg])) = I) ∧
      ∃ U : Polynomial ℚ → H.Opens,
        Pairwise (Function.onFun Disjoint U) ∧ (⨆ θ, U θ) = ⊤ ∧
        ∀ θ : Polynomial ℚ, IsHProjective ((U θ).ι ≫ πH) ∧
          ∀ (B : Type u) [CommRing B] (s : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of A))
            (g : Spec (CommRingCat.of B) ⟶ H) (hg : g ≫ πH = s)
            (I : (pullback f s).IdealSheafData),
            W.comap (pullback.map f s f πH (𝟙 X) g (𝟙 _) (by simp) (by simp [hg])) = I →
              (Set.range g.base ⊆ (U θ : Set H) ↔
                ∀ (k : Type u) [Field k] [IsAlgClosed k] (sk : B →+* k),
                  ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
                    ((Scheme.Modules.geomFibreH0Finrank (I.subschemeι ≫ pullback.snd f s)
                      (Nat.rec (motive := fun _ => I.subscheme.Modules) (𝟙_ I.subscheme.Modules)
                        (fun _ M => M ⊗ (Scheme.Modules.pullback
                          (I.subschemeι ≫ pullback.fst f s)).obj 𝓛X) n) k sk : ℕ) : ℚ) =
                      θ.eval (n : ℚ))

end Langlands.AlgebraicGeometry
