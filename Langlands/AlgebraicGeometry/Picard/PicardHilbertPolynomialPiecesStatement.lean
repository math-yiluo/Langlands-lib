import Langlands.AlgebraicGeometry.Picard.RelativeEffectiveDivisor
import Langlands.AlgebraicGeometry.Modules.DerivedSections
import Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ModulesProjPresentation
import Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_PolarisedAbelianScheme
import Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Langlands.AnthropicFLT.Definitions.Def_SheafOfModules_MonoidalV2
import Mathlib.AlgebraicGeometry.Geometrically.Integral
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Noetherian

/-! # Open pieces of invertible modules on a projective flat family, by Hilbert polynomials
and vanishing of higher cohomology -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory

namespace Langlands.AlgebraicGeometry.Picard

open Langlands.AlgebraicGeometry.Modules.DerivedSections

/-- Let `A` be a noetherian ring, `f : X ⟶ Spec A` proper and flat with geometrically integral
fibres, and `𝓛X` an invertible module on `X` whose global sections give a closed immersion into
a finite projective space over `A` (so `𝓛X = O_X(1)`). Write `L(m) = L ⊗ O(1)^{⊗m}`.

Then there are an index type `κ`, polynomials `θ c m`, and for every scheme `T` over `Spec A`,
every module `L` on `X_T` and every `(c, m)` an open `U T s L c m` of `T`, such that, for
locally noetherian `T` and invertible `L`:

* `U` depends only on the class of `L` modulo pullbacks of invertible modules on `T`;
* `U` is compatible with base change along every morphism of locally noetherian schemes;
* `U` increases with `m`, is disjoint for distinct `c`, and the `U T s L c m` cover `T`;
* if `U T s L c m = T`, then `H¹(X_t, L_t(m)) = 0` and `H⁰(X_t, L_t(m)) ≠ 0` at every point `t`;
* over a noetherian affine `Spec B` with `U = Spec B`, every relative effective divisor `E` on
  `X_B` with `O(E) ≅ L(m) ⊗ N_{X_B}` has, on every geometric fibre, Hilbert polynomial `θ c m`
  with respect to `O(1)`, measured as `dim H⁰(E_k, O(n))` for all large `n`.

This is the open decomposition of the Picard functor into the pieces `P^φ_m` in the proof of
Kleiman's Theorem 4.8, with the additional condition `H⁰(X_t, L_t(m)) ≠ 0`. -/
def PicardHilbertPolynomialPiecesStatement : Prop :=
  ∀ (A : Type u) [CommRing A] [IsNoetherianRing A] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of A)) (𝓛X : X.Modules),
    IsProper f → Flat f → GeometricallyIntegral f →
    Scheme.Modules.IsInvertible 𝓛X → Scheme.Modules.ClosedImmersionBySections 𝓛X f →
    ∃ (κ : Type) (θ : κ → ℕ → Polynomial ℚ)
      (U : ∀ (T : Scheme.{u}) (s : T ⟶ Spec (CommRingCat.of A)),
        (pullback f s).Modules → κ → ℕ → T.Opens),
      -- invariance under twisting by invertible modules from the base
      (∀ (T : Scheme.{u}) [IsLocallyNoetherian T] (s : T ⟶ Spec (CommRingCat.of A))
          (L L' : (pullback f s).Modules) (N : T.Modules),
          Scheme.Modules.IsInvertible L → Scheme.Modules.IsInvertible L' →
          Scheme.Modules.IsInvertible N →
          Nonempty (L ≅ L' ⊗ (Scheme.Modules.pullback (pullback.snd f s)).obj N) →
          ∀ (c : κ) (m : ℕ), U T s L c m = U T s L' c m) ∧
      -- base change
      (∀ (T T' : Scheme.{u}) [IsLocallyNoetherian T] [IsLocallyNoetherian T']
          (s : T ⟶ Spec (CommRingCat.of A)) (h : T' ⟶ T) (L : (pullback f s).Modules),
          Scheme.Modules.IsInvertible L → ∀ (c : κ) (m : ℕ),
            U T' (h ≫ s) ((Scheme.Modules.pullback
                (pullback.map f (h ≫ s) f s (𝟙 X) h (𝟙 _) (by simp) (by simp))).obj L) c m =
              h ⁻¹ᵁ U T s L c m) ∧
      -- increasing in `m`, disjoint in `c`, covering
      (∀ (T : Scheme.{u}) [IsLocallyNoetherian T] (s : T ⟶ Spec (CommRingCat.of A))
          (L : (pullback f s).Modules), Scheme.Modules.IsInvertible L →
          (∀ (c : κ) (m : ℕ), U T s L c m ≤ U T s L c (m + 1)) ∧
          (∀ (c c' : κ) (m m' : ℕ), c ≠ c' → Disjoint (U T s L c m) (U T s L c' m')) ∧
          (⨆ (c : κ) (m : ℕ), U T s L c m) = ⊤) ∧
      -- fibrewise cohomology of `L(m)` on a whole piece
      (∀ (T : Scheme.{u}) [IsLocallyNoetherian T] (s : T ⟶ Spec (CommRingCat.of A))
          (L : (pullback f s).Modules), Scheme.Modules.IsInvertible L →
          ∀ (c : κ) (m : ℕ), U T s L c m = ⊤ → ∀ t : T,
            IsZero ((relativeCohomology
                (pullback.snd (pullback.snd f s) (T.fromSpecResidueField t)) 1).obj
              ((Scheme.Modules.pullback
                  (pullback.fst (pullback.snd f s) (T.fromSpecResidueField t))).obj
                (Nat.rec (motive := fun _ => (pullback f s).Modules) L
                  (fun _ M => M ⊗ (Scheme.Modules.pullback (pullback.fst f s)).obj 𝓛X) m))) ∧
            ¬ IsZero ((relativeCohomology
                (pullback.snd (pullback.snd f s) (T.fromSpecResidueField t)) 0).obj
              ((Scheme.Modules.pullback
                  (pullback.fst (pullback.snd f s) (T.fromSpecResidueField t))).obj
                (Nat.rec (motive := fun _ => (pullback f s).Modules) L
                  (fun _ M => M ⊗ (Scheme.Modules.pullback (pullback.fst f s)).obj 𝓛X) m)))) ∧
      -- Hilbert polynomial of the divisors in the linear system of `L(m)`
      (∀ (B : Type u) [CommRing B] [IsNoetherianRing B]
          (s : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of A))
          (L : (pullback f s).Modules), Scheme.Modules.IsInvertible L →
          ∀ (c : κ) (m : ℕ), U (Spec (CommRingCat.of B)) s L c m = ⊤ →
          ∀ (I : (pullback f s).IdealSheafData)
            (hI : IsRelativeEffectiveCartierIdeal (pullback.snd f s) I)
            (N : (Spec (CommRingCat.of B)).Modules), Scheme.Modules.IsInvertible N →
            Nonempty ((EffectiveCartierDivisor.lineBundle ⟨I, hI.1⟩).obj ≅
              Nat.rec (motive := fun _ => (pullback f s).Modules) L
                  (fun _ M => M ⊗ (Scheme.Modules.pullback (pullback.fst f s)).obj 𝓛X) m ⊗
                (Scheme.Modules.pullback (pullback.snd f s)).obj N) →
            ∀ (k : Type u) [Field k] [IsAlgClosed k] (sk : B →+* k),
              ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
                ((Scheme.Modules.geomFibreH0Finrank (I.subschemeι ≫ pullback.snd f s)
                  (Nat.rec (motive := fun _ => I.subscheme.Modules) (𝟙_ I.subscheme.Modules)
                    (fun _ M => M ⊗ (Scheme.Modules.pullback
                      (I.subschemeι ≫ pullback.fst f s)).obj 𝓛X) n) k sk : ℕ) : ℚ) =
                  (θ c m).eval (n : ℚ))

end Langlands.AlgebraicGeometry.Picard
