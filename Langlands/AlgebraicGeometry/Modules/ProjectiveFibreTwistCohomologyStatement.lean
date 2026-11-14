import Langlands.AlgebraicGeometry.Modules.ProperFlatFibreCohomologySemicontinuityStatement
import Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ModulesProjPresentation
import Langlands.AnthropicFLT.Definitions.Def_SheafOfModules_Monoidal
import Mathlib.Algebra.Polynomial.Eval.Defs

/-! # Cohomology of large twists on the fibres of a projective flat family -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory

namespace Langlands.AlgebraicGeometry.Modules

/-- The twist `F ⊗ 𝓛^{⊗ n}`, with right-associated FLT tensor products:
`F ⊗ 𝓛^{⊗ 0} = F` and `F ⊗ 𝓛^{⊗ (n + 1)} = (F ⊗ 𝓛^{⊗ n}) ⊗ 𝓛`. -/
noncomputable abbrev twist {X : Scheme.{u}} (𝓛 F : X.Modules) (n : ℕ) : X.Modules :=
  Nat.rec (motive := fun _ => X.Modules) F (fun _ M => M ⊗ 𝓛) n

/-- Let `A` be noetherian, `f : X ⟶ Spec A` proper and flat, and `𝓛X` an invertible module with
a projective presentation `𝔓` of dimension `N` whose morphism to `ℙᴺ_A` is a closed immersion.
Let `T` be a locally noetherian scheme over `Spec A`, `F` an invertible module on
`X_T = X ×_{Spec A} T`, and write `F(n) = F ⊗ 𝓛^{⊗ n}` for the pullback `𝓛` of `𝓛X` to `X_T`.
Then, on the fibres `X_t` of `X_T ⟶ T`:

* every point of `T` has a neighbourhood `V` and an `n₀` with `Hᵖ(X_{t'}, F(n)_{t'}) = 0` for all
  `t' ∈ V`, `n ≥ n₀` and `p > 0`;
* if the fibre `X_t` is nonempty, then `H⁰(X_t, F(n)_t) ≠ 0` for all large `n`;
* `n ↦ χ(F(n)_t)` is given by a rational polynomial of degree at most `N`. -/
def ProjectiveFibreTwistCohomologyStatement : Prop :=
  ∀ (A : Type u) [CommRing A] [IsNoetherianRing A] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of A)) (𝓛X : X.Modules) (N : ℕ)
    (𝔓 : 𝓛X.ProjPresentation f N),
    IsProper f → Flat f → Scheme.Modules.IsInvertible 𝓛X → IsClosedImmersion 𝔓.toProj →
    ∀ (T : Scheme.{u}) [IsLocallyNoetherian T] (s : T ⟶ Spec (CommRingCat.of A))
      (F : (pullback f s).Modules), Scheme.Modules.IsInvertible F →
      (∀ t : T, ∃ V : T.Opens, t ∈ V ∧ ∃ n₀ : ℕ, ∀ t' ∈ V, ∀ n p : ℕ, n₀ ≤ n → 0 < p →
        IsZero (fibreCohomology (pullback.snd f s) t'
          (twist ((Scheme.Modules.pullback (pullback.fst f s)).obj 𝓛X) F n) p)) ∧
      (∀ t : T, Nonempty (pullback (C := Scheme.{u}) (pullback.snd f s) (T.fromSpecResidueField t)) →
        ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
          ¬ IsZero (fibreCohomology (pullback.snd f s) t
            (twist ((Scheme.Modules.pullback (pullback.fst f s)).obj 𝓛X) F n) 0)) ∧
      (∀ t : T, ∃ P : Polynomial ℚ, P.natDegree ≤ N ∧ ∀ n : ℕ,
        ((fibreEulerCharacteristic (pullback.snd f s) t
          (twist ((Scheme.Modules.pullback (pullback.fst f s)).obj 𝓛X) F n) : ℤ) : ℚ) =
            P.eval (n : ℚ))

end Langlands.AlgebraicGeometry.Modules
