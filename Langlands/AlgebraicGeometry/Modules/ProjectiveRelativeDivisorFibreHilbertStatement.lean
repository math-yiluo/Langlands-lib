import Langlands.AlgebraicGeometry.Modules.ProperFlatFibreCohomologySemicontinuityStatement
import Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ModulesProjPresentation
import Langlands.AnthropicFLT.Definitions.Def_SheafOfModules_Monoidal
import Langlands.AlgebraicGeometry.Picard.RelativeEffectiveDivisor
import Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_PolarisedAbelianScheme
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-! # Hilbert functions of relative effective divisors on geometric fibres -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory

namespace Langlands.AlgebraicGeometry.Modules

open Langlands.AlgebraicGeometry.Picard

/-- Let `A` be noetherian, `f : X ⟶ Spec A` proper and flat, and `𝓛X` an invertible module with
a projective presentation of dimension `N` whose morphism to `ℙᴺ_A` is a closed immersion
(`O_X(1)`). Let `B` be noetherian, `s : Spec B ⟶ Spec A`, and `I` a relative effective Cartier
ideal on `X_B = X ×_{Spec A} Spec B` over `Spec B`, with subscheme `E` and ideal module
`K = ker(O_{X_B} → O_E)`. Let `k` be an algebraically closed field, `sk : B →+* k`, and `t` the
image in `Spec B` of the point of `Spec k`. Then for all large `n`,
`dim_k H⁰(E_k, O_E(n)) = χ(O_{X_t}(n)) - χ(K_t(n))`, where `E_k` is the geometric fibre of `E`
over `sk` and the Euler characteristics are those of the fibre `X_t` over `κ(t)`. The twists
`M(n) = M ⊗ 𝓛^{⊗ n}` are right-associated FLT tensor powers written with `Nat.rec`, for the
pullbacks `𝓛` of `𝓛X` to `E` and to `X_B`. -/
def ProjectiveRelativeDivisorFibreHilbertStatement : Prop :=
  ∀ (A : Type u) [CommRing A] [IsNoetherianRing A] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of A)) (𝓛X : X.Modules) (N : ℕ)
    (𝔓 : 𝓛X.ProjPresentation f N),
    IsProper f → Flat f → Scheme.Modules.IsInvertible 𝓛X → IsClosedImmersion 𝔓.toProj →
    ∀ (B : Type u) [CommRing B] [IsNoetherianRing B]
      (s : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of A))
      (I : (pullback f s).IdealSheafData),
      IsRelativeEffectiveCartierIdeal (pullback.snd f s) I →
      ∀ (k : Type u) [Field k] [IsAlgClosed k] (sk : B →+* k),
        ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
          ((Scheme.Modules.geomFibreH0Finrank (I.subschemeι ≫ pullback.snd f s)
              (Nat.rec (motive := fun _ => I.subscheme.Modules) (𝟙_ I.subscheme.Modules)
                (fun _ M => M ⊗ (Scheme.Modules.pullback
                  (I.subschemeι ≫ pullback.fst f s)).obj 𝓛X) n) k sk : ℕ) : ℤ) =
            fibreEulerCharacteristic (pullback.snd f s)
                ((Spec.map (CommRingCat.ofHom sk)) (IsLocalRing.closedPoint k))
                (Nat.rec (motive := fun _ => (pullback f s).Modules) (𝟙_ (pullback f s).Modules)
                  (fun _ M => M ⊗ (Scheme.Modules.pullback (pullback.fst f s)).obj 𝓛X) n) -
              fibreEulerCharacteristic (pullback.snd f s)
                ((Spec.map (CommRingCat.ofHom sk)) (IsLocalRing.closedPoint k))
                (Nat.rec (motive := fun _ => (pullback f s).Modules)
                  (StructureKernelModule.kernelModule I.subschemeι)
                  (fun _ M => M ⊗ (Scheme.Modules.pullback (pullback.fst f s)).obj 𝓛X) n)

end Langlands.AlgebraicGeometry.Modules
