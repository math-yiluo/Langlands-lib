import Mathlib.AlgebraicGeometry.Geometrically.Integral
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Noetherian
import Langlands.AlgebraicGeometry.Picard.LineBundle

/-! # The noetherian seesaw for line bundles on a flat proper family -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.Picard

/-- Let `c : X ⟶ Spec R` be proper, flat and geometrically integral, with global functions
commuting with every affine base change `Spec B ⟶ Spec R`. For a locally noetherian scheme `T`
over `Spec R` and two locally free rank-one sheaves `M`, `M'` on `X ×_{Spec R} T`, there is a
closed immersion `ι : Z ⟶ T` such that a morphism `ψ : T' ⟶ T` factors through `ι` exactly when
the pullbacks of `M` and `M'` to `(X ×_{Spec R} T) ×_T T'` are isomorphic over some open
neighbourhood in `T'` of each point of `T'`. -/
def NoetherianLineBundleSeesawStatement : Prop :=
  ∀ {R : Type u} [CommRing R] {X : Scheme.{u}} (c : X ⟶ Spec (CommRingCat.of R))
    [IsProper c] [Flat c] [GeometricallyIntegral c],
    (∀ (B : Type u) [CommRing B] [Algebra R B],
      Function.Bijective
        (pullback.snd c (Spec.map (CommRingCat.ofHom (algebraMap R B)))).appTop) →
    ∀ {T : Scheme.{u}} [IsLocallyNoetherian T] (t : T ⟶ Spec (CommRingCat.of R))
      (M M' : (pullback c t).Modules),
      IsLocallyFreeRankOne M → IsLocallyFreeRankOne M' →
      ∃ (Z : Scheme.{u}) (ι : Z ⟶ T), IsClosedImmersion ι ∧
        ∀ {T' : Scheme.{u}} (ψ : T' ⟶ T),
          (∃ z : T' ⟶ Z, z ≫ ι = ψ) ↔
            ∀ τ : T', ∃ U : T'.Opens, τ ∈ U ∧
              Nonempty
                (((Scheme.Modules.pullback (pullback.fst (pullback.snd c t) ψ)).obj M).restrict
                    (pullback.snd (pullback.snd c t) ψ ⁻¹ᵁ U).ι ≅
                  ((Scheme.Modules.pullback (pullback.fst (pullback.snd c t) ψ)).obj M').restrict
                    (pullback.snd (pullback.snd c t) ψ ⁻¹ᵁ U).ι)

end Langlands.AlgebraicGeometry.Picard
