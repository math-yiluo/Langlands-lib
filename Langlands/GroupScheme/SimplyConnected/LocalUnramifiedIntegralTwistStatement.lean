import Langlands.GroupScheme.SimplyConnected.Basic
import Langlands.GroupScheme.LocalUnramifiedIntegralCocycle
import Langlands.GroupScheme.GaloisPointTower
import Langlands.Galois.Local.SeparableInertiaDefinitions
import Mathlib.NumberTheory.LocalField.Basic

/-! # Unramified simply connected cocycles become integral after a twist -/

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj ValuativeRel

namespace Langlands.GroupScheme

/-- **Twisting unramified cocycles into an Iwahori model** (the building step of Kaletha–Prasad,
Theorems 10.6.1 and 10.6.4). Let `F` be a nonarchimedean local field, `L` the inertia fixed field
of `F` in its separable closure and `G` a semisimple simply connected group over `F`. There is a
smooth integral model `M` of `G` over `𝒪[F]` with connected special fibre such that, for every
finite Galois extension `E/F` with an `F`-embedding into `L` and every crossed homomorphism
`c : Gal(E/F) → G(E)`, some `h ∈ G(L)` makes all the twisted values
`h⁻¹ · c(σ|E) · σ(h)`, `σ ∈ Gal(L/F)`, have integral coordinates for `M`. -/
def LocalSimplyConnectedUnramifiedIntegralTwistStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom],
    IsSimplyConnected G →
    ∃ M : IntegralModel 𝒪[F] F G, M.IsSmooth ∧
      ConnectedSpace ((GroupScheme.baseChange (Spec.algebraMap 𝒪[F] 𝓀[F])).obj M.group).X.left ∧
      ∀ (E : Type u) [Field E] [Algebra F E] [FiniteDimensional F E] [IsGalois F E]
        [Algebra E (LocalGalois.Separable.inertiaFixedField F)]
        [IsScalarTower F E (LocalGalois.Separable.inertiaFixedField F)]
        (c : (E ≃ₐ[F] E) → G.affinePoints (CommAlgCat.of F E)),
        (∀ σ τ, c (σ * τ) = c σ * GaloisPoint.conjugate F E G σ (c τ)) →
        ∃ h : G.affinePoints (CommAlgCat.of F (LocalGalois.Separable.inertiaFixedField F)),
          ∀ σ : LocalGalois.Separable.inertiaFixedField F ≃ₐ[F]
              LocalGalois.Separable.inertiaFixedField F,
            M.HasIntegralCoordinates (LocalGalois.Separable.inertiaFixedField F)
              (h⁻¹ *
                GaloisPoint.relativeExtend F E (LocalGalois.Separable.inertiaFixedField F) G
                  (c (σ.restrictNormal E)) *
                GaloisPoint.conjugate F (LocalGalois.Separable.inertiaFixedField F) G σ h)

end Langlands.GroupScheme
