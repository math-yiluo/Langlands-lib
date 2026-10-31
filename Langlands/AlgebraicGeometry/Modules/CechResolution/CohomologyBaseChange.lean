import Langlands.AlgebraicGeometry.Modules.CechResolution.AffineSectionsBaseChange
import Langlands.AlgebraicGeometry.Modules.CechResolution.Pushforward

/-! # Canonical scalar cohomology base change from actual Čech resolutions -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Langlands.AlgebraicGeometry.Modules.DerivedSections

namespace Langlands.AlgebraicGeometry.Modules.CechResolution

variable {X Y : Scheme.{u}} {R S : CommRingCat.{u}}
  (φ : R ⟶ S) (f : X ⟶ Spec R) (f' : Y ⟶ Spec S)
  (g : Y ⟶ X) (w : g ≫ f = f' ≫ Spec.map φ)
  [IsAffineHom g] [IsSeparated f]
  (M : X.Modules) [M.IsQuasicoherent] (𝒰 : X.OrderedAffineCover)

/-- The actual Čech complexes compute the canonical scalar base-change map,
once their terms are acyclic for the two relative sections functors. -/
theorem isIso_scalarBaseChangeMap_of_cech
    (h : IsPullback g f' f (Spec.map φ)) (hφ : φ.hom.Flat)
    (hK : ∀ i q : ℕ, IsZero ((relativeCohomology f (q + 1)).obj
      ((cechComplex 𝒰 M).X i)))
    (hL : ∀ i q : ℕ, IsZero ((relativeCohomology f' (q + 1)).obj
      ((cechComplex (inverseImageCover g 𝒰) ((Scheme.Modules.pullback g).obj M)).X i)))
    (hM : ∀ q : ℕ, IsZero ((higherDirectImage g (q + 1)).obj
      ((Scheme.Modules.pullback g).obj M)))
    (n : ℕ) : IsIso (scalarBaseChangeMap φ f f' g w M hM n) := by
  let := quasiIso_cechAug 𝒰 M
  let := quasiIso_cechAug (inverseImageCover g 𝒰) ((Scheme.Modules.pullback g).obj M)
  let := quasiIso_pushforward_cechAug g ((Scheme.Modules.pullback g).obj M) 𝒰
  have : QuasiIso (scalarResolutionSectionsBaseChangeMap φ f f' g w
      (cechPullback g (M := M) 𝒰)) :=
    quasiIso_scalarCechSectionsMap_of_isPullback_of_isSeparated g M φ f f' w 𝒰 h
  exact isIso_scalarBaseChangeMap_of_acyclicResolutions φ f f' g w
    (cechAug 𝒰 M)
    (cechAug (inverseImageCover g 𝒰) ((Scheme.Modules.pullback g).obj M))
    (cechPullback g 𝒰) (cechAug_cechPullback g 𝒰) hφ hK hL hM n

/-- The canonical scalar comparison, with its inverse provided by the actual
acyclic Čech resolutions. -/
def scalarCechCohomologyBaseChangeIso
    (h : IsPullback g f' f (Spec.map φ)) (hφ : φ.hom.Flat)
    (hK : ∀ i q : ℕ, IsZero ((relativeCohomology f (q + 1)).obj
      ((cechComplex 𝒰 M).X i)))
    (hL : ∀ i q : ℕ, IsZero ((relativeCohomology f' (q + 1)).obj
      ((cechComplex (inverseImageCover g 𝒰) ((Scheme.Modules.pullback g).obj M)).X i)))
    (hM : ∀ q : ℕ, IsZero ((higherDirectImage g (q + 1)).obj
      ((Scheme.Modules.pullback g).obj M)))
    (n : ℕ) :
    (ModuleCat.extendScalars φ.hom).obj ((relativeCohomology f n).obj M) ≅
      (relativeCohomology f' n).obj ((Scheme.Modules.pullback g).obj M) := by
  have := isIso_scalarBaseChangeMap_of_cech φ f f' g w M 𝒰 h hφ hK hL hM n
  exact asIso (scalarBaseChangeMap φ f f' g w M hM n)

end Langlands.AlgebraicGeometry.Modules.CechResolution
