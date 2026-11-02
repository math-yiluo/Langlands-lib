import Langlands.AlgebraicGeometry.Modules.RelativeFlatness
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Noetherian

/-! # Actual noetherian models for two modules on a proper scheme -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.Modules

/-- A noetherian model over an affine base, including the actual Cartesian
square and ordinary module-pullback isomorphisms. Only the target model is
required to be flat over the model base. -/
def HasAffineNoetherianModel {R : CommRingCat.{u}} {Y : Scheme.{u}}
    (p : Y ⟶ Spec R) (M N : Y.Modules) : Prop :=
  ∃ (R₀ : CommRingCat.{u}) (_ : IsNoetherianRing R₀) (φ : R₀ ⟶ R)
    (Y₀ : Scheme.{u}) (p₀ : Y₀ ⟶ Spec R₀) (q : Y ⟶ Y₀)
    (M₀ N₀ : Y₀.Modules),
    IsProper p₀ ∧ LocallyOfFinitePresentation p₀ ∧
    M₀.IsFinitePresentation ∧ N₀.IsFinitePresentation ∧ IsFlatOver p₀ N₀ ∧
    IsPullback q p p₀ (Spec.map φ) ∧
    Nonempty ((Scheme.Modules.pullback q).obj M₀ ≅ M) ∧
    Nonempty ((Scheme.Modules.pullback q).obj N₀ ≅ N)

namespace HasAffineNoetherianModel

/-- Changing either of the actual modules by an isomorphism preserves a model. -/
lemma of_iso {R : CommRingCat.{u}} {Y : Scheme.{u}} {p : Y ⟶ Spec R}
    {M N M' N' : Y.Modules} (h : HasAffineNoetherianModel p M N)
    (eM : M ≅ M') (eN : N ≅ N') : HasAffineNoetherianModel p M' N' := by
  obtain ⟨R₀, hR₀, φ, Y₀, p₀, q, M₀, N₀, hp₀, hfp, hM₀, hN₀,
    hflat, hcart, ⟨eM₀⟩, ⟨eN₀⟩⟩ := h
  exact ⟨R₀, hR₀, φ, Y₀, p₀, q, M₀, N₀, hp₀, hfp, hM₀, hN₀,
    hflat, hcart, ⟨eM₀ ≪≫ eM⟩, ⟨eN₀ ≪≫ eN⟩⟩

end HasAffineNoetherianModel

end Langlands.AlgebraicGeometry.Modules
