import Langlands.AlgebraicGeometry.Modules.DerivedSections
import Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.ResidueField
import Mathlib.LinearAlgebra.Dimension.Finrank

/-! # Semicontinuity of fibre cohomology for proper flat morphisms -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.Modules

open DerivedSections

variable {Y T : Scheme.{u}}

/-- The fibre `Y_t = Y ×_T Spec κ(t)` of `g : Y ⟶ T` over a point `t`, as a scheme over
`Spec κ(t)`. -/
noncomputable abbrev fibreMap (g : Y ⟶ T) (t : T) :
    pullback g (T.fromSpecResidueField t) ⟶ Spec (T.residueField t) :=
  pullback.snd g (T.fromSpecResidueField t)

/-- The restriction `F_t` of a module `F` on `Y` to the fibre `Y_t`. -/
noncomputable abbrev fibreModule (g : Y ⟶ T) (t : T) (F : Y.Modules) :
    (pullback g (T.fromSpecResidueField t)).Modules :=
  (Scheme.Modules.pullback (pullback.fst g (T.fromSpecResidueField t))).obj F

/-- The fibre cohomology `Hᵖ(Y_t, F_t)`, a `κ(t)`-module. -/
noncomputable abbrev fibreCohomology (g : Y ⟶ T) (t : T) (F : Y.Modules) (p : ℕ) :
    ModuleCat.{u} (T.residueField t) :=
  (relativeCohomology (fibreMap g t) p).obj (fibreModule g t F)

/-- The dimension `dim_{κ(t)} Hᵖ(Y_t, F_t)` (zero if the space is infinite dimensional). -/
noncomputable abbrev fibreCohomologyDim (g : Y ⟶ T) (t : T) (F : Y.Modules) (p : ℕ) : ℕ :=
  Module.finrank (T.residueField t) (fibreCohomology g t F p)

/-- The Euler characteristic `χ(F_t) = ∑ₚ (-1)ᵖ dim Hᵖ(Y_t, F_t)` of the fibre, as a finite sum
(zero if infinitely many terms are nonzero). -/
noncomputable def fibreEulerCharacteristic (g : Y ⟶ T) (t : T) (F : Y.Modules) : ℤ :=
  ∑ᶠ p : ℕ, (-1 : ℤ) ^ p * (fibreCohomologyDim g t F p : ℤ)

/-- Let `g : Y ⟶ T` be a proper flat morphism to a locally noetherian scheme and `F` an
invertible module on `Y`. Then

* every fibre cohomology space `Hᵖ(Y_t, F_t)` is finite dimensional over `κ(t)`;
* locally on `T`, these spaces vanish in all degrees above one bound;
* for every `p` and `r`, the set of points `t` with `dim Hᵖ(Y_t, F_t) < r` is open
  (upper semicontinuity);
* the Euler characteristic `t ↦ χ(F_t)` is locally constant. -/
def ProperFlatFibreCohomologySemicontinuityStatement : Prop :=
  ∀ (T Y : Scheme.{u}) [IsLocallyNoetherian T] (g : Y ⟶ T), IsProper g → Flat g →
    ∀ F : Y.Modules, Scheme.Modules.IsInvertible F →
      (∀ (t : T) (p : ℕ), Module.Finite (T.residueField t) (fibreCohomology g t F p)) ∧
      (∀ t : T, ∃ V : T.Opens, t ∈ V ∧ ∃ b : ℕ, ∀ t' ∈ V, ∀ p : ℕ, b ≤ p →
        IsZero (fibreCohomology g t' F p)) ∧
      (∀ p r : ℕ, IsOpen {t : T | fibreCohomologyDim g t F p < r}) ∧
      (∀ t : T, ∃ V : T.Opens, t ∈ V ∧ ∀ t' ∈ V,
        fibreEulerCharacteristic g t' F = fibreEulerCharacteristic g t F)

end Langlands.AlgebraicGeometry.Modules
