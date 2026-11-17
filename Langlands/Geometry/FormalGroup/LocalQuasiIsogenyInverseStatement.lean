import Langlands.Geometry.FormalGroup.RationalSectionIso

/-! # The remaining inverse theorem for actual local quasi-isogenies -/

noncomputable section
universe u v
namespace Langlands.FormalGroup.ModuleLaw
open TopologicalSpace AlgebraicGeometry
variable {O : Type u} [CommRing O]
variable {R : Type v} [CommRing R] [Algebra O R]
variable {σ τ : Type} [Finite σ] [Finite τ]

/-- Every actual local quasi-isogeny has a unique actual invertible-section
lift, and the reverse section satisfies the same local scalar-isogeny condition.
The scalar and divisibility hypotheses are retained inside LocalQuasiIsogeny. -/
def LocalQuasiIsogenyInverseStatement (F : Type v) [Field F] [Algebra O F]
    (π : O) (M : ModuleLaw O R σ) (N : ModuleLaw O R τ) : Prop :=
  ∀ (U : Opens (PrimeSpectrum R)) (z : LocalQuasiIsogeny F π M N U),
    ∃! e : RationalSectionIso F M N U,
      e.hom = z.val ∧ RationalSection.IsLocallyScalarIsogeny π e.inv

end Langlands.FormalGroup.ModuleLaw
