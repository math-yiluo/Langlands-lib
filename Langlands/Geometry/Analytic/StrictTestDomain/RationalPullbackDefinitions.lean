import Langlands.Geometry.Analytic.StrictTestDomain.Definitions

/-! # Pullback of rational data along bounded algebra maps -/

noncomputable section

universe u

namespace Langlands.Analytic.StrictTestDomain.RationalData

variable {K : Type u} [NormedField K] [IsUltrametricDist K]
  {P Q R : PresentedStrictAffinoidAlgebra K}

/-- Map the rational elements along an actual bounded algebra map.
The absence of common zeros follows by pulling back each spectrum point. -/
def pullback (d : RationalData K P) (φ : BoundedAlgHom K P Q) : RationalData K Q where
  arity := d.arity
  denominator := φ d.denominator
  numerator j := φ (d.numerator j)
  no_common_zero x := d.no_common_zero (BanachSpectrum.comap φ.toBoundedRingHom x)

@[simp]
theorem pullback_arity (d : RationalData K P) (φ : BoundedAlgHom K P Q) :
    (d.pullback φ).arity = d.arity := rfl

@[simp]
theorem pullback_denominator (d : RationalData K P) (φ : BoundedAlgHom K P Q) :
    (d.pullback φ).denominator = φ d.denominator := rfl

@[simp]
theorem pullback_numerator (d : RationalData K P) (φ : BoundedAlgHom K P Q)
    (j : Fin d.arity) :
    (d.pullback φ).numerator j = φ (d.numerator j) := rfl

@[simp]
theorem pullback_id (d : RationalData K P) :
    d.pullback (BoundedAlgHom.id K P) = d := by
  cases d
  rfl

@[simp]
theorem pullback_comp (d : RationalData K P) (φ : BoundedAlgHom K P Q)
    (ψ : BoundedAlgHom K Q R) :
    d.pullback (ψ.comp φ) = (d.pullback φ).pullback ψ := rfl

/-- The rational inequalities pull back along the actual spectrum map. -/
theorem locus_pullback (d : RationalData K P) (φ : BoundedAlgHom K P Q) :
    (d.pullback φ).locus = (BanachSpectrum.comap φ.toBoundedRingHom) ⁻¹' d.locus := rfl

@[simp]
theorem mem_locus_pullback (d : RationalData K P) (φ : BoundedAlgHom K P Q)
    (x : BanachSpectrum Q) :
    x ∈ (d.pullback φ).locus ↔
      BanachSpectrum.comap φ.toBoundedRingHom x ∈ d.locus := Iff.rfl

/-- A test map lands in the pulled-back locus precisely when its composite
lands in the original locus. No representability hypothesis is needed. -/
theorem hasImageIn_pullback_iff (d : RationalData K P) (φ : BoundedAlgHom K P Q)
    (ψ : BoundedAlgHom K Q R) :
    HasImageIn K ψ (d.pullback φ).locus ↔
      HasImageIn K (ψ.comp φ) d.locus := Iff.rfl

end Langlands.Analytic.StrictTestDomain.RationalData
