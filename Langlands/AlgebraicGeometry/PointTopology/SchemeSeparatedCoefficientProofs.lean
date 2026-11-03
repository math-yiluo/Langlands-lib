import Langlands.AlgebraicGeometry.PointTopology.SchemeSeparatedCoefficientStatements

/-! # Injectivity of actual separated scheme points under coefficient change -/

universe u

open CategoryTheory
open _root_.AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.PointTopology

variable (R S T : Type u) [CommRing R] [CommRing S] [CommRing T]
variable [Algebra R S] [Algebra R T]

/-- An injective coefficient map gives a dominant map of test spectra. -/
theorem isDominant_ringTestMap (f : S →ₐ[R] T) (hf : Function.Injective f) :
    IsDominant (ringTestMap R f).left := by
  constructor
  change DenseRange (PrimeSpectrum.comap f.toRingHom)
  apply (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical f.toRingHom).mpr
  rw [(RingHom.injective_iff_ker_eq_bot f.toRingHom).mp hf]
  exact bot_le

variable [_root_.IsReduced S]

/-- Reduced-source maps into separated schemes are determined after a
coefficient inclusion. -/
theorem schemeSeparatedCoefficientInjectivity_proof :
    SchemeSeparatedCoefficientInjectivityProperty R S T := by
  intro X _ f hf p q hpq
  have : IsDominant (ringTestMap R f).left := isDominant_ringTestMap R S T f hf
  let : IsReduced (ringTest R S).left := by
    change IsReduced (Spec (CommRingCat.of S))
    infer_instance
  apply RingPoint.ext
  exact ext_of_isDominant_of_isSeparated X.hom
    ((Over.w p).trans (Over.w q).symm) (ringTestMap R f).left
    (congrArg (fun z : RingPoint R X T => z.left) hpq)

end Langlands.AlgebraicGeometry.PointTopology
