import Langlands.AlgebraicGeometry.QuasiFiniteAtStalkDimensionStatement

/-! # Proof: stalk dimension at a quasi-finite point -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AlgebraicGeometry

/-- A quasi-finite algebra has Krull dimension at most that of its base. -/
theorem ringKrullDim_le_of_quasiFinite {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.QuasiFinite R S] : ringKrullDim S ≤ ringKrullDim R := by
  have H := Order.krullDim_le_of_krullDim_preimage_le' (m := 0)
    (PrimeSpectrum.comap (algebraMap R S)) (fun _ _ h ↦ Ideal.comap_mono h) (fun p ↦ by
      rw [Order.krullDim_eq_of_orderIso (PrimeSpectrum.preimageOrderIsoFiber R S p),
        ← ringKrullDim, ← Ring.krullDimLE_iff]
      infer_instance)
  simpa [ringKrullDim] using H

/-- Quasi-finiteness of the stalk map at `x` bounds the stalk dimension at `x` by that at
`f x`. -/
theorem quasiFiniteAtStalkDimension : QuasiFiniteAtStalkDimensionStatement.{u} := by
  intro X Y f _ x hx
  let := (f.stalkMap x).hom.toAlgebra
  have : Algebra.QuasiFinite (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) := hx
  exact ringKrullDim_le_of_quasiFinite

end Langlands.AlgebraicGeometry
