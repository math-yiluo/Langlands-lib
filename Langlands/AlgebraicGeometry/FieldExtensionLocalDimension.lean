import Langlands.AlgebraicGeometry.FlatOpenLocalDimension
import Langlands.AlgebraicGeometry.FieldExtensionDimensionProof
import Langlands.AlgebraicGeometry.FieldExtensionLocalDimensionStatement

/-! # Local dimension under extension of the ground field -/

noncomputable section

universe u v w

open Set Topology TopologicalSpace
open scoped TensorProduct

namespace Langlands.AlgebraicGeometry.SchemeFiberGeometry

/-- A ground-field extension cannot increase the local dimension at a point
of a finite-type algebra. -/
theorem topologicalKrullDimAt_tensorProduct_le
    (k : Type u) (K : Type v) (A : Type w)
    [Field k] [Field K] [CommRing A] [Algebra k K] [Algebra k A]
    [Algebra.FiniteType k A] (q : PrimeSpectrum (K ⊗[k] A)) :
    topologicalKrullDimAt q ≤
      topologicalKrullDimAt (q.comap Algebra.TensorProduct.includeRight.toRingHom) := by
  let p := q.comap (Algebra.TensorProduct.includeRight (R := k) (A := K)).toRingHom
  obtain ⟨r, hr, hdim⟩ := exists_away_dimension_eq_at A p
  let s : K ⊗[k] A := 1 ⊗ₜ[k] r
  have hs : s ∉ q.asIdeal := hr
  let e := localizationAwayBasicOpenHomeomorph s
  let z := e.symm ⟨q, hs⟩
  have hz : PrimeSpectrum.comap (algebraMap (K ⊗[k] A) (Localization.Away s)) z = q :=
    congrArg Subtype.val (e.apply_symm_apply ⟨q, hs⟩)
  have hlocal : topologicalKrullDimAt z = topologicalKrullDimAt q :=
    (topologicalKrullDimAt_eq_of_isOpenEmbedding
      (PrimeSpectrum.localization_away_isOpenEmbedding (Localization.Away s) s) z).trans
      (congrArg topologicalKrullDimAt hz)
  calc
    topologicalKrullDimAt q = topologicalKrullDimAt z := hlocal.symm
    _ ≤ topologicalKrullDim (PrimeSpectrum (Localization.Away s)) :=
      topologicalKrullDimAt_le z
    _ = ringKrullDim (Localization.Away s) :=
      PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim _
    _ = ringKrullDim (K ⊗[k] Localization.Away r) :=
      (ringKrullDim_eq_of_ringEquiv
        (IsLocalization.Away.tensorProductEquivTMulRight k K r
          (Localization.Away r)).toRingEquiv).symm
    _ = ringKrullDim (Localization.Away r) :=
      (finiteTypeFieldExtensionRingDimensionInvariance k K (Localization.Away r)).symm
    _ = topologicalKrullDimAt p := hdim

/-- Extension of the ground field preserves dimension at every actual prime. -/
theorem topologicalKrullDimAt_tensorProduct_eq
    (k : Type u) (K : Type v) (A : Type w)
    [Field k] [Field K] [CommRing A] [Algebra k K] [Algebra k A]
    [Algebra.FiniteType k A] (q : PrimeSpectrum (A ⊗[k] K)) :
    topologicalKrullDimAt q =
      topologicalKrullDimAt (q.comap (algebraMap A (A ⊗[k] K))) := by
  apply le_antisymm
  · let e := Algebra.TensorProduct.comm k K A
    let q' := q.comap e.toRingHom
    have he : e.toRingHom.comp
        (Algebra.TensorProduct.includeRight (R := k) (A := K)).toRingHom =
        algebraMap A (A ⊗[k] K) := by
      ext a
      simp [e]
    have hp : q'.comap Algebra.TensorProduct.includeRight.toRingHom =
        q.comap (algebraMap A (A ⊗[k] K)) := by
      change q.comap (e.toRingHom.comp _) = _
      rw [he]
    have hq : topologicalKrullDimAt q = topologicalKrullDimAt q' :=
      topologicalKrullDimAt_eq_of_isOpenEmbedding
        (PrimeSpectrum.isHomeomorph_comap_of_bijective e.bijective).isOpenEmbedding q
    exact hq.trans_le ((topologicalKrullDimAt_tensorProduct_le k K A q').trans_eq
      (congrArg topologicalKrullDimAt hp))
  · exact topologicalKrullDimAt_comap_le_of_flat_of_isOpenMap A (A ⊗[k] K)
      PrimeSpectrum.isOpenMap_comap_algebraMap_tensorProduct_of_field q

/-- The same comparison with the field in the left tensor factor. -/
theorem topologicalKrullDimAt_tensorProduct_includeRight_eq
    (k : Type u) (K : Type v) (A : Type w)
    [Field k] [Field K] [CommRing A] [Algebra k K] [Algebra k A]
    [Algebra.FiniteType k A] (q : PrimeSpectrum (K ⊗[k] A)) :
    topologicalKrullDimAt q =
      topologicalKrullDimAt (q.comap Algebra.TensorProduct.includeRight.toRingHom) := by
  let e := Algebra.TensorProduct.comm k A K
  let q' := q.comap e.toRingHom
  have he : e.toRingHom.comp (algebraMap A (A ⊗[k] K)) =
      (Algebra.TensorProduct.includeRight (R := k) (A := K)).toRingHom := by
    ext a
    simp [e]
  have hp : q'.comap (algebraMap A (A ⊗[k] K)) =
      q.comap Algebra.TensorProduct.includeRight.toRingHom := by
    change q.comap (e.toRingHom.comp _) = _
    rw [he]
  have hq : topologicalKrullDimAt q = topologicalKrullDimAt q' :=
    topologicalKrullDimAt_eq_of_isOpenEmbedding
      (PrimeSpectrum.isHomeomorph_comap_of_bijective e.bijective).isOpenEmbedding q
  exact hq.trans ((topologicalKrullDimAt_tensorProduct_eq k K A q').trans
    (congrArg topologicalKrullDimAt hp))

/-- The exact universal local-dimension invariance proposition. -/
theorem finiteTypeFieldExtensionLocalDimensionInvariance :
    FiniteTypeFieldExtensionLocalDimensionInvariance.{u,v,w} := by
  intro k K A _ _ _ _ _ _ q
  exact topologicalKrullDimAt_tensorProduct_includeRight_eq k K A q

end Langlands.AlgebraicGeometry.SchemeFiberGeometry
