import Langlands.AlgebraicGeometry.FiberNormalizationQuasiFinite
import Langlands.AlgebraicGeometry.QuasiFiniteAtStalkDimensionProof
import Mathlib.RingTheory.TensorProduct.Finite

/-! # Principal polynomial charts and uniform fibre dimension bounds -/

universe u v w

namespace Langlands.AlgebraicGeometry.SchemeFiberGeometry

open Algebra TensorProduct
open P2MW.S_AlgebraicGeometry_exists_smoothProperCurve_opens_hom_comp_eq_of_ringKrullDim_eq_one.P2mNormOpen

private theorem quasiFinite_tensor_map_left
    {R B C A : Type*} [CommRing R] [CommRing B] [CommRing C] [CommRing A]
    [Algebra R B] [Algebra R C] [Algebra R A]
    (f : B →ₐ[R] C) (hf : f.toRingHom.QuasiFinite) :
    (Algebra.TensorProduct.map f (AlgHom.id R A)).toRingHom.QuasiFinite := by
  let := f.toRingHom.toAlgebra
  have := IsScalarTower.of_algebraMap_eq' f.comp_algebraMap.symm
  have : Algebra.QuasiFinite B C := hf
  change (Algebra.TensorProduct.map (Algebra.ofId B C) (AlgHom.id R A)).toRingHom.QuasiFinite
  convert_to (((Algebra.TensorProduct.comm _ _ _).trans
      (Algebra.TensorProduct.cancelBaseChange R B B C A)).toAlgHom.comp
    Algebra.TensorProduct.includeLeft).toRingHom.QuasiFinite
  · ext <;> simp [Algebra.smul_def]
  exact (RingHom.QuasiFinite.of_finite (RingEquiv.finite _)).comp
    (RingHom.quasiFinite_algebraMap.mpr inferInstance)

/-- Extending both algebras' scalars along the original base preserves
quasi-finiteness of their map. -/
theorem quasiFinite_tensor_map_right
    {R B C A : Type*} [CommRing R] [CommRing B] [CommRing C] [CommRing A]
    [Algebra R B] [Algebra R C] [Algebra R A]
    (f : B →ₐ[R] C) (hf : f.toRingHom.QuasiFinite) :
    (Algebra.TensorProduct.map (AlgHom.id R A) f).toRingHom.QuasiFinite := by
  convert_to (((Algebra.TensorProduct.comm R C A).toAlgHom.comp
    (Algebra.TensorProduct.map f (AlgHom.id R A))).comp
      (Algebra.TensorProduct.comm R A B).toAlgHom).toRingHom.QuasiFinite
  · ext <;> simp
  have hCA := RingHom.QuasiFinite.of_finite
    (Algebra.TensorProduct.comm R C A).toRingEquiv.finite
  have hAB := RingHom.QuasiFinite.of_finite
    (Algebra.TensorProduct.comm R A B).toRingEquiv.finite
  exact (hCA.comp (quasiFinite_tensor_map_left f hf)).comp hAB

/-- A quasi-finite polynomial map bounds the total dimension of every
actual residue-field fibre over the original base. -/
theorem fiber_dimension_le_of_quasiFinite_polynomial
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    {n : ℕ} (f : MvPolynomial (Fin n) R →ₐ[R] S)
    (hf : f.toRingHom.QuasiFinite) (p : PrimeSpectrum R) :
    ringKrullDim (p.asIdeal.Fiber S) ≤ (n : WithBot ℕ∞) := by
  let φ : p.asIdeal.Fiber (MvPolynomial (Fin n) R) →ₐ[p.asIdeal.ResidueField]
      p.asIdeal.Fiber S := Algebra.TensorProduct.map (.id _ _) f
  let := φ.toRingHom.toAlgebra
  have : Algebra.QuasiFinite (p.asIdeal.Fiber (MvPolynomial (Fin n) R))
      (p.asIdeal.Fiber S) := quasiFinite_tensor_map_right f hf
  have h := Langlands.AlgebraicGeometry.ringKrullDim_le_of_quasiFinite
    (R := p.asIdeal.Fiber (MvPolynomial (Fin n) R)) (S := p.asIdeal.Fiber S)
  have he : ringKrullDim (p.asIdeal.Fiber (MvPolynomial (Fin n) R)) =
      ringKrullDim (MvPolynomial (Fin n) p.asIdeal.ResidueField) :=
    (MvPolynomial.algebraTensorAlgEquiv R p.asIdeal.ResidueField).toRingEquiv.ringKrullDim
  exact h.trans_eq (he.trans (ringKrullDim_mvPolynomial_fin p.asIdeal.ResidueField n))

/-- Quasi-finiteness at a prime of a finite-type algebra extends to a
principal localization containing that prime. -/
theorem exists_away_quasiFinite_of_quasiFiniteAt
    {B : Type u} {S : Type v} [CommRing B] [CommRing S] [Algebra B S]
    [Algebra.FiniteType B S] (q : PrimeSpectrum S)
    [Algebra.QuasiFiniteAt B q.asIdeal] :
    ∃ r : S, r ∉ q.asIdeal ∧ Algebra.QuasiFinite B (Localization.Away r) := by
  obtain ⟨S', hS', r, hrq, H⟩ :=
    Algebra.QuasiFiniteAt.exists_fg_and_exists_notMem_and_awayMap_bijective
      (R := B) q.asIdeal
  have : Module.Finite B S' := ⟨(Submodule.fg_top _).mpr hS'⟩
  have : Algebra.QuasiFinite B (Localization.Away r) := .trans _ S' _
  exact ⟨r.1, hrq, .of_surjective_algHom (Localization.awayMapₐ S'.val r) H.2⟩

/-- Polynomial coordinates and a principal source neighbourhood containing a
specified point, with a uniform bound on every actual base fibre. -/
structure FiberDimensionPrincipalChart
    (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]
    (q : PrimeSpectrum S) extends
      FiberQuasiFiniteCoordinates R S (q.comap (algebraMap R S)) where
  element : S
  not_mem : element ∉ q.asIdeal
  quasiFinite : (MvPolynomial.aeval (R := R)
    (fun i => algebraMap S (Localization.Away element) (coordinates i))).toRingHom.QuasiFinite
  fiber_dimension_le : ∀ p : PrimeSpectrum R,
    ringKrullDim (p.asIdeal.Fiber (Localization.Away element)) ≤ (rank : WithBot ℕ∞)

/-- Construct a principal polynomial chart at any point of a finite-type
algebra, with rank equal to the total dimension of its original base fibre. -/
noncomputable def fiberDimensionPrincipalChart
    (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.FiniteType R S] (q : PrimeSpectrum S) :
    FiberDimensionPrincipalChart R S q := by
  classical
  apply Classical.choice
  let p := q.comap (algebraMap R S)
  have : Nontrivial (p.asIdeal.Fiber S) :=
    ((PrimeSpectrum.preimageHomeomorphFiber R S p) ⟨q, rfl⟩).nontrivial
  let d := fiberQuasiFiniteCoordinates R S p
  let B := MvPolynomial (Fin d.rank) R
  let f : B →ₐ[R] S := MvPolynomial.aeval d.coordinates
  let := f.toRingHom.toAlgebra
  have : IsScalarTower R B S :=
    IsScalarTower.of_algebraMap_eq fun r => (f.commutes r).symm
  have : Algebra.FiniteType B S := Algebra.FiniteType.of_restrictScalars_finiteType R B S
  have : Algebra.QuasiFiniteAt B q.asIdeal := d.quasiFiniteAt q rfl
  obtain ⟨r, hr, hfin⟩ := exists_away_quasiFinite_of_quasiFiniteAt (B := B) q
  let g : B →ₐ[R] Localization.Away r :=
    MvPolynomial.aeval fun i => algebraMap S (Localization.Away r) (d.coordinates i)
  have hg : g.toRingHom.QuasiFinite := by
    have he : g = (IsScalarTower.toAlgHom R S (Localization.Away r)).comp f := by
      ext i
      simp [g, f]
    rw [he]
    change ((algebraMap S (Localization.Away r)).comp (algebraMap B S)).QuasiFinite
    rw [← IsScalarTower.algebraMap_eq]
    exact RingHom.quasiFinite_algebraMap.mpr hfin
  exact ⟨
    { toFiberQuasiFiniteCoordinates := d
      element := r
      not_mem := hr
      quasiFinite := hg
      fiber_dimension_le := fiber_dimension_le_of_quasiFinite_polynomial g hg }⟩

end Langlands.AlgebraicGeometry.SchemeFiberGeometry
