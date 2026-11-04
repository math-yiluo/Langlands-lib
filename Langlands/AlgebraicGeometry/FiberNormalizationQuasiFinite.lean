import Langlands.AlgebraicGeometry.FiberNormalizationCoordinates
import Mathlib.RingTheory.ZariskisMainTheorem
import Mathlib.RingTheory.RingHom.QuasiFinite
import Mathlib.RingTheory.TensorProduct.MvPolynomial

/-! # Quasi-finiteness from normalization of a residue-field fibre -/

universe u v w

namespace Langlands.AlgebraicGeometry.SchemeFiberGeometry

open Algebra TensorProduct

/-- Quasi-finiteness on a fixed residue-field fibre reflects to each point of
that fibre for a finite-type morphism over an intermediate algebra. -/
theorem quasiFiniteAt_of_quasiFinite_base_fiber
    {R : Type u} {B : Type v} {S : Type w}
    [CommRing R] [CommRing B] [CommRing S]
    [Algebra R B] [Algebra R S] [Algebra B S] [IsScalarTower R B S]
    [Algebra.FiniteType B S] (p : PrimeSpectrum R) (q : PrimeSpectrum S)
    (hq : q.comap (algebraMap R S) = p)
    (hfin : (Algebra.TensorProduct.map (AlgHom.id p.asIdeal.ResidueField p.asIdeal.ResidueField)
      (IsScalarTower.toAlgHom R B S)).toRingHom.QuasiFinite) :
    Algebra.QuasiFiniteAt B q.asIdeal := by
  let φ : p.asIdeal.Fiber B →ₐ[p.asIdeal.ResidueField] p.asIdeal.Fiber S :=
    Algebra.TensorProduct.map (.id _ _) (IsScalarTower.toAlgHom R B S)
  let := φ.toRingHom.toAlgebra
  have : Algebra.QuasiFinite (p.asIdeal.Fiber B) (p.asIdeal.Fiber S) := hfin
  let eS := PrimeSpectrum.preimageHomeomorphFiber R S p
  let eB := PrimeSpectrum.preimageHomeomorphFiber R B p
  let qF : PrimeSpectrum (p.asIdeal.Fiber S) := eS ⟨q, hq⟩
  have hcomm (z : PrimeSpectrum (p.asIdeal.Fiber S)) :
      (z.comap φ.toRingHom).comap Algebra.TensorProduct.includeRight.toRingHom =
        (z.comap Algebra.TensorProduct.includeRight.toRingHom).comap (algebraMap B S) := by
    rw [← PrimeSpectrum.comap_comp_apply, ← PrimeSpectrum.comap_comp_apply]
    congr 1
  have hinj : Function.Injective
      (PrimeSpectrum.comap (Algebra.TensorProduct.includeRight.toRingHom :
        B →+* p.asIdeal.Fiber B)) := by
    intro a b hab
    apply eB.symm.injective
    exact Subtype.ext hab
  let T := PrimeSpectrum.comap (algebraMap B S) ⁻¹' {q.comap (algebraMap B S)}
  have hRp (z : T) : z.1.comap (algebraMap R S) = p := by
    rw [IsScalarTower.algebraMap_eq R B S, PrimeSpectrum.comap_comp_apply,
      show z.1.comap (algebraMap B S) = q.comap (algebraMap B S) from z.2,
      ← PrimeSpectrum.comap_comp_apply, ← IsScalarTower.algebraMap_eq R B S]
    exact hq
  let a : T → PrimeSpectrum (p.asIdeal.Fiber S) := fun z => eS ⟨z.1, hRp z⟩
  have ha : Continuous a := eS.continuous.comp (continuous_subtype_val.subtype_mk hRp)
  have hainj : Function.Injective a := by
    intro z z' h
    exact Subtype.ext
      (congrArg (fun z : {z : PrimeSpectrum S //
        z.comap (algebraMap R S) = p} => z.val) (eS.injective h))
  have haf (z : T) : (a z).comap φ.toRingHom = qF.comap φ.toRingHom := by
    apply hinj
    rw [hcomm, hcomm]
    have hz := congrArg Subtype.val (eS.symm_apply_apply ⟨z.1, hRp z⟩)
    have hq' := congrArg Subtype.val (eS.symm_apply_apply ⟨q, hq⟩)
    change (a z).comap Algebra.TensorProduct.includeRight.toRingHom = z.1 at hz
    change qF.comap Algebra.TensorProduct.includeRight.toRingHom = q at hq'
    rw [hz, hq']
    exact z.2
  let U := PrimeSpectrum.comap φ.toRingHom ⁻¹' {qF.comap φ.toRingHom}
  let a' : T → U := fun z => ⟨a z, haf z⟩
  have ha' : Continuous a' := ha.subtype_mk haf
  have hinj' : Function.Injective a' := fun _ _ h => hainj (congrArg Subtype.val h)
  have : DiscreteTopology U :=
    isDiscrete_iff_discreteTopology.mp
      (Algebra.QuasiFinite.isDiscrete_comap_preimage_singleton
        (R := p.asIdeal.Fiber B) (S := p.asIdeal.Fiber S) (qF.comap φ.toRingHom))
  apply Algebra.QuasiFiniteAt.of_isOpen_singleton_fiber q
  have hopen := (isOpen_discrete ({a' ⟨q, rfl⟩} : Set U)).preimage ha'
  have hpre : a' ⁻¹' {a' ⟨q, rfl⟩} = {⟨q, rfl⟩} := by
    ext z
    exact hinj'.eq_iff
  rwa [hpre] at hopen

/-- Finiteness of polynomial evaluation on a residue-field fibre implies
quasi-finiteness of the original polynomial map at every point of that fibre. -/
theorem quasiFiniteAt_aeval_of_finite_fiber_aeval
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.FiniteType R S] {n : ℕ} (s : Fin n → S)
    (p : PrimeSpectrum R) (q : PrimeSpectrum S)
    (hq : q.comap (algebraMap R S) = p)
    (hfin : (MvPolynomial.aeval (R := p.asIdeal.ResidueField)
      (fun i => (1 : p.asIdeal.ResidueField) ⊗ₜ[R] s i)).Finite) :
    (MvPolynomial.aeval (R := R) s).toRingHom.QuasiFiniteAt q.asIdeal := by
  let f : MvPolynomial (Fin n) R →ₐ[R] S := MvPolynomial.aeval s
  let := f.toRingHom.toAlgebra
  have : IsScalarTower R (MvPolynomial (Fin n) R) S :=
    IsScalarTower.of_algebraMap_eq fun r => (f.commutes r).symm
  have : Algebra.FiniteType (MvPolynomial (Fin n) R) S :=
    Algebra.FiniteType.of_restrictScalars_finiteType R _ _
  let φ : p.asIdeal.Fiber (MvPolynomial (Fin n) R) →ₐ[p.asIdeal.ResidueField]
      p.asIdeal.Fiber S := Algebra.TensorProduct.map (.id _ _) f
  let e := MvPolynomial.algebraTensorAlgEquiv (σ := Fin n) R p.asIdeal.ResidueField
  have he : φ.comp e.symm.toAlgHom = MvPolynomial.aeval (R := p.asIdeal.ResidueField)
      (fun i => (1 : p.asIdeal.ResidueField) ⊗ₜ[R] s i) := by
    ext i
    simp [φ, e, f]
  apply quasiFiniteAt_of_quasiFinite_base_fiber
    (B := MvPolynomial (Fin n) R) p q hq
  change φ.toRingHom.QuasiFinite
  apply RingHom.QuasiFinite.of_comp (g := e.symm.toAlgHom.toRingHom)
  change (φ.comp e.symm.toAlgHom).toRingHom.QuasiFinite
  rw [he]
  exact RingHom.QuasiFinite.of_finite hfin

/-- Actual normalization coordinates whose original polynomial map is
quasi-finite at every point above the chosen base prime. -/
structure FiberQuasiFiniteCoordinates
    (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]
    (p : PrimeSpectrum R) extends FiberNormalizationCoordinates R S p.asIdeal where
  quasiFiniteAt : ∀ q : PrimeSpectrum S, q.comap (algebraMap R S) = p →
    (MvPolynomial.aeval (R := R) coordinates).toRingHom.QuasiFiniteAt q.asIdeal

/-- Construct quasi-finite polynomial coordinates along the actual nonzero
residue-field fibre of an arbitrary finite-type algebra. -/
noncomputable def fiberQuasiFiniteCoordinates
    (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.FiniteType R S] (p : PrimeSpectrum R)
    [Nontrivial (p.asIdeal.Fiber S)] : FiberQuasiFiniteCoordinates R S p :=
  let d := fiberNormalizationCoordinates R S p.asIdeal
  { toFiberNormalizationCoordinates := d
    quasiFiniteAt := fun q hq =>
      quasiFiniteAt_aeval_of_finite_fiber_aeval d.coordinates p q hq d.finite }

end Langlands.AlgebraicGeometry.SchemeFiberGeometry
