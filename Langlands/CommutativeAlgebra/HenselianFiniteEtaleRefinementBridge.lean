import Langlands.CommutativeAlgebra.HenselianFiniteEtaleRefinementStatement
import Mathlib.RingTheory.Ideal.Over

/-! # Algebra and spectrum interfaces for Henselian finite étale refinement -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.CommutativeAlgebra

/-- The algebraic refinement interface: an étale algebra with a prime over the
closed point maps to a local finite étale algebra over the same base. -/
def LocalFiniteEtaleRefinementRingStatement : Prop :=
  ∀ (R : Type u) [CommRing R] [HenselianLocalRing R]
    (A : Type u) [CommRing A] [Algebra R A] [Algebra.Etale R A]
    (q : Ideal A) [q.IsPrime] [q.LiesOver (IsLocalRing.maximalIdeal R)],
    ∃ (R' : Type u) (_ : CommRing R') (_ : IsLocalRing R') (_ : Algebra R R'),
      Algebra.Etale R R' ∧ Module.Finite R R' ∧ Nonempty (A →ₐ[R] R')

/-- Convert algebraic finite étale refinement into the exact affine scheme
statement, including its factorization equation. -/
theorem henselianFiniteEtaleRefinement_of_ring
    (h : LocalFiniteEtaleRefinementRingStatement.{u}) :
    HenselianFiniteEtaleRefinementStatement.{u} := by
  intro R _ _ A _ f hf hx
  let φ : CommRingCat.of R ⟶ CommRingCat.of A := Spec.preimage f
  have hφ : Spec.map φ = f := Spec.map_preimage _
  let : Algebra R A := φ.hom.toAlgebra
  have : Algebra.Etale R A := by
    exact RingHom.Etale.toAlgebra (HasRingHomProperty.Spec_iff.mp (hφ.symm ▸ hf))
  obtain ⟨x, hx⟩ := hx
  have hq : x.asIdeal.comap (algebraMap R A) = IsLocalRing.maximalIdeal R := by
    have hx' : Spec.map φ x = IsLocalRing.closedPoint R := by
      rw [hφ]
      exact hx
    exact congrArg PrimeSpectrum.asIdeal hx'
  have : x.asIdeal.IsPrime := x.isPrime
  have : x.asIdeal.LiesOver (IsLocalRing.maximalIdeal R) := ⟨hq.symm⟩
  obtain ⟨R', _, _, _, hEt, hfin, ⟨ψ⟩⟩ := h R A x.asIdeal
  refine ⟨R', inferInstance, inferInstance, inferInstance, hEt, hfin,
    Spec.map (CommRingCat.ofHom ψ.toRingHom), ?_⟩
  have hcomp : φ ≫ CommRingCat.ofHom ψ.toRingHom =
      CommRingCat.ofHom (algebraMap R R') := by
    ext r
    exact ψ.commutes r
  rw [← hφ, ← Spec.map_comp, hcomp]

/-- Conversely, affine scheme refinement gives the algebraic interface. -/
theorem localFiniteEtaleRefinementRing_of_scheme
    (h : HenselianFiniteEtaleRefinementStatement.{u}) :
    LocalFiniteEtaleRefinementRingStatement.{u} := by
  intro R _ _ A _ _ _ q _ _
  let f := Spec.algebraMap R A
  have hf : Etale f := by
    exact HasRingHomProperty.Spec_iff.mpr (RingHom.etale_algebraMap.mpr inferInstance)
  have hx : IsLocalRing.closedPoint R ∈ Set.range f := by
    refine ⟨⟨q, inferInstance⟩, ?_⟩
    apply PrimeSpectrum.ext
    exact (q.over_def (IsLocalRing.maximalIdeal R)).symm
  obtain ⟨R', _, _, _, hEt, hfin, g, hg⟩ := h R A f hf hx
  let ψ : CommRingCat.of A ⟶ CommRingCat.of R' := Spec.preimage g
  have hψ : Spec.map ψ = g := Spec.map_preimage _
  have hcomp : CommRingCat.ofHom (algebraMap R A) ≫ ψ =
      CommRingCat.ofHom (algebraMap R R') := by
    apply Spec.map_injective
    rw [Spec.map_comp, hψ]
    exact hg
  let ψA : A →ₐ[R] R' :=
    { toRingHom := ψ.hom
      commutes' := fun r =>
        congrArg (fun k : CommRingCat.of R ⟶ CommRingCat.of R' => k.hom r) hcomp }
  exact ⟨R', inferInstance, inferInstance, inferInstance, hEt, hfin, ⟨ψA⟩⟩

/-- The algebraic and affine scheme formulations have exactly the same scope. -/
theorem localFiniteEtaleRefinementRing_iff_scheme :
    LocalFiniteEtaleRefinementRingStatement.{u} ↔
      HenselianFiniteEtaleRefinementStatement.{u} :=
  ⟨henselianFiniteEtaleRefinement_of_ring, localFiniteEtaleRefinementRing_of_scheme⟩

end Langlands.CommutativeAlgebra
