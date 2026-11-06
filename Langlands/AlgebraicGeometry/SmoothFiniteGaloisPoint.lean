import Langlands.AlgebraicGeometry.PointTopology.SeparablyClosedDensity
import Langlands.CommutativeAlgebra.SeparablyClosedRationalPointProof
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.FieldTheory.Normal.Closure

/-! # Points of smooth schemes over finite Galois extensions -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

namespace Langlands.AlgebraicGeometry

/-- **Points of smooth algebras over finite Galois extensions.** A nonzero smooth algebra over a
field `K` has a `K`-algebra homomorphism to some finite Galois extension of `K`. -/
theorem exists_finiteGalois_algHom_of_smooth (K R : Type u) [Field K] [CommRing R]
    [Algebra K R] [Algebra.Smooth K R] [Nontrivial R] :
    ∃ (L : Type u) (_ : Field L) (_ : Algebra K L) (_ : FiniteDimensional K L)
      (_ : IsGalois K L), Nonempty (R →ₐ[K] L) := by
  let Ω := SeparableClosure K
  have : Nontrivial (Ω ⊗[K] R) := by
    obtain ⟨m, hm⟩ := Ideal.exists_maximal R
    let k := R ⧸ m
    let : Field k := Ideal.Quotient.field m
    have : Nontrivial (Ω ⊗[K] k) :=
      Algebra.TensorProduct.nontrivial_of_algebraMap_injective_of_isDomain K Ω k
        (algebraMap K Ω).injective (algebraMap K k).injective
    exact (Algebra.TensorProduct.map (AlgHom.id K Ω)
      (IsScalarTower.toAlgHom K R k)).toRingHom.domain_nontrivial
  have : Algebra.IsGeometricallyReduced Ω (Ω ⊗[K] R) :=
    PointTopology.isGeometricallyReduced_of_smooth Ω (Ω ⊗[K] R)
  obtain ⟨a⟩ := CommutativeAlgebra.SeparablyClosedRationalPointProof.separablyClosedRationalPoint
    Ω (Ω ⊗[K] R)
  let φ : R →ₐ[K] Ω := (a.restrictScalars K).comp Algebra.TensorProduct.includeRight
  obtain ⟨t, ht⟩ := Algebra.FiniteType.out (R := K) (A := R)
  let F := IntermediateField.adjoin K (φ '' t)
  have : FiniteDimensional K F := IntermediateField.finiteDimensional_adjoin fun x _ =>
    (Algebra.IsSeparable.isIntegral K x)
  let N := IntermediateField.normalClosure K F Ω
  have : IsGalois K N :=
    { to_isSeparable := Algebra.isSeparable_tower_bot_of_isSeparable K N Ω
      to_normal := inferInstance }
  have hφ (r : R) : φ r ∈ N := by
    apply IntermediateField.le_normalClosure F
    apply IntermediateField.algebra_adjoin_le_adjoin K (φ '' t)
    rw [← AlgHom.map_adjoin, ht]
    exact ⟨r, trivial, rfl⟩
  exact ⟨N, inferInstance, inferInstance, inferInstance, inferInstance,
    ⟨φ.codRestrict N.toSubalgebra hφ⟩⟩

/-- **Points of smooth affine schemes over finite Galois extensions.** A nonempty affine scheme
smooth over a field `K` has a point over some finite Galois extension `L` of `K`, that is a
morphism from `Spec L` compatible with the structure morphisms to `Spec K`. -/
theorem exists_finiteGalois_point_of_smooth (K : Type u) [Field K] {X : Scheme.{u}}
    [IsAffine X] [Nonempty X] (f : X ⟶ Spec (CommRingCat.of K)) [Smooth f] :
    ∃ (L : Type u) (_ : Field L) (_ : Algebra K L) (_ : FiniteDimensional K L)
      (_ : IsGalois K L) (σ : Spec (CommRingCat.of L) ⟶ X),
      σ ≫ f = Spec.map (CommRingCat.ofHom (algebraMap K L)) := by
  let φ := Spec.preimage (X.isoSpec.inv ≫ f)
  have hφ : Spec.map φ = X.isoSpec.inv ≫ f := Spec.map_preimage _
  have : Smooth (Spec.map φ) := by rw [hφ]; infer_instance
  have : Nontrivial Γ(X, ⊤) := by
    obtain ⟨y⟩ := ‹Nonempty X›
    exact PrimeSpectrum.nonempty_iff_nontrivial.mp ⟨X.isoSpec.hom y⟩
  algebraize [φ.hom]
  have : Algebra.Smooth K Γ(X, ⊤) := RingHom.smooth_algebraMap.mp
    ((HasRingHomProperty.Spec_iff (P := @Smooth)).mp ‹Smooth (Spec.map φ)›)
  obtain ⟨L, _, _, _, _, ⟨a⟩⟩ := exists_finiteGalois_algHom_of_smooth K Γ(X, ⊤)
  refine ⟨L, inferInstance, inferInstance, inferInstance, inferInstance,
    Spec.map (CommRingCat.ofHom a.toRingHom) ≫ X.isoSpec.inv, ?_⟩
  rw [Category.assoc, ← hφ, ← Spec.map_comp]
  congr 1
  ext r
  exact a.commutes r

end Langlands.AlgebraicGeometry
