import Langlands.AlgebraicGeometry.LangWeil.BertiniGenericHyperplaneStatement
import Langlands.AlgebraicGeometry.LangWeil.BertiniHyperplaneCore
import Langlands.AlgebraicGeometry.LangWeil.BertiniHyperplaneDimension
import Langlands.AlgebraicGeometry.GeometricIrreducibilityAffine
import Langlands.AlgebraicGeometry.TensorSpectrumBaseChange

/-!
# Proof of Bertini's theorem for the generic hyperplane section

We descend the primality statement of `BertiniHyperplaneCore`, proved over an algebraically
closed field `K` for a domain `D` receiving a surjection `K ⊗[k] A → D` with nil kernel, to the
generic hyperplane section of `Spec A` over `𝓛 = k(a_*, a_0, …)`, and conclude with the
criterion of `TensorSpectrumBaseChange` for an algebraically closed extension `Ω` of `𝓛`.
-/

noncomputable section

universe u

open MvPolynomial TensorProduct CategoryTheory
open _root_.AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.LangWeil.BertiniGenericHyperplane

section Reduction

variable (k : Type u) [Field k] (A : Type u) [CommRing A] [Algebra k A]
  (K : Type u) [Field K] [Algebra k K] {D : Type u} [CommRing D] [Algebra K D]
  (π : K ⊗[k] A →ₐ[K] D)
  (S : Type u) [Field S] [Algebra K S] (Ω : Type u) [Field Ω] [Algebra k Ω] [Algebra K Ω]
  [IsScalarTower k K Ω] [Algebra S Ω] [IsScalarTower K S Ω]

/-- The ring map `Ω ⊗[k] A ≅ Ω ⊗[K] (K ⊗[k] A) → Ω ⊗[K] D ≅ Ω ⊗[S] (S ⊗[K] D)`. -/
def reductionMap : Ω ⊗[k] A →+* Ω ⊗[S] (S ⊗[K] D) :=
  ((Algebra.TensorProduct.cancelBaseChange K S Ω Ω D).symm.toAlgHom.restrictScalars K).toRingHom.comp
    ((Algebra.TensorProduct.map (AlgHom.id K Ω) π).toRingHom.comp
      ((Algebra.TensorProduct.cancelBaseChange k K Ω Ω A).symm.toAlgHom.restrictScalars K).toRingHom)

theorem reductionMap_tmul (ω : Ω) (a : A) :
    reductionMap k A K π S Ω (ω ⊗ₜ[k] a) = ω ⊗ₜ[S] ((1 : S) ⊗ₜ[K] π ((1 : K) ⊗ₜ[k] a)) := by
  simp [reductionMap]

theorem reductionMap_surjective (hπ : Function.Surjective π) :
    Function.Surjective (reductionMap k A K π S Ω) :=
  (Algebra.TensorProduct.cancelBaseChange K S Ω Ω D).symm.surjective.comp
    ((Algebra.TensorProduct.map_surjective (AlgHom.id K Ω) π (fun x => ⟨x, rfl⟩) hπ).comp
      (Algebra.TensorProduct.cancelBaseChange k K Ω Ω A).symm.surjective)

theorem ker_reductionMap_le (hπ : Function.Surjective π)
    (hker : RingHom.ker π ≤ nilradical (K ⊗[k] A)) :
    RingHom.ker (reductionMap k A K π S Ω) ≤ nilradical (Ω ⊗[k] A) := by
  intro z hz
  set e := Algebra.TensorProduct.cancelBaseChange k K Ω Ω A
  have h1 : e.symm z ∈ RingHom.ker (Algebra.TensorProduct.map (AlgHom.id K Ω) π) := by
    rw [RingHom.mem_ker]
    apply (Algebra.TensorProduct.cancelBaseChange K S Ω Ω D).symm.injective
    rw [map_zero]
    exact hz
  rw [Algebra.TensorProduct.lTensor_ker _ hπ] at h1
  have h2 : (RingHom.ker π).map
      (Algebra.TensorProduct.includeRight : K ⊗[k] A →ₐ[K] Ω ⊗[K] (K ⊗[k] A)) ≤
      nilradical (Ω ⊗[K] (K ⊗[k] A)) := by
    rw [Ideal.map_le_iff_le_comap]
    intro x hx
    exact (mem_nilradical.mp (hker hx)).map _
  have h3 : IsNilpotent (e.symm z) := mem_nilradical.mp (h2 h1)
  have h4 := h3.map e
  rwa [AlgEquiv.apply_symm_apply] at h4

omit [Algebra k Ω] [Algebra K Ω] [IsScalarTower k K Ω] [IsScalarTower K S Ω] in
theorem algebraMap_tmul_one_tmul (s : S) (d : D) :
    algebraMap S Ω s ⊗ₜ[S] ((1 : S) ⊗ₜ[K] d) = (1 : Ω) ⊗ₜ[S] (s ⊗ₜ[K] d) := by
  rw [Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul, TensorProduct.smul_tmul',
    smul_eq_mul, mul_one]

end Reduction

section Descent

variable (k : Type u) [Field k] (A : Type u) [CommRing A] [Algebra k A] {n : ℕ} (g : Fin n → A)
  (K : Type u) [Field K] [Algebra k K] {D : Type u} [CommRing D] [Algebra K D]
  (π : K ⊗[k] A →ₐ[K] D)

set_option hygiene false in
local notation "𝓛" => FractionRing (MvPolynomial (Option (Fin n)) k)
set_option hygiene false in
local notation "𝓛'" => FractionRing (MvPolynomial (Option (Fin n)) K)

variable (Ω : Type u) [Field Ω] [Algebra k Ω] [Algebra K Ω] [IsScalarTower k K Ω]
  [Algebra 𝓛' Ω] [IsScalarTower K 𝓛' Ω] [Algebra 𝓛 Ω] [IsScalarTower k 𝓛 Ω]

theorem reductionMap_hyperplaneEq
    (hcompat : ∀ o : Option (Fin n),
      algebraMap 𝓛 Ω (algebraMap (MvPolynomial (Option (Fin n)) k) 𝓛 (X o)) =
        algebraMap 𝓛' Ω (algebraMap (MvPolynomial (Option (Fin n)) K) 𝓛' (X o))) :
    reductionMap k A K π 𝓛' Ω
        (TensorSpectrumBaseChange.fieldTensorMap k 𝓛 Ω A (hyperplaneEq k g)) =
      (1 : Ω) ⊗ₜ[𝓛'] hyperplaneEq K (fun i => π ((1 : K) ⊗ₜ[k] g i)) := by
  simp only [hyperplaneEq, TensorSpectrumBaseChange.fieldTensorMap, map_add, map_sum,
    Algebra.TensorProduct.map_tmul, IsScalarTower.coe_toAlgHom', AlgHom.id_apply,
    reductionMap_tmul, hcompat, algebraMap_tmul_one_tmul, TensorProduct.tmul_add,
    TensorProduct.tmul_sum]
  rw [← Algebra.TensorProduct.one_def, map_one]

/-- Descent of the core primality statement to `Ω ⊗[k] A`. -/
theorem radical_span_fieldTensorMap_hyperplaneEq_isPrime [IsAlgClosed K] [IsDomain D]
    [Algebra.FiniteType K D] [Algebra.IsAlgebraic 𝓛' Ω] (hπ : Function.Surjective π)
    (hker : RingHom.ker π ≤ nilradical (K ⊗[k] A)) {j l : Fin n}
    (hjl : AlgebraicIndependent K
      ![algebraMap D (FractionRing D) (π ((1 : K) ⊗ₜ[k] g j)),
        algebraMap D (FractionRing D) (π ((1 : K) ⊗ₜ[k] g l))])
    (hcompat : ∀ o : Option (Fin n),
      algebraMap 𝓛 Ω (algebraMap (MvPolynomial (Option (Fin n)) k) 𝓛 (X o)) =
        algebraMap 𝓛' Ω (algebraMap (MvPolynomial (Option (Fin n)) K) 𝓛' (X o))) :
    (Ideal.span {TensorSpectrumBaseChange.fieldTensorMap k 𝓛 Ω A
      (hyperplaneEq k g)}).radical.IsPrime := by
  apply radical_span_singleton_isPrime_of_surjective (reductionMap k A K π 𝓛' Ω)
    (reductionMap_surjective k A K π 𝓛' Ω hπ) (ker_reductionMap_le k A K π 𝓛' Ω hπ hker)
  rw [reductionMap_hyperplaneEq k A g K π Ω hcompat]
  exact radical_span_one_tmul_hyperplaneEq_isPrime K (fun i => π ((1 : K) ⊗ₜ[k] g i)) hjl Ω

/-- Geometric irreducibility of the generic hyperplane section, given the reduction data:
an algebraically closed `K ⊇ k`, a domain `D` of finite type over `K` with a surjection
`π : K ⊗[k] A → D` with nil kernel under which two generators become algebraically
independent, and a separably closed field `Ω` containing `k(a)` and `K(a)` compatibly. -/
theorem geometricallyIrreducible_of_reduction [IsAlgClosed K] [IsDomain D]
    [Algebra.FiniteType K D] [Algebra.IsAlgebraic 𝓛' Ω] [IsSepClosed Ω]
    (hπ : Function.Surjective π) (hker : RingHom.ker π ≤ nilradical (K ⊗[k] A)) {j l : Fin n}
    (hjl : AlgebraicIndependent K
      ![algebraMap D (FractionRing D) (π ((1 : K) ⊗ₜ[k] g j)),
        algebraMap D (FractionRing D) (π ((1 : K) ⊗ₜ[k] g l))])
    (hcompat : ∀ o : Option (Fin n),
      algebraMap 𝓛 Ω (algebraMap (MvPolynomial (Option (Fin n)) k) 𝓛 (X o)) =
        algebraMap 𝓛' Ω (algebraMap (MvPolynomial (Option (Fin n)) K) 𝓛' (X o))) :
    GeometricallyIrreducible (Spec.map (CommRingCat.ofHom
      (algebraMap 𝓛 ((𝓛 ⊗[k] A) ⧸ Ideal.span {hyperplaneEq k g})))) := by
  have h := TensorSpectrumBaseChange.geometricallyIrreducible_quotient_of_isSepClosed_baseChange
    k 𝓛 Ω A (Ideal.span {hyperplaneEq k g}) (by
      rw [Ideal.map_span, Set.image_singleton, PrimeSpectrum.isIrreducible_zeroLocus_iff]
      exact radical_span_fieldTensorMap_hyperplaneEq_isPrime k A g K π Ω hπ hker hjl hcompat)
  rwa [← Spec.map_comp, ← CommRingCat.ofHom_comp, Ideal.Quotient.mk_comp_algebraMap] at h

end Descent

section Main

variable (k : Type u) [Field k] {n : ℕ}

/-- The `k`-algebra map `k[a] → K(a)` induced by `k → K`. -/
def polyFracMap (K : Type u) [Field K] [Algebra k K] :
    MvPolynomial (Option (Fin n)) k →ₐ[k] FractionRing (MvPolynomial (Option (Fin n)) K) :=
  (IsScalarTower.toAlgHom k (MvPolynomial (Option (Fin n)) K)
      (FractionRing (MvPolynomial (Option (Fin n)) K))).comp
    (MvPolynomial.mapAlgHom (Algebra.ofId k K))

theorem polyFracMap_injective (K : Type u) [Field K] [Algebra k K] :
    Function.Injective (polyFracMap k (n := n) K) :=
  (IsFractionRing.injective _ _).comp (MvPolynomial.map_injective _ (algebraMap k K).injective)

/-- The `k`-algebra map `k(a) → K(a)` of rational function fields induced by `k → K`. -/
def fracMap (K : Type u) [Field K] [Algebra k K] :
    FractionRing (MvPolynomial (Option (Fin n)) k) →ₐ[k]
      FractionRing (MvPolynomial (Option (Fin n)) K) :=
  IsFractionRing.liftAlgHom (polyFracMap_injective k K)

theorem fracMap_algebraMap_X (K : Type u) [Field K] [Algebra k K] (o : Option (Fin n)) :
    fracMap k K (algebraMap (MvPolynomial (Option (Fin n)) k)
        (FractionRing (MvPolynomial (Option (Fin n)) k)) (X o)) =
      algebraMap (MvPolynomial (Option (Fin n)) K)
        (FractionRing (MvPolynomial (Option (Fin n)) K)) (X o) := by
  rw [fracMap, IsFractionRing.liftAlgHom_apply, IsFractionRing.lift_algebraMap]
  simp [polyFracMap]

end Main

/-- **Bertini's theorem for the generic hyperplane section.** -/
theorem bertiniGenericHyperplaneStatement : BertiniGenericHyperplaneStatement.{u} := by
  intro k _ A _ _ n g hg hirr hdim
  classical
  have hprime : (nilradical (AlgebraicClosure k ⊗[k] A)).IsPrime :=
    (SchemeFiberGeometry.geometricallyIrreducible_specMap_iff k A).mp hirr (AlgebraicClosure k)
  have hgen := adjoin_range_baseChange_reduction k A g hg
  have hdim' := hdim.trans (ringKrullDim_le_baseChange_reduction k A)
  have : Algebra.FiniteType (AlgebraicClosure k)
      ((AlgebraicClosure k ⊗[k] A) ⧸ nilradical (AlgebraicClosure k ⊗[k] A)) :=
    ⟨⟨Finset.univ.image _, by simpa using hgen⟩⟩
  obtain ⟨j, l, hjl⟩ := exists_algebraicIndependent_pair_of_two_le_ringKrullDim _ _ hgen hdim'
  let φ := (IsScalarTower.toAlgHom (AlgebraicClosure k)
    (FractionRing (MvPolynomial (Option (Fin n)) (AlgebraicClosure k)))
    (AlgebraicClosure (FractionRing (MvPolynomial (Option (Fin n)) (AlgebraicClosure k))))).restrictScalars k |>.comp
    (fracMap k (n := n) (AlgebraicClosure k))
  let _ : Algebra (FractionRing (MvPolynomial (Option (Fin n)) k))
      (AlgebraicClosure (FractionRing (MvPolynomial (Option (Fin n)) (AlgebraicClosure k)))) :=
    φ.toRingHom.toAlgebra
  have : IsScalarTower k (FractionRing (MvPolynomial (Option (Fin n)) k))
      (AlgebraicClosure (FractionRing (MvPolynomial (Option (Fin n)) (AlgebraicClosure k)))) :=
    IsScalarTower.of_algebraMap_eq fun c => (φ.commutes c).symm
  exact geometricallyIrreducible_of_reduction k A g (AlgebraicClosure k)
    (Ideal.Quotient.mkₐ (AlgebraicClosure k) (nilradical (AlgebraicClosure k ⊗[k] A)))
    (AlgebraicClosure (FractionRing (MvPolynomial (Option (Fin n)) (AlgebraicClosure k))))
    (Ideal.Quotient.mkₐ_surjective _ _)
    (Ideal.Quotient.mkₐ_ker (AlgebraicClosure k) (nilradical (AlgebraicClosure k ⊗[k] A))).le hjl
    (fun o => by
      change algebraMap _ _ (fracMap k (n := n) (AlgebraicClosure k) _) = _
      rw [fracMap_algebraMap_X])

end Langlands.AlgebraicGeometry.LangWeil.BertiniGenericHyperplane
