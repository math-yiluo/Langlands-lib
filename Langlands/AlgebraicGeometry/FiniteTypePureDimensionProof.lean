import Langlands.AlgebraicGeometry.FiniteTypePureDimensionStatement
import Mathlib.RingTheory.Ideal.GoingDown
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.Flat.Localization
import Mathlib.RingTheory.Flat.Stability
import Mathlib.RingTheory.Ideal.MinimalPrime.Localization
import Mathlib.RingTheory.NoetherNormalization
import Mathlib.RingTheory.TensorProduct.Finite
import Mathlib.RingTheory.TensorProduct.MvPolynomial
import Mathlib.RingTheory.TensorProduct.Quotient
import Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_exists_smoothProperCurve_opens_hom_comp_eq_of_ringKrullDim_eq_one

universe u v w t

open scoped TensorProduct

namespace Langlands.AlgebraicGeometry.SchemeFiberGeometry

open P2MW.S_AlgebraicGeometry_exists_smoothProperCurve_opens_hom_comp_eq_of_ringKrullDim_eq_one.P2mNormOpen

/-- Ring isomorphisms transport the componentwise dimension condition,
including between different universes. -/
theorem HasPureRingDimension.of_ringEquiv
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] {d : ℕ}
    (h : HasPureRingDimension A d) (e : A ≃+* B) :
    HasPureRingDimension B d := by
  apply hasPureDimension_spec_iff.mp
  have hA := hasPureDimension_spec_iff.mpr h
  let e' := PrimeSpectrum.homeomorphOfRingEquiv e
  intro Z hZ
  have hpre : e' ⁻¹' Z ∈ irreducibleComponents (PrimeSpectrum A) :=
    preimage_mem_irreducibleComponents hZ e'.isOpenEmbedding
      (by
        obtain ⟨z, hz⟩ := hZ.1.1
        exact ⟨z, hz, e'.surjective z⟩)
  let eZ : (e' ⁻¹' Z) ≃ₜ Z :=
    (e'.image (e' ⁻¹' Z)).trans
      (Homeomorph.setCongr (Set.image_preimage_eq Z e'.surjective))
  exact (eZ.isHomeomorph.topologicalKrullDim_eq _).symm.trans (hA _ hpre)

/-- A flat domain base change of an injective extension of domains is torsion-free. -/
theorem tensorProduct_isTorsionFree_of_domains
    (R : Type u) (A : Type v) (S : Type w)
    [CommRing R] [IsDomain R] [CommRing A] [IsDomain A]
    [Algebra R A] [FaithfulSMul R A] [CommRing S] [IsDomain S]
    [Algebra R S] [Module.Flat R S] :
    Module.IsTorsionFree S (S ⊗[R] A) := by
  let : Algebra (FractionRing R) (FractionRing A) :=
    FractionRing.liftAlgebra R (FractionRing A)
  have : Module.Flat R (FractionRing A) :=
    Module.Flat.trans R (FractionRing R) (FractionRing A)
  let j := TensorProduct.AlgebraTensorModule.lTensor S S
    (IsScalarTower.toAlgHom R A (FractionRing A)).toLinearMap
  have hj : Function.Injective j :=
    Module.Flat.lTensor_preserves_injective_linearMap
      (IsScalarTower.toAlgHom R A (FractionRing A)).toLinearMap
      (IsFractionRing.injective A (FractionRing A))
  exact Function.Injective.moduleIsTorsionFree j hj (fun r x => j.map_smul r x)

/-- A minimal prime contracts to zero in a torsion-free algebra over a domain. -/
theorem under_eq_bot_of_minimal_of_torsionFree
    (R : Type u) (B : Type v) [CommRing R] [IsDomain R] [CommRing B]
    [Algebra R B] [Module.IsTorsionFree R B]
    (q : Ideal B) (hq : q ∈ minimalPrimes B) : q.under R = ⊥ := by
  apply le_antisymm _ bot_le
  intro r hr
  change r = 0
  by_contra hne
  have hreg : algebraMap R B r ∈ nonZeroDivisors B := by
    rw [mem_nonZeroDivisors_iff_right]
    intro b hb
    exact (smul_eq_zero.mp (by simpa [Algebra.smul_def, mul_comm] using hb)).resolve_left hne
  exact notMem_nonZeroDivisors_of_mem_mem_minimalPrimes
    (show algebraMap R B r ∈ q from hr) hq hreg

/-- Integral torsion-free algebras over a domain have the same dimension
on every minimal-prime quotient. -/
theorem hasPureRingDimension_of_integral_of_torsionFree
    (R : Type u) (B : Type v) [CommRing R] [IsDomain R] [CommRing B]
    [Algebra R B] [Module.IsTorsionFree R B] [Algebra.IsIntegral R B]
    (d : ℕ) (hd : ringKrullDim R = (d : WithBot ℕ∞)) :
    HasPureRingDimension B d := by
  intro q hq
  have hdim := ringKrullDim_eq_of_ringHom_isIntegral_of_injective
    (Ideal.quotientMap q (algebraMap R B) le_rfl)
    (RingHom.IsIntegral.quotient (algebraMap R B) Algebra.IsIntegral.isIntegral)
    Ideal.quotientMap_injective
  change ringKrullDim (R ⧸ q.under R) = _ at hdim
  rw [under_eq_bot_of_minimal_of_torsionFree R B q hq] at hdim
  exact hdim.symm.trans
    ((ringKrullDim_eq_of_ringEquiv (RingEquiv.quotientBot R)).trans hd)

/-- Every component after scalar extension of a finite-type domain has
the dimension of the original domain. -/
theorem hasPureRingDimension_tensorProduct_of_domain
    (k : Type u) (K : Type v) (A : Type w)
    [Field k] [Field K] [CommRing A] [IsDomain A]
    [Algebra k K] [Algebra k A] [Algebra.FiniteType k A]
    (d : ℕ) (hd : ringKrullDim A = (d : WithBot ℕ∞)) :
    HasPureRingDimension (A ⊗[k] K) d := by
  obtain ⟨n, g, hinj, hfin⟩ := exists_finite_inj_algHom_of_fg k A
  let P := MvPolynomial (Fin n) k
  let : Algebra P A := g.toRingHom.toAlgebra
  have : IsScalarTower k P A := IsScalarTower.of_algebraMap_eq' g.comp_algebraMap.symm
  have : FaithfulSMul P A := (faithfulSMul_iff_algebraMap_injective P A).mpr hinj
  have : Module.Finite P A := (RingHom.finite_algebraMap).mp hfin
  let S := P ⊗[k] K
  let eS : S ≃+* MvPolynomial (Fin n) K :=
    (Algebra.TensorProduct.comm k P K).toRingEquiv.trans
      (MvPolynomial.algebraTensorAlgEquiv k K).toRingEquiv
  have : IsDomain S := eS.toMulEquiv.isDomain _
  have : Module.Flat P S := inferInstance
  have : Module.IsTorsionFree S (S ⊗[P] A) :=
    tensorProduct_isTorsionFree_of_domains P A S
  have hS : ringKrullDim S = (d : WithBot ℕ∞) := by
    have hP := ringKrullDim_eq_of_ringHom_isIntegral_of_injective
      g.toRingHom hfin.to_isIntegral hinj
    rw [ringKrullDim_eq_of_ringEquiv eS, ringKrullDim_mvPolynomial_fin]
    rw [← hP, ringKrullDim_mvPolynomial_fin] at hd
    exact hd
  have hT : HasPureRingDimension (S ⊗[P] A) d :=
    hasPureRingDimension_of_integral_of_torsionFree S (S ⊗[P] A) d hS
  exact hT.of_ringEquiv
    ((Algebra.TensorProduct.comm P S A).toRingEquiv.trans
      (Algebra.TensorProduct.cancelBaseChange k P P A K).toRingEquiv)

/-- A minimal-prime quotient can be computed in any intermediate quotient
whose defining ideal is contained in that prime. -/
theorem ringKrullDim_quotient_eq_of_intermediate_pure
    {B : Type u} [CommRing B] (I q : Ideal B)
    (hIq : I ≤ q) (hq : q ∈ minimalPrimes B) (d : ℕ)
    (h : HasPureRingDimension (B ⧸ I) d) :
    ringKrullDim (B ⧸ q) = (d : WithBot ℕ∞) := by
  have hqI : q ∈ I.minimalPrimes :=
    ⟨⟨hq.1.1, hIq⟩, fun r hr hrq => hq.2 ⟨hr.1, bot_le⟩ hrq⟩
  rw [Ideal.minimalPrimes_eq_comap] at hqI
  obtain ⟨r, hr, hrq⟩ := hqI
  have hrmap : q.map (Ideal.Quotient.mk I) = r := by
    rw [← hrq, Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective]
  have hd := h r hr
  rw [← hrmap] at hd
  exact (ringKrullDim_eq_of_ringEquiv
    (DoubleQuot.quotQuotEquivQuotOfLE hIq)).symm.trans hd

/-- Every finite-type domain over a field has a natural Krull dimension. -/
theorem exists_nat_ringKrullDim_of_finiteType_domain
    (k : Type u) (A : Type v) [Field k] [CommRing A] [IsDomain A]
    [Algebra k A] [Algebra.FiniteType k A] :
    ∃ d : ℕ, ringKrullDim A = (d : WithBot ℕ∞) := by
  obtain ⟨n, g, hinj, hfin⟩ := exists_finite_inj_algHom_of_fg k A
  exact ⟨n, (ringKrullDim_eq_of_ringHom_isIntegral_of_injective
    g.toRingHom hfin.to_isIntegral hinj).symm.trans (ringKrullDim_mvPolynomial_fin k n)⟩

/-- An individual component after field extension has the dimension of
its contracted component. -/
theorem ringKrullDim_minimalPrime_quotient_tensorProduct
    (k : Type u) (K : Type v) (A : Type w)
    [Field k] [Field K] [CommRing A]
    [Algebra k K] [Algebra k A] [Algebra.FiniteType k A]
    (q : Ideal (A ⊗[k] K)) (hq : q ∈ minimalPrimes (A ⊗[k] K)) :
    ringKrullDim ((A ⊗[k] K) ⧸ q) = ringKrullDim (A ⧸ q.under A) := by
  have : q.IsPrime := hq.1.1
  let p := q.under A
  have : p.IsPrime := inferInstance
  obtain ⟨d, hd⟩ := exists_nat_ringKrullDim_of_finiteType_domain k (A ⧸ p)
  have hT := hasPureRingDimension_tensorProduct_of_domain k K (A ⧸ p) d hd
  have hQ := hT.of_ringEquiv
    (Algebra.TensorProduct.quotientTensorEquiv (R := k) k K A p).toRingEquiv
  exact (ringKrullDim_quotient_eq_of_intermediate_pure
    (p.map (algebraMap A (A ⊗[k] K))) q
    (Ideal.map_le_of_le_comap le_rfl) hq d hQ).trans hd.symm

/-- Arbitrary ground-field extensions preserve and reflect componentwise
pure dimension for every finite-type algebra. -/
theorem hasPureRingDimension_tensorProduct_iff
    (k : Type u) (K : Type v) (A : Type w)
    [Field k] [Field K] [CommRing A]
    [Algebra k K] [Algebra k A] [Algebra.FiniteType k A] (d : ℕ) :
    HasPureRingDimension A d ↔ HasPureRingDimension (A ⊗[k] K) d := by
  constructor
  · intro h q hq
    have : q.IsPrime := hq.1.1
    have hp : q.under A ∈ minimalPrimes A := by
      refine ⟨⟨inferInstance, bot_le⟩, ?_⟩
      rintro p ⟨hp, _⟩ hpq
      have := hp
      obtain ⟨Q, hQq, hQ, hQp⟩ :=
        Ideal.exists_ideal_le_liesOver_of_le (p := p) (q := q.under A) q hpq
      have := hQ
      have := hQp
      have heq : Q = q := hQq.antisymm (hq.2 ⟨hQ, bot_le⟩ hQq)
      exact le_of_eq (by rw [← heq]; exact (Q.over_def p).symm)
    exact (ringKrullDim_minimalPrime_quotient_tensorProduct k K A q hq).trans (h _ hp)
  · intro h p hp
    have hinj : Function.Injective (algebraMap A (A ⊗[k] K)) := by
      convert (TensorProduct.comm k K A).injective.comp
        (Module.Flat.tensorProduct_mk_injective (R := k) (S := K) (M := A)) using 1
      ext a
      simp
    have hp' : p ∈ ((⊥ : Ideal (A ⊗[k] K)).comap (algebraMap A (A ⊗[k] K))).minimalPrimes := by
      rwa [Ideal.comap_bot_of_injective _ hinj]
    obtain ⟨q, hq, hqp⟩ := Ideal.exists_minimalPrimes_comap_eq
      (algebraMap A (A ⊗[k] K)) p hp'
    rw [← hqp]
    exact (ringKrullDim_minimalPrime_quotient_tensorProduct k K A q hq).symm.trans (h q hq)

/-- The exact universal finite-type pure-dimension comparison. -/
theorem finiteTypeFieldExtensionPureRingDimensionInvariance :
    FiniteTypeFieldExtensionPureRingDimensionInvariance.{u,v,w} := by
  intro k K A _ _ _ _ _ _ d
  exact hasPureRingDimension_tensorProduct_iff k K A d

end Langlands.AlgebraicGeometry.SchemeFiberGeometry
