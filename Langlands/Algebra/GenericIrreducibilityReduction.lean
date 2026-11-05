import Langlands.Algebra.GenericDensity
import Langlands.Algebra.GeometricIrreducibilitySpreadingStatement
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.RingTheory.TensorProduct.Quotient

/-! # Nilradical reductions for generic geometric irreducibility -/

open scoped TensorProduct

universe u v w t

namespace Langlands.Algebra.GenericIrreducibilityReduction

/-- A surjection with nil kernel preserves and reflects primality of the nilradical. -/
theorem nilradical_isPrime_iff_of_surjective_nil_kernel
    {A B : Type*} [CommRing A] [CommRing B]
    (f : A →+* B) (hf : Function.Surjective f)
    (hker : RingHom.ker f ≤ nilradical A) :
    (nilradical A).IsPrime ↔ (nilradical B).IsPrime := by
  have heq : Ideal.comap f (nilradical B) = nilradical A := by
    change Ideal.comap f (⊥ : Ideal B).radical = (⊥ : Ideal A).radical
    rw [Ideal.comap_radical, ← RingHom.ker_eq_comap_bot]
    exact le_antisymm ((Ideal.radical_isRadical _).radical_le_iff.mpr hker)
      (Ideal.radical_mono bot_le)
  constructor
  · intro h
    let := h
    have hmap := Ideal.map_isPrime_of_surjective hf hker
    have heq' : (nilradical A).map f = nilradical B := by
      rw [← heq, Ideal.map_comap_of_surjective _ hf]
    exact heq' ▸ hmap
  · intro h
    let := h
    rw [← heq]
    infer_instance

/-- Primality of the nilradical is invariant under ring equivalences. -/
theorem nilradical_isPrime_iff_of_ringEquiv
    {A B : Type*} [CommRing A] [CommRing B] (e : A ≃+* B) :
    (nilradical A).IsPrime ↔ (nilradical B).IsPrime :=
  nilradical_isPrime_iff_of_surjective_nil_kernel e.toRingHom e.surjective
    (by
      rw [(RingHom.injective_iff_ker_eq_bot e.toRingHom).mp e.injective]
      exact bot_le)

/-- Generic nilpotence specializes after inverting one base element, uniformly in the
element and the scalar algebra. -/
theorem exists_ne_zero_forall_tensor_nilpotent
    {R : Type u} [CommRing R] [IsDomain R]
    (B : Type v) [CommRing B] [Algebra R B] [Algebra.FiniteType R B]
    (F : Type t) [Field F] [Algebra R F] [IsFractionRing R F] :
    ∃ a : R, a ≠ 0 ∧ ∀ (K : Type w) [CommRing K] [Algebra R K],
      IsUnit (algebraMap R K a) → ∀ b : B,
        IsNilpotent (1 ⊗ₜ[R] b : F ⊗[R] B) →
          IsNilpotent (1 ⊗ₜ[R] b : K ⊗[R] B) := by
  obtain ⟨a, ha, hflat⟩ := GenericDensity.genFlat_of_finiteType (R := R) B
  have : Module.Flat R (LocalizedModule (Submonoid.powers a) B) := hflat a dvd_rfl
  refine ⟨a, ha, fun K _ _ hK b ⟨n, hn⟩ => ⟨n, ?_⟩⟩
  let j := TensorProduct.mk R F B (1 : F)
  have hj : j (b ^ n) = 0 := by
    simpa only [j, TensorProduct.mk_apply, Algebra.TensorProduct.tmul_pow, one_pow]
      using hn
  obtain ⟨s, hs⟩ := (IsLocalizedModule.eq_zero_iff (nonZeroDivisors R) j).mp hj
  change (s : R) • b ^ n = 0 at hs
  let m := LocalizedModule.mkLinearMap (Submonoid.powers a) B
  have hm : m (b ^ n) = 0 := by
    apply Module.Flat.isSMulRegular_of_nonZeroDivisors
      (M := LocalizedModule (Submonoid.powers a) B) s.property
    change (s : R) • m (b ^ n) = (s : R) • 0
    rw [smul_zero]
    rw [← m.map_smul, hs, map_zero]
  have ht : (m.lTensor K) (1 ⊗ₜ[R] b ^ n) = 0 := by
    simp [hm]
  have hzero : (1 ⊗ₜ[R] b ^ n : K ⊗[R] B) = 0 :=
    GenericDensity.lTensor_mkLinearMap_injective_of_isUnit a K hK
      (ht.trans (map_zero _).symm)
  simpa only [Algebra.TensorProduct.tmul_pow, one_pow] using hzero

/-- A quotient by elements whose images are nilpotent leaves fibre irreducibility unchanged. -/
theorem nilradical_tensor_quotient_isPrime_iff
    {R B K : Type*} [CommRing R] [CommRing B] [CommRing K]
    [Algebra R B] [Algebra R K]
    (I : Ideal B)
    (hI : ∀ b ∈ I, IsNilpotent (1 ⊗ₜ[R] b : K ⊗[R] B)) :
    (nilradical (K ⊗[R] B)).IsPrime ↔
      (nilradical (K ⊗[R] (B ⧸ I))).IsPrime := by
  let j : B →ₐ[R] K ⊗[R] B := Algebra.TensorProduct.includeRight
  let J := I.map j.toRingHom
  have hJ : J ≤ nilradical (K ⊗[R] B) := by
    apply Ideal.map_le_iff_le_comap.mpr
    intro b hb
    exact (mem_nilradical).mpr (hI b hb)
  let e := Algebra.TensorProduct.tensorQuotientEquiv (R := R) K B K I
  have hquot := nilradical_isPrime_iff_of_surjective_nil_kernel
    (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective
    (by rw [Ideal.mk_ker]; exact hJ)
  exact hquot.trans (nilradical_isPrime_iff_of_ringEquiv e.toRingEquiv).symm

/-- Nilpotence descends from an algebraic closure in a scalar-extended tensor product. -/
theorem nilpotent_tensor_of_algebraicClosure
    {R B F : Type*} [CommRing R] [CommRing B] [Field F]
    [Algebra R B] [Algebra R F] (b : B)
    (hb : IsNilpotent (1 ⊗ₜ[R] b : AlgebraicClosure F ⊗[R] B)) :
    IsNilpotent (1 ⊗ₜ[R] b : F ⊗[R] B) := by
  let e := Algebra.TensorProduct.cancelBaseChange R F F (AlgebraicClosure F) B
  have h : IsNilpotent
      (1 ⊗ₜ[F] (1 ⊗ₜ[R] b) : AlgebraicClosure F ⊗[F] (F ⊗[R] B)) := by
    apply (IsNilpotent.map_iff e.injective).mp
    simpa only [e, Algebra.TensorProduct.cancelBaseChange_tmul, one_smul] using hb
  exact (IsNilpotent.map_iff
    (Algebra.TensorProduct.includeRight_injective
      (B := F ⊗[R] B) (RingHom.injective (algebraMap F (AlgebraicClosure F))))).mp h

/-- The domain-algebra case suffices for an arbitrary finite type algebra over a domain. -/
theorem spreading_of_domain_algebras
    {R : Type u} [CommRing R] [IsDomain R]
    (B : Type v) [CommRing B] [Algebra R B] [Algebra.FiniteType R B]
    (F : Type t) [Field F] [Algebra R F] [IsFractionRing R F]
    (hcore : ∀ (C : Type v) [CommRing C] [IsDomain C] [Algebra R C]
      [FaithfulSMul R C] [Algebra.FiniteType R C],
      (nilradical (AlgebraicClosure F ⊗[R] C)).IsPrime →
        ∃ a : R, a ≠ 0 ∧ ∀ (K : Type w) [Field K] [Algebra R K],
          algebraMap R K a ≠ 0 → (nilradical (K ⊗[R] C)).IsPrime)
    (hgen : (nilradical (AlgebraicClosure F ⊗[R] B)).IsPrime) :
    ∃ a : R, a ≠ 0 ∧ ∀ (K : Type w) [Field K] [Algebra R K],
      algebraMap R K a ≠ 0 → (nilradical (K ⊗[R] B)).IsPrime := by
  let G := AlgebraicClosure F ⊗[R] B
  let j : B →ₐ[R] G := Algebra.TensorProduct.includeRight
  let I : Ideal B := (nilradical G).comap j.toRingHom
  let := hgen
  have : I.IsPrime := inferInstance
  let C := B ⧸ I
  have hinj : Function.Injective (algebraMap R C) := by
    apply (injective_iff_map_eq_zero _).mpr
    intro r hr
    by_contra hr0
    have hI : algebraMap R B r ∈ I := Ideal.Quotient.eq_zero_iff_mem.mp hr
    change j (algebraMap R B r) ∈ nilradical G at hI
    rw [j.commutes] at hI
    have hrf : algebraMap R F r ≠ 0 := by
      exact fun h => hr0 ((IsFractionRing.injective R F) (h.trans (map_zero _).symm))
    have hu : IsUnit (algebraMap R G r) := by
      rw [IsScalarTower.algebraMap_apply R F G]
      exact (isUnit_iff_ne_zero.mpr hrf).map (algebraMap F G)
    exact hgen.ne_top ((nilradical G).eq_top_of_isUnit_mem hI hu)
  let : FaithfulSMul R C := (faithfulSMul_iff_algebraMap_injective R C).mpr hinj
  have hnil : ∀ b ∈ I, IsNilpotent (1 ⊗ₜ[R] b : G) := by
    intro b hb
    exact mem_nilradical.mp hb
  have hgenC : (nilradical (AlgebraicClosure F ⊗[R] C)).IsPrime :=
    (nilradical_tensor_quotient_isPrime_iff I hnil).mp hgen
  obtain ⟨a, ha, hC⟩ := hcore C hgenC
  obtain ⟨d, hd, hnilnear⟩ :=
    exists_ne_zero_forall_tensor_nilpotent (R := R) B F
  refine ⟨a * d, mul_ne_zero ha hd, fun K _ _ hK => ?_⟩
  have had : algebraMap R K a ≠ 0 ∧ algebraMap R K d ≠ 0 := by
    simpa only [map_mul, mul_ne_zero_iff] using hK
  apply (nilradical_tensor_quotient_isPrime_iff I ?_).mpr (hC K had.1)
  intro b hb
  exact hnilnear K (isUnit_iff_ne_zero.mpr had.2) b
    (nilpotent_tensor_of_algebraicClosure b (hnil b hb))

/-- Removing the base nilradical and the generic-fibre nilradical reduces the full
affine spreading proposition to faithful finite type domain algebras over domains. -/
theorem spreading_of_domain_bases
    (hcore : ∀ (S : Type u) [CommRing S] [IsDomain S]
      (F : Type u) [Field F] [Algebra S F] [IsFractionRing S F]
      (C : Type max u v) [CommRing C] [IsDomain C] [Algebra S C]
      [FaithfulSMul S C] [Algebra.FiniteType S C],
      (nilradical (AlgebraicClosure F ⊗[S] C)).IsPrime →
        ∃ a : S, a ≠ 0 ∧ ∀ (K : Type w) [Field K] [Algebra S K],
          algebraMap S K a ≠ 0 → (nilradical (K ⊗[S] C)).IsPrime) :
    Langlands.Algebra.FiniteTypeGeometricIrreducibilitySpreading.{u,v,w} := by
  intro R _ _ B _ _ _ hgen
  let S := R ⧸ nilradical R
  let D := S ⊗[R] B
  let F := (nilradical R).ResidueField
  let e := Algebra.TensorProduct.cancelBaseChange R S S (AlgebraicClosure F) B
  have hgenD : (nilradical (AlgebraicClosure F ⊗[S] D)).IsPrime :=
    (nilradical_isPrime_iff_of_ringEquiv e.toRingEquiv).mpr hgen
  obtain ⟨a, ha, hD⟩ :=
    spreading_of_domain_algebras D F (hcore S F) hgenD
  obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective a
  refine ⟨r, ?_, fun K _ φ hrK => ?_⟩
  · intro hrnil
    apply ha
    rw [← hr, Ideal.Quotient.eq_zero_iff_mem]
    exact mem_nilradical.mpr hrnil
  · let : Algebra R K := φ.toAlgebra
    let ψ : S →+* K := Ideal.Quotient.lift (nilradical R) φ (by
      intro x hx
      exact isNilpotent_iff_eq_zero.mp ((mem_nilradical.mp hx).map φ))
    let : Algebra S K := ψ.toAlgebra
    let : IsScalarTower R S K := IsScalarTower.of_algebraMap_eq' rfl
    have haK : algebraMap S K a ≠ 0 := by
      rw [← hr]
      exact hrK
    let eK := Algebra.TensorProduct.cancelBaseChange R S S K B
    exact (nilradical_isPrime_iff_of_ringEquiv eK.toRingEquiv).mp (hD K haK)

end Langlands.Algebra.GenericIrreducibilityReduction
