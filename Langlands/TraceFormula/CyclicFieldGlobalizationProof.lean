import Langlands.TraceFormula.CyclicFieldGlobalizationStatement
import Langlands.BaseChange.CyclicNormDeterminant
import Langlands.LocalField.CharZeroPadicRealization
import Langlands.Global.Arithmetic.FieldRealizationProof
import Langlands.Global.Arithmetic.ChebotarevPrimeRealizationProof
import Langlands.Global.AdelicFunctoriality.CompletedTensorComparisonProof
import Langlands.Global.AdelicFunctoriality.LocalDegree
import Mathlib.RingTheory.RamificationInertia.Ramification

/-! # Globalization of a cyclic extension of local fields -/

noncomputable section

open NumberField IsDedekindDomain
open scoped TensorProduct NumberField.LiesOver Pointwise
open scoped Langlands.Global.AdelicFunctoriality.FiniteExtension
open scoped Langlands.Global.AdelicFunctoriality.InfiniteExtension

namespace Langlands.TraceFormula

open Langlands.BaseChange Langlands.Global.AdelicFunctoriality

universe u v

section Split

variable {K L A : Type*} [Field K] [Field L] [Field A] [Algebra K L] [Algebra K A]

/-- An embedding into the coefficient field gives cyclic coordinates by evaluating
at successive powers of the chosen generator. -/
private theorem cyclicShiftSplit_of_embedding (f : L →ₐ[K] A)
    (σ : L ≃ₐ[K] L) (l : ℕ) (hcyc : IsCyclicAlgebra σ l) :
    IsCyclicShiftSplit K L A σ l := by
  classical
  have : FiniteDimensional K L := hcyc.1
  have horder := hcyc.2.2.2.1
  let coordinate (i : Fin l) : A ⊗[K] L →ₐ[A] A :=
    Algebra.TensorProduct.lift (Algebra.ofId A A)
      (f.comp (σ ^ (i : ℕ)).toAlgHom) (fun _ _ => mul_comm ..)
  have hcoordinate (i : Fin l) (a : A) (x : L) :
      coordinate i (a ⊗ₜ[K] x) = a * f ((σ ^ (i : ℕ)) x) := rfl
  have hconstant (i : Fin l) (a : A) :
      coordinate i (algebraMap A (A ⊗[K] L) a) = a := (coordinate i).commutes a
  let I (i : Fin l) : Ideal (A ⊗[K] L) := RingHom.ker (coordinate i).toRingHom
  have (i : Fin l) : (I i).IsMaximal :=
    RingHom.ker_isMaximal_of_surjective (coordinate i).toRingHom fun a =>
      ⟨algebraMap A (A ⊗[K] L) a, hconstant i a⟩
  have hcoprime : Pairwise (fun i j => IsCoprime (I i) (I j)) := by
    intro i j hij
    apply Ideal.isCoprime_of_isMaximal
    intro heq
    apply hij
    apply Fin.ext
    refine pow_injOn_Iio_orderOf (x := σ) (by simp [horder]) (by simp [horder])
      (AlgEquiv.ext fun x => f.injective ?_)
    let y : A ⊗[K] L := 1 ⊗ₜ[K] x
    have hy : y - algebraMap A (A ⊗[K] L) (coordinate i y) ∈ I j := by
      rw [← heq]
      change coordinate i (y - algebraMap A (A ⊗[K] L) (coordinate i y)) = 0
      rw [map_sub, hconstant, sub_self]
    change coordinate j (y - algebraMap A (A ⊗[K] L) (coordinate i y)) = 0 at hy
    rw [map_sub, hconstant, sub_eq_zero,
      hcoordinate, hcoordinate, one_mul, one_mul] at hy
    exact hy.symm
  let product := AlgHom.pi coordinate
  have hsurj : Function.Surjective product := by
    intro a
    obtain ⟨y, hy⟩ := Ideal.exists_forall_sub_mem_ideal hcoprime
      (fun i => algebraMap A (A ⊗[K] L) (a i))
    refine ⟨y, funext fun i => ?_⟩
    have hi := hy i
    change coordinate i (y - algebraMap A (A ⊗[K] L) (a i)) = 0 at hi
    rwa [map_sub, hconstant, sub_eq_zero] at hi
  have hdim : Module.finrank A (A ⊗[K] L) = Module.finrank A (Fin l → A) := by
    rw [Module.finrank_baseChange, hcyc.2.1, Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
  refine ⟨AlgEquiv.ofBijective product
    (OrzechProperty.bijective_of_surjective_of_finrank_le product.toLinearMap hsurj hdim.le), ?_⟩
  intro y
  funext i
  change coordinate i (Algebra.TensorProduct.congr (AlgEquiv.refl : A ≃ₐ[A] A) σ y) =
    coordinate (finRotate l i) y
  induction y using TensorProduct.inductionOn with
  | tmul a x =>
    change coordinate i (a ⊗ₜ[K] σ x) = coordinate (finRotate l i) (a ⊗ₜ[K] x)
    rw [hcoordinate, hcoordinate]
    have := i.neZero
    have hpow : σ ^ ((finRotate l i : Fin l) : ℕ) = σ ^ ((i : ℕ) + 1) := by
      simp only [finRotate_apply, Fin.val_add, Fin.coe_ofNat_eq_mod, Nat.add_mod_mod]
      simpa only [horder] using pow_mod_orderOf σ ((i : ℕ) + 1)
    rw [hpow, pow_succ, AlgEquiv.mul_apply]
  | add x y hx hy => simp only [map_add, hx, hy]

end Split

section NumberFields

variable {K L : Type} [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]

private theorem cyclicShiftSplit_infinite [IsTotallyReal L]
    (w : InfinitePlace K) (σ : L ≃ₐ[K] L) (l : ℕ) (hcyc : IsCyclicAlgebra σ l) :
    IsCyclicShiftSplit K L w.Completion σ l := by
  obtain ⟨z, hz⟩ := InfinitePlace.comap_surjective (K := L) w
  have : z.LiesOver w := ⟨congrArg Subtype.val hz⟩
  have hone := ((IsTotallyReal.isReal z).isUnramified (k := K)).finrank_eq_one w
  let e : w.Completion ≃ₐ[w.Completion] z.Completion :=
    AlgEquiv.ofBijective (Algebra.ofId _ _)
      (Algebra.finrank_eq_one_iff_bijective_algebraMap.mp hone)
  let q : InfinitePlacesAbove L w := ⟨z, inferInstance⟩
  let f : w.Completion ⊗[K] L →ₐ[w.Completion] w.Completion :=
    e.symm.toAlgHom.comp ((Pi.evalAlgHom _ _ q).comp (infiniteTensorMap w))
  exact cyclicShiftSplit_of_embedding
    ((f.restrictScalars K).comp Algebra.TensorProduct.includeRight) σ l hcyc

private theorem exists_bounded_away_frobenius [IsGalois K L]
    (σ : L ≃ₐ[K] L) (S : Finset (HeightOneSpectrum (𝓞 K))) (N : ℕ) :
    ∃ p : HeightOneSpectrum (𝓞 K), p ∉ S ∧ N ≤ p.asIdeal.absNorm ∧
      ∃ q : HeightOneSpectrum (𝓞 L), q.asIdeal.LiesOver p.asIdeal ∧
        Algebra.IsUnramifiedAt (𝓞 K) q.asIdeal ∧
        (RingOfIntegers.mapAlgHom σ).IsArithFrobAt q.asIdeal := by
  classical
  have small := Ring.HasFiniteQuotients.finite_absNorm_heightOneSpectrum_le (S := 𝓞 K) N
  obtain ⟨p, hp, q, hq, hu, hf⟩ :=
    Global.chebotarevPrimeRealizationStatement K L σ (S ∪ small.toFinset)
  refine ⟨p, fun h => hp (Finset.mem_union_left _ h), le_of_not_ge fun h => ?_, q, hq, hu, hf⟩
  exact hp (Finset.mem_union_right _ (small.mem_toFinset.mpr h))

private theorem localDegree_eq_one_of_identity_frobenius
    (p : HeightOneSpectrum (𝓞 K)) (q : HeightOneSpectrum (𝓞 L))
    [q.asIdeal.LiesOver p.asIdeal] [Algebra.IsUnramifiedAt (𝓞 K) q.asIdeal]
    (hf : (RingOfIntegers.mapAlgHom (1 : L ≃ₐ[K] L)).IsArithFrobAt q.asIdeal) :
    Module.finrank (p.adicCompletion K) (q.adicCompletion L) = 1 := by
  classical
  let : Field (𝓞 K ⧸ p.asIdeal) := Ideal.Quotient.field _
  let : Field (𝓞 L ⧸ q.asIdeal) := Ideal.Quotient.field _
  let : Fintype (𝓞 K ⧸ p.asIdeal) := Fintype.ofFinite _
  let frob := FiniteField.frobeniusAlgHom (𝓞 K ⧸ p.asIdeal) (𝓞 L ⧸ q.asIdeal)
  have hfrob : frob = 1 := by
    ext x
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
    have hy := hf.mk_apply y
    rw [← q.asIdeal.over_def p.asIdeal, Nat.card_eq_fintype_card] at hy
    exact hy.symm
  rw [localDegree_eq, Ideal.ramificationIdx_eq_one, one_mul,
    Ideal.inertiaDeg_eq_of_isMaximal p.asIdeal q.asIdeal,
    ← FiniteField.orderOf_frobeniusAlgHom, show orderOf frob = 1 by rw [hfrob, orderOf_one]]

private theorem cyclicShiftSplit_finite (p : HeightOneSpectrum (𝓞 K))
    (q : HeightOneSpectrum (𝓞 L)) [q.asIdeal.LiesOver p.asIdeal]
    [Algebra.IsUnramifiedAt (𝓞 K) q.asIdeal]
    (hf : (RingOfIntegers.mapAlgHom (1 : L ≃ₐ[K] L)).IsArithFrobAt q.asIdeal)
    (σ : L ≃ₐ[K] L) (l : ℕ) (hcyc : IsCyclicAlgebra σ l) :
    IsCyclicShiftSplit K L (p.adicCompletion K) σ l := by
  let e : p.adicCompletion K ≃ₐ[p.adicCompletion K] q.adicCompletion L :=
    AlgEquiv.ofBijective (Algebra.ofId _ _)
      (Algebra.finrank_eq_one_iff_bijective_algebraMap.mp
        (localDegree_eq_one_of_identity_frobenius p q hf))
  let z : FinitePlacesAbove L p := ⟨q, inferInstance⟩
  let f : p.adicCompletion K ⊗[K] L →ₐ[p.adicCompletion K] p.adicCompletion K :=
    e.symm.toAlgHom.comp ((Pi.evalAlgHom _ _ z).comp (finiteTensorMap p))
  exact cyclicShiftSplit_of_embedding
    ((f.restrictScalars K).comp Algebra.TensorProduct.includeRight) σ l hcyc

open UniqueFactorizationMonoid in
private theorem prime_map_of_generator_frobenius [IsGalois K L]
    (p : HeightOneSpectrum (𝓞 K)) (q : HeightOneSpectrum (𝓞 L))
    [q.asIdeal.LiesOver p.asIdeal] [Algebra.IsUnramifiedAt (𝓞 K) q.asIdeal]
    (σ : L ≃ₐ[K] L) (hgen : Subgroup.zpowers σ = ⊤)
    (hf : (RingOfIntegers.mapAlgHom σ).IsArithFrobAt q.asIdeal) :
    (Ideal.map (algebraMap (𝓞 K) (𝓞 L)) p.asIdeal).IsPrime := by
  classical
  have : IsGaloisGroup (L ≃ₐ[K] L) (𝓞 K) (𝓞 L) :=
    IsGaloisGroup.of_isFractionRing (L ≃ₐ[K] L) (𝓞 K) (𝓞 L) K L
  have hstab := IsArithFrobAt.mem_stabilizer (R := 𝓞 K) (σ := σ) (by exact hf)
  let J := Ideal.map (algebraMap (𝓞 K) (𝓞 L)) p.asIdeal
  have hall : ∀ P ∈ normalizedFactors J, P = q.asIdeal := by
    intro P hP
    obtain ⟨hPprime, hPover⟩ :=
      (Ideal.mem_primesOver_iff_mem_normalizedFactors (𝓞 L) p.ne_bot).mpr hP
    have : P.IsPrime := hPprime
    have : P.LiesOver p.asIdeal := hPover
    obtain ⟨τ, hτ⟩ := Ideal.exists_smul_eq_of_isGaloisGroup
      p.asIdeal q.asIdeal P (L ≃ₐ[K] L)
    exact hτ.symm.trans (smul_eq_self_of_mem_zpowers (by rw [hgen]; trivial)
      (MulAction.mem_stabilizer_iff.mp hstab))
  have hfac := Multiset.eq_replicate_of_mem hall
  have hJ : J ≠ ⊥ := Ideal.map_ne_bot_of_ne_bot p.ne_bot
  have hcount : (normalizedFactors J).count q.asIdeal = 1 :=
    (Ideal.IsDedekindDomain.ramificationIdx_eq_normalizedFactors_count
      p.asIdeal q.asIdeal hJ).symm.trans
      (Ideal.ramificationIdx_eq_one q.asIdeal (𝓞 K))
  rw [hfac, Multiset.count_replicate_self] at hcount
  change J.IsPrime
  rw [← Ideal.prod_normalizedFactors_eq_self hJ, hfac, Multiset.prod_replicate, hcount, pow_one]
  exact q.isPrime

end NumberFields

section SelectedCompletion

open scoped WithZero

variable {K L : Type} [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]
variable {F : Type u} [Field F] [TopologicalSpace F] [IsTopologicalRing F]
variable {E : Type v} [Field E] [Algebra F E] [TopologicalSpace E] [IsTopologicalRing E]
  [IsModuleTopology F E]

private theorem equivariant_tensor_comparison
    (p : HeightOneSpectrum (𝓞 K)) (q : HeightOneSpectrum (𝓞 L)) [hq : q.asIdeal.LiesOver p.asIdeal]
    (hunique : ∀ r : HeightOneSpectrum (𝓞 L), r.asIdeal.LiesOver p.asIdeal → r = q)
    (φ : p.adicCompletion K ≃+* F) (η : q.adicCompletion L ≃+* E)
    (hφ : Continuous φ) (hη : Continuous η) (hηinv : Continuous η.symm)
    (hbase : ∀ x : K, η (algebraMap L (q.adicCompletion L) (algebraMap K L x)) =
      algebraMap F E (φ (algebraMap K (p.adicCompletion K) x)))
    (σK : L ≃ₐ[K] L) (σ : E ≃ₐ[F] E)
    (hσ : ∀ x : L, σ (η (algebraMap L (q.adicCompletion L) x)) =
      η (algebraMap L (q.adicCompletion L) (σK x))) :
    ∃ ψ : p.adicCompletion K ⊗[K] L ≃+* E,
      (∀ a : p.adicCompletion K, ψ (a ⊗ₜ[K] (1 : L)) = algebraMap F E (φ a)) ∧
      (∀ y : p.adicCompletion K ⊗[K] L,
        ψ (Algebra.TensorProduct.congr
          (AlgEquiv.refl : p.adicCompletion K ≃ₐ[p.adicCompletion K] _) σK y) = σ (ψ y)) ∧
      letI : TopologicalSpace (p.adicCompletion K ⊗[K] L) :=
        moduleTopology (p.adicCompletion K) (p.adicCompletion K ⊗[K] L)
      Continuous ψ ∧ Continuous ψ.symm := by
  let r : FinitePlacesAbove L p := ⟨q, hq⟩
  let : Unique (FinitePlacesAbove L p) := ⟨⟨r⟩, fun z => Subtype.ext (hunique z.1 z.2)⟩
  let comparison : p.adicCompletion K ⊗[K] L ≃ₐ[p.adicCompletion K] q.adicCompletion L :=
    (AlgEquiv.ofBijective (finiteTensorMap p) (completedTensorComparison K L |>.1 p)).trans
      (AlgEquiv.ofRingEquiv (f := RingEquiv.piUnique (fun z : FinitePlacesAbove L p =>
        z.1.adicCompletion L)) (fun _ => rfl))
  let ψ : p.adicCompletion K ⊗[K] L ≃+* E := comparison.toRingEquiv.trans η
  have htmul (a : p.adicCompletion K) (x : L) :
      ψ (a ⊗ₜ[K] x) = η (FiniteExtension.completionMap p q a) *
        η (algebraMap L (q.adicCompletion L) x) := by
    change η (finiteTensorMap p (a ⊗ₜ[K] x) r) = _
    rw [finiteTensorMap_tmul, map_mul]
  have : T2Space E := T2Space.of_injective_continuous η.symm.injective hηinv
  have hscalar (a : p.adicCompletion K) :
      η (FiniteExtension.completionMap p q a) = algebraMap F E (φ a) := by
    have halg : Continuous (algebraMap F E) :=
      IsModuleTopology.continuous_of_linearMap (Algebra.linearMap F E)
    refine congrFun ((p.denseRange_algebraMap K).equalizer
      (hη.comp (FiniteExtension.continuous_completionMap p q)) (halg.comp hφ) ?_) a
    funext x
    simpa only [Function.comp_apply, FiniteExtension.completionMap_coe] using hbase x
  refine ⟨ψ, fun a => by rw [htmul, map_one, map_one, mul_one, hscalar], ?_, ?_⟩
  · intro y
    induction y using TensorProduct.inductionOn with
    | tmul a x =>
      change ψ (a ⊗ₜ[K] σK x) = σ (ψ (a ⊗ₜ[K] x))
      rw [htmul, htmul, map_mul, hscalar a, σ.commutes, hσ]
    | add x y hx hy => simp only [map_add, hx, hy]
  · let : TopologicalSpace (p.adicCompletion K ⊗[K] L) :=
      moduleTopology (p.adicCompletion K) (p.adicCompletion K ⊗[K] L)
    let : NontriviallyNormedField (p.adicCompletion K) :=
      Valued.toNontriviallyNormedField (p.adicCompletion K) ℤᵐ⁰
    have : IsModuleTopology (p.adicCompletion K) (q.adicCompletion L) :=
      isModuleTopologyOfFiniteDimensional
    have : ContinuousAdd (p.adicCompletion K ⊗[K] L) :=
      ModuleTopology.continuousAdd (p.adicCompletion K) (p.adicCompletion K ⊗[K] L)
    exact ⟨hη.comp (IsModuleTopology.continuous_of_linearMap comparison.toLinearMap),
      (IsModuleTopology.continuous_of_linearMap comparison.symm.toLinearMap).comp hηinv⟩

end SelectedCompletion

/-- Every cyclic extension of characteristic-zero local fields has the requested
equivariant globalization and auxiliary split and inert places. -/
theorem cyclicFieldGlobalization : CyclicFieldGlobalizationStatement.{u, v} := by
  classical
  intro F _ _ topologyF _ _ E _ _ topologyE _ _ σ l hcyc hfield
  let : Field E := hfield.toField
  have : FiniteDimensional F E := hcyc.1
  have : IsGalois F E := hcyc.isGalois
  let p := CharZeroLocalField.residueChar F
  have : Fact p.Prime := CharZeroLocalField.fact_residueChar_prime F
  let : Algebra (Padic p) F := CharZeroLocalField.padicAlgebra F
  have : FiniteDimensional (Padic p) F := CharZeroLocalField.finiteDimensional F
  let : Algebra (Padic p) E := ((algebraMap F E).comp (algebraMap (Padic p) F)).toAlgebra
  have : IsScalarTower (Padic p) F E := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : FiniteDimensional (Padic p) E := FiniteDimensional.trans (Padic p) F E
  let Fp := PadicField.ofField (p := p) F
  let Ep := PadicField.ofField (p := p) E
  have : IsModuleTopology (Padic p) F := CharZeroLocalField.isModuleTopology F
  have : T2Space F := HarmonicAnalysis.GeneralLocalField.t2Space F
  let coordinates := (Module.finBasis F E).equivFun
  have : T2Space E := T2Space.of_injective_continuous coordinates.injective
    (IsModuleTopology.continuous_of_linearMap coordinates.toLinearMap)
  have : ContinuousSMul (Padic p) E := continuousSMul_of_algebraMap _ _
    ((IsModuleTopology.continuous_of_linearMap (Algebra.linearMap F E)).comp
      (CharZeroLocalField.continuous_padicEmbedding F))
  have : IsModuleTopology (Padic p) E := isModuleTopologyOfFiniteDimensional
  have hFtop : topologyF = Fp.canonicalTopology :=
    eq_moduleTopology (Padic p) F
  have hEtop : topologyE = Ep.canonicalTopology :=
    eq_moduleTopology (Padic p) E
  have hReal := Global.totallyRealGaloisRealization p inferInstance Fp Ep
    (inferInstance : Algebra F E) (inferInstance : IsScalarTower (Padic p) F E)
    (inferInstance : IsGalois F E)
  dsimp only [Fp, Ep, PadicField.ofField] at hReal
  obtain ⟨K, L, instK, instL, nfK, nfL, algKL, galKL, _, realL, hdegree,
    p₀, q₀, φ, η, θ, hq₀, hunique, hφ, hφinv, hη, hηinv, hbase, haction⟩ := hReal
  let : Field K := instK
  let : Field L := instL
  have : NumberField K := nfK
  have : NumberField L := nfL
  let : Algebra K L := algKL
  have : IsGalois K L := galKL
  have : IsTotallyReal L := realL
  have : q₀.asIdeal.LiesOver p₀.asIdeal := hq₀
  change p₀.adicCompletion K ≃+* F at φ
  change q₀.adicCompletion L ≃+* E at η
  change (L ≃ₐ[K] L) ≃* (E ≃ₐ[F] E) at θ
  let σK : L ≃ₐ[K] L := θ.symm σ
  have hord : orderOf σK = l :=
    (orderOf_injective θ.symm.toMonoidHom θ.symm.injective σ).trans hcyc.2.2.2.1
  have hdeg : Module.finrank K L = l := hdegree.trans hcyc.2.1
  have hgen : Subgroup.zpowers σK = ⊤ := by
    apply (Subgroup.card_eq_iff_eq_top _).mp
    rw [Nat.card_zpowers, IsGalois.card_aut_eq_finrank, hdeg, hord]
  have hcycK : IsCyclicAlgebra σK l := by
    refine ⟨inferInstance, hdeg, inferInstance, hord, fun x hx => ?_⟩
    apply (IsGalois.mem_range_algebraMap_iff_fixed x).mpr
    intro τ
    exact smul_eq_self_of_mem_zpowers (by rw [hgen]; trivial) hx
  have hφ' : Continuous φ := by
    rw [hFtop]
    exact hφ
  have hφinv' : Continuous φ.symm := by
    rw [hFtop]
    exact hφinv
  have hη' : Continuous η := by
    rw [hEtop]
    exact hη
  have hηinv' : Continuous η.symm := by
    rw [hEtop]
    exact hηinv
  have hσ (x : L) : σ (η (algebraMap L (q₀.adicCompletion L) x)) =
      η (algebraMap L (q₀.adicCompletion L) (σK x)) := by
    have hθ : θ σK = σ := θ.apply_symm_apply σ
    rw [← hθ]
    exact haction σK x
  obtain ⟨ψ, hψbase, hψaction, hψcont⟩ :=
    equivariant_tensor_comparison p₀ q₀ hunique φ η hφ' hη' hηinv' hbase σK σ hσ
  refine ⟨K, L, instK, instL, nfK, nfL, algKL, σK, hcycK,
    fun w => cyclicShiftSplit_infinite w σK l hcycK,
    ⟨p₀, φ, ψ, hφ', hφinv', hψbase, hψaction, hψcont⟩, ?_, ?_⟩
  · intro S N
    obtain ⟨w, hw, hnorm, z, hzo, hzu, hf⟩ :=
      exists_bounded_away_frobenius (1 : L ≃ₐ[K] L) S N
    exact ⟨w, hw, hnorm, cyclicShiftSplit_finite w z hf σK l hcycK⟩
  · intro S N
    obtain ⟨w, hw, hnorm, z, hzo, hzu, hf⟩ := exists_bounded_away_frobenius σK S N
    exact ⟨w, hw, hnorm, prime_map_of_generator_frobenius w z σK hgen hf⟩

end Langlands.TraceFormula
