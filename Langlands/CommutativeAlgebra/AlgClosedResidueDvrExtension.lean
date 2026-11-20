import Langlands.CommutativeAlgebra.MaximalUniformizerSubalgebra
import Mathlib.Algebra.Polynomial.Eval.Irreducible
import Mathlib.Algebra.Polynomial.Lifts
import Mathlib.FieldTheory.AlgebraicClosure
import Mathlib.RingTheory.DiscreteValuationRing.TFAE

/-! # DVR extensions with algebraically closed residue field -/

noncomputable section

universe u

open IsLocalRing Polynomial

namespace Langlands.CommutativeAlgebra

private theorem adjoinRoot_isDomain {S : Type*} [CommRing S] [IsDomain S]
    [IsDiscreteValuationRing S] {f : S[X]} (hf : f.Monic)
    (hi : Irreducible (f.map (residue S))) : IsDomain (AdjoinRoot f) :=
  AdjoinRoot.isDomain_of_prime
    ((Polynomial.Monic.irreducible_of_irreducible_map (residue S) f hf hi).prime)

private theorem adjoinRoot_isLocalRing {S : Type*} [CommRing S] [IsLocalRing S]
    {f : S[X]} (hf : f.Monic) (hi : Irreducible (f.map (residue S))) :
    ∃ _ : IsLocalRing (AdjoinRoot f),
      maximalIdeal (AdjoinRoot f) = (maximalIdeal S).map (algebraMap S (AdjoinRoot f)) := by
  let T := AdjoinRoot f
  let m : Ideal T := (maximalIdeal S).map (algebraMap S T)
  have hm : m.IsMaximal := by
    apply Ideal.Quotient.maximal_of_isField
    exact (AdjoinRoot.quotAdjoinRootEquivQuotPolynomialQuot (maximalIdeal S) f).toMulEquiv.isField
      (AdjoinRoot.isField_iff_irreducible.mpr hi)
  have : IsLocalRing T := IsLocalRing.of_unique_max_ideal ⟨m, hm, fun n hn => by
    have : Algebra.IsIntegral S T := AdjoinRoot.isIntegral_of_monic hf
    have hunder : n.under S = maximalIdeal S :=
      IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_under_of_isIntegral_of_isMaximal n)
    have hmn : m ≤ n := Ideal.map_le_iff_le_comap.mpr hunder.ge
    exact (hm.eq_of_le hn.ne_top hmn).symm⟩
  exact ⟨this, (IsLocalRing.eq_maximalIdeal hm).symm⟩

namespace FixedUniformizer

variable {R Ω : Type*} [CommRing R] [Field Ω] [Algebra R Ω]
  {t : R} {S : Subalgebra R Ω} (hmax : Maximal (FixedUniformizer t) S)

include hmax

private theorem surjective_of_extension
    (T : Type*) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T]
    [Algebra S T] (htT : Irreducible (algebraMap S T (algebraMap R S t)))
    (e : T →ₐ[S] Ω) (he : Function.Injective e) :
    Function.Surjective (algebraMap S T) := by
  let : Algebra R T := ((algebraMap S T).comp (algebraMap R S)).toAlgebra
  have : IsScalarTower R S T := IsScalarTower.of_algebraMap_eq' rfl
  let eR : T →ₐ[R] Ω := e.restrictScalars R
  let U : Subalgebra R Ω := eR.range
  let eU : T ≃ₐ[R] U := AlgEquiv.ofInjective eR he
  have htU : eU (algebraMap S T (algebraMap R S t)) = algebraMap R U t := by
    rw [← IsScalarTower.algebraMap_apply R S T, eU.commutes]
  have hT := of_irreducible htT
  have hU : FixedUniformizer t U := by
    refine ⟨?_, fun y => ?_⟩
    · intro h
      apply hT.1
      simpa only [← htU, eU.symm_apply_apply] using h.map eU.symm
    · rcases hT.2 (eU.symm y) with h0 | ⟨n, z, hz, h⟩
      · exact Or.inl (eU.symm.injective (by simpa only [map_zero] using h0))
      · refine Or.inr ⟨n, eU z, hz.map eU, ?_⟩
        simpa only [eU.apply_symm_apply, map_mul, map_pow, htU] using congrArg eU h
  have hSU : S ≤ U := by
    intro x hx
    exact ⟨algebraMap S T ⟨x, hx⟩, e.commutes ⟨x, hx⟩⟩
  have hUS : U ≤ S := hmax.2 hU hSU
  intro y
  let a : S := ⟨e y, hUS (eR.mem_range_self y)⟩
  exact ⟨a, he (e.commutes a)⟩

variable [IsDomain R] [IsAlgClosed Ω] [FaithfulSMul R Ω] [IsDiscreteValuationRing S]

/-- A maximal subalgebra preserving a uniformizer has algebraically closed residue field. -/
theorem isAlgClosed_residueField : IsAlgClosed (ResidueField S) := by
  apply IsAlgClosed.of_exists_root
  intro p hp hi
  obtain ⟨f, hfmap, _, hf⟩ := lifts_and_degree_eq_and_monic
    (mem_lifts_of_surjective (residue_surjective (R := S)) p) hp
  have hif : Irreducible (f.map (residue S)) := hfmap ▸ hi
  have hdeg : 0 < f.degree := by
    rw [← hf.degree_map (residue S), hfmap]
    exact degree_pos_of_irreducible hi
  let T := AdjoinRoot f
  have : IsDomain T := adjoinRoot_isDomain hf hif
  obtain ⟨hLocal, hmaxT⟩ := adjoinRoot_isLocalRing hf hif
  let tS : S := algebraMap R S t
  have htS : Irreducible tS := irreducible hmax.1
  have hspan : maximalIdeal T = Ideal.span {algebraMap S T tS} := by
    rw [hmaxT, htS.maximalIdeal_eq, Ideal.map_span, Set.image_singleton]
  have hfaithful : FaithfulSMul S T := AdjoinRoot.faithfulSMul_of_monic_of_degree_pos hf hdeg
  have ht0 : algebraMap S T tS ≠ 0 := by
    simpa only [map_zero] using (FaithfulSMul.algebraMap_injective S T).ne htS.ne_zero
  have hnF : ¬IsField T := by
    rwa [isField_iff_maximalIdeal_eq, hspan, Ideal.span_singleton_eq_bot]
  have hprincipal : (maximalIdeal T).IsPrincipal := ⟨_, hspan⟩
  have : IsDiscreteValuationRing T :=
    ((IsDiscreteValuationRing.TFAE T hnF).out 5 1).mp hprincipal
  have htT : Irreducible (algebraMap S T tS) :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer _).mpr hspan
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_aeval_eq_zero_of_injective Ω Subtype.val_injective f hdeg.ne'
  let e : T →ₐ[S] Ω := AdjoinRoot.liftAlgHom f (Algebra.ofId S Ω) x hx
  have hmap : e (algebraMap S T tS) ≠ 0 := by
    rw [e.commutes]
    intro h
    apply htS.ne_zero
    exact (show Function.Injective (algebraMap S Ω) from Subtype.val_injective)
      (h.trans (map_zero (algebraMap S Ω)).symm)
  have he : Function.Injective e := by
    apply (injective_iff_map_eq_zero e).mpr
    intro y hy
    by_contra hy0
    obtain ⟨n, v, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hy0 htT
    rw [map_mul, map_pow] at hy
    exact mul_ne_zero (v.isUnit.map e).ne_zero (pow_ne_zero n hmap) hy
  obtain ⟨a, ha⟩ := surjective_of_extension hmax T htT e he (AdjoinRoot.root f)
  have haf : f.eval a = 0 := by
    apply FaithfulSMul.algebraMap_injective S T
    rw [← eval₂_at_apply, ← aeval_def, ha, AdjoinRoot.aeval_eq, AdjoinRoot.mk_self, map_zero]
  refine ⟨residue S a, ?_⟩
  rw [← hfmap, eval_map, eval₂_at_apply, haf, map_zero]

end FixedUniformizer

/-- A DVR admits a same-universe faithfully flat DVR extension with algebraically
closed residue field. -/
theorem exists_algClosedResidueDvrExtension (R : Type u) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] :
    ∃ (S : Type u) (_ : CommRing S) (_ : IsDomain S) (_ : IsDiscreteValuationRing S)
      (_ : Algebra R S), Module.FaithfullyFlat R S ∧ IsAlgClosed (ResidueField S) := by
  let Ω := AlgebraicClosure (FractionRing R)
  have : FaithfulSMul R Ω := (faithfulSMul_iff_algebraMap_injective R Ω).mpr (by
    rw [IsScalarTower.algebraMap_eq R (FractionRing R) Ω]
    exact (algebraMap (FractionRing R) Ω).injective.comp (IsFractionRing.injective R _))
  obtain ⟨t, ht⟩ := IsDiscreteValuationRing.exists_irreducible R
  obtain ⟨S, hS⟩ := FixedUniformizer.exists_maximal (Ω := Ω) ht
  have : IsDiscreteValuationRing S := FixedUniformizer.isDiscreteValuationRing ht.ne_zero hS.1
  have : IsLocalHom (algebraMap R S) := FixedUniformizer.isLocalHom ht hS.1
  exact ⟨S, inferInstance, inferInstance, inferInstance, inferInstance,
    Module.FaithfullyFlat.of_flat_of_isLocalHom, FixedUniformizer.isAlgClosed_residueField hS⟩

end Langlands.CommutativeAlgebra
