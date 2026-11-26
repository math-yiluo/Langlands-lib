import Langlands.Global.NormOneIdeleClassCompact
import Langlands.ClassFieldTheory.Global.IntegralIdeleClassQuotientFinite
import Langlands.Galois.HeckeAvatarFinitePart
import Langlands.Global.AdelesLocallyCompactProof
import Langlands.Global.Arithmetic.CMInfinityExtension
import Langlands.Global.Factors.HeckeFiniteRamification
import Langlands.Global.FiniteAdelicGroupCompactOpenBasisProof
import Langlands.Global.IntegralFiniteAdeles
import Mathlib.Algebra.Field.ULift
import Mathlib.FieldTheory.AlgebraicClosure

/-! # The common coefficient field of the finite idele character -/

noncomputable section

universe uK uL

namespace Langlands.GaloisRepresentation

open Langlands.Global Langlands.ClassFieldTheory.Global NumberField IsDedekindDomain
open CMUnramifiedInfinity (infinityDiagonal coordinate_diagonal_units)
open HeckeFunctionalEquation (integralUnitIdeles)

variable {K : Type uK} [Field K] [NumberField K]

private theorem isOpen_finitePart_ker (χ : HeckeCharacter K) :
    IsOpen (χ.atFinite.toMonoidHom.ker : Set (FiniteIdeles K)) := by
  let : LocallyCompactSpace (FiniteAdeles K) := finiteAdeles_locallyCompactSpace K
  let : TotallyDisconnectedSpace (FiniteAdeles K) := finiteAdeles_totallyDisconnectedSpace K
  let : TotallyDisconnectedSpace (FiniteIdeles K) :=
    ⟨isTotallyDisconnected_of_image Units.continuous_val.continuousOn Units.val_injective
      (isTotallyDisconnected_of_totallyDisconnectedSpace _)⟩
  let : NonarchimedeanGroup (FiniteIdeles K) := by
    constructor
    intro U hU
    obtain ⟨H, _, hH⟩ :=
      ((Langlands.Topology.LocallyProfiniteProof.vanDantzig (FiniteIdeles K)).mp
        Langlands.Topology.isLocallyProfinite_of_mathlib).2 U hU
    exact ⟨H, hH⟩
  exact Langlands.isOpen_ker_of_continuous_complex_character _ χ.atFinite.continuous

private def finitePart (K : Type uK) [Field K] [NumberField K] :
    Ideles K →ₜ* FiniteIdeles K where
  toMonoidHom := (MonoidHom.snd _ _).comp (ideleProductEquiv K).toMonoidHom
  continuous_toFun := continuous_snd.comp (ideleProductEquiv K).continuous

private theorem finitePart_inclusion (x : FiniteIdeles K) :
    finitePart K (finiteIdelesInclusion K x) = x :=
  congrArg Prod.snd ((ideleProductEquiv K).apply_symm_apply (1, x))

private abbrev IntegralUnitProduct (K : Type uK) [Field K] [NumberField K] :=
  ∀ v : Global.FinitePlace K, (v.adicCompletionIntegers K)ˣ

private def integralUnitValues (χ : HeckeCharacter K) : IntegralUnitProduct K →ₜ* ℂˣ :=
  χ.atFinite.comp ((finitePart K).comp (integralUnitIdeles K))

private theorem finite_integralUnitValues (χ : HeckeCharacter K)
    (hopen : IsOpen (χ.atFinite.toMonoidHom.ker : Set (FiniteIdeles K))) :
    Finite (integralUnitValues χ).toMonoidHom.range := by
  let : ∀ v : Global.FinitePlace K, CompactSpace (v.adicCompletionIntegers K)ˣ := fun v => by
    let : CompactSpace (v.adicCompletionIntegers K) :=
      isCompact_iff_compactSpace.mp (isCompact_adicCompletionIntegers K v)
    infer_instance
  let θ := (integralUnitValues χ).toMonoidHom
  have hopen' : IsOpen (θ.ker : Set (IntegralUnitProduct K)) :=
    hopen.preimage ((finitePart K).comp (integralUnitIdeles K)).continuous
  let : Finite (IntegralUnitProduct K ⧸ θ.ker) := θ.ker.quotient_finite_of_isOpen hopen'
  exact Finite.of_equiv _ (QuotientGroup.quotientKerEquivRange θ).toEquiv

private theorem finitePart_integral {x : Ideles K} (hx : x ∈ integralIdeles K) :
    ∃ u : IntegralUnitProduct K, finitePart K (integralUnitIdeles K u) = finitePart K x := by
  have hunit (v : Global.FinitePlace K) :
      x.val.2 v ∈ v.adicCompletionIntegers K ∧ x.inv.2 v ∈ v.adicCompletionIntegers K :=
    (HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one
      (a := ideleCoordinate v x)).mpr ((mem_integralIdeles_iff x).mp hx v)
  let u : IntegralUnitProduct K := fun v =>
    { val := ⟨x.val.2 v, (hunit v).1⟩
      inv := ⟨x.inv.2 v, (hunit v).2⟩
      val_inv := Subtype.ext (congrArg (fun y : Adeles K => y.2 v) x.val_inv)
      inv_val := Subtype.ext (congrArg (fun y : Adeles K => y.2 v) x.inv_val) }
  refine ⟨u, Units.ext ?_⟩
  apply RestrictedProduct.ext
  intro v
  rfl

private theorem principalValue_mem [IsTotallyComplex K] (χ : HeckeCharacter K)
    (t : InfinityType K) (ht : χ.HasPrescribedInfinityComponent (InfinityType.toCharacter t))
    (E : IntermediateField ℚ ℂ) (hE : ∀ (σ : K →+* ℂ) (a : K), σ a ∈ E) (a : Kˣ) :
    (χ.atFinite (finitePart K (diagonalUnits K a)) : ℂ) ∈ E := by
  have hinfty : (χ.atInfinity (infinityDiagonal a) : ℂ) ∈ E := by
    unfold HeckeCharacter.HasPrescribedInfinityComponent at ht
    rw [ht, InfinityType.toCharacter_apply, Units.coe_prod]
    apply E.prod_mem
    intro v _
    simp only [Units.val_mul, Units.val_zpow_eq_zpow_val, Units.coe_star,
      coordinate_diagonal_units, Units.coe_map]
    exact E.mul_mem (zpow_mem (hE v.embedding a) _)
      (zpow_mem (hE (ComplexEmbedding.conjugate v.embedding) a) _)
  have hsplit : infiniteIdelesInclusion K (infinityDiagonal a) *
      finiteIdelesInclusion K (finitePart K (diagonalUnits K a)) = diagonalUnits K a := by
    let e := ideleProductEquiv K
    apply e.injective
    rw [map_mul]
    change e (e.symm ((e (diagonalUnits K a)).1, 1)) *
      e (e.symm (1, (e (diagonalUnits K a)).2)) = e (diagonalUnits K a)
    rw [e.apply_symm_apply, e.apply_symm_apply]
    exact Prod.ext (mul_one _) (one_mul _)
  have hprincipal : χ.atInfinity (infinityDiagonal a) *
      χ.atFinite (finitePart K (diagonalUnits K a)) = 1 := by
    calc
      _ = χ.onIdeles (infiniteIdelesInclusion K (infinityDiagonal a) *
            finiteIdelesInclusion K (finitePart K (diagonalUnits K a))) :=
        (map_mul χ.onIdeles _ _).symm
      _ = 1 := (congrArg χ.onIdeles hsplit).trans (χ.onIdeles_diagonalUnits a)
  rw [eq_inv_of_mul_eq_one_right hprincipal, Units.val_inv_eq_inv_val]
  exact E.inv_mem hinfty

private theorem residualMap_eq_one {x : Ideles K} (hx : Langlands.Global.NormOneIdeleClass.toIntegralQuotient K x = 1) :
    ∃ y ∈ integralIdeles K, ∃ a : Kˣ, x = y * diagonalUnits K a := by
  have hc : ideleClassMap K x ∈ integralIdeleClasses K :=
    (QuotientGroup.eq_one_iff _).mp hx
  obtain ⟨y, hy, hclass⟩ := (mem_integralIdeleClasses_iff _).mp hc
  have hclass' : ideleClassMap K y = ideleClassMap K x := hclass
  have hdiv : ideleClassMap K (x / y) = 1 := by
    rw [map_div, hclass', div_self']
  obtain ⟨a, ha⟩ : x / y ∈ principalIdeles K := (QuotientGroup.eq_one_iff _).mp hdiv
  exact ⟨y, hy, a, by rw [ha, mul_comm, div_mul_cancel]⟩

private def embeddingField (K : Type uK) [Field K] [NumberField K] : IntermediateField ℚ ℂ :=
  ⨆ σ : K →+* ℂ, ((RingHom.equivRatAlgHom K ℂ) σ).fieldRange

private theorem embedding_mem (σ : K →+* ℂ) (x : K) : σ x ∈ embeddingField K :=
  (le_iSup (fun τ : K →+* ℂ => ((RingHom.equivRatAlgHom K ℂ) τ).fieldRange) σ)
    (AlgHom.mem_fieldRange.mpr ⟨x, rfl⟩)

private theorem finiteDimensional_embeddingField : FiniteDimensional ℚ (embeddingField K) := by
  let : ∀ σ : K →+* ℂ, FiniteDimensional ℚ ((RingHom.equivRatAlgHom K ℂ) σ).fieldRange :=
    fun σ => ((RingHom.equivRatAlgHom K ℂ) σ).equivFieldRange.toLinearEquiv.finiteDimensional
  unfold embeddingField
  infer_instance

private theorem exists_lift_finitePart {L : Type uL} [Field L] (χ : HeckeCharacter K)
    (ι : L →+* ℂ) (hvalues : ∀ x, (χ.atFinite x : ℂ) ∈ Set.range ι)
    (hopen : IsOpen (χ.atFinite.toMonoidHom.ker : Set (FiniteIdeles K))) :
    ∃ φ : FiniteIdeles K →* Lˣ, IsHeckeFinitePart χ ι φ := by
  let f := Units.map ι.toMonoidHom
  have hf : Function.Injective f := Units.map_injective ι.injective
  have h : ∀ x, χ.atFinite x ∈ f.range := by
    intro x
    obtain ⟨b, hb⟩ := hvalues x
    have hne : b ≠ 0 := by
      intro he
      exact (χ.atFinite x).ne_zero (by simpa only [he, map_zero] using hb.symm)
    exact ⟨Units.mk0 b hne, Units.ext hb⟩
  let g := χ.atFinite.toMonoidHom.codRestrict f.range h
  let φ := (MonoidHom.ofInjective hf).symm.toMonoidHom.comp g
  have hφ (x : FiniteIdeles K) : f (φ x) = χ.atFinite x :=
    MonoidHom.apply_ofInjective_symm hf (g x)
  have hker : φ.ker = χ.atFinite.toMonoidHom.ker := by
    ext x
    change φ x = 1 ↔ χ.atFinite x = 1
    rw [← hφ x, ← map_one f, hf.eq_iff]
  exact ⟨φ, hker ▸ hopen, hφ⟩

/-- The finite idele character and the complex embeddings of the base field admit a common
number field of definition. -/
theorem algebraicHeckeFinitePart : AlgebraicHeckeFinitePartStatement.{uK, uL} := by
  classical
  intro K _ _ _ χ t ht
  have hopen := isOpen_finitePart_ker χ
  let θ := integralUnitValues χ
  let : Finite θ.toMonoidHom.range := finite_integralUnitValues χ hopen
  let U : Set ℂ := Set.range fun z : θ.toMonoidHom.range => ((z : ℂˣ) : ℂ)
  let : Finite U := (Set.finite_range _).to_subtype
  have hU : ∀ z ∈ U, IsIntegral ℚ z := by
    rintro _ ⟨z, rfl⟩
    have hz : z ^ Nat.card θ.toMonoidHom.range = 1 := pow_card_eq_one'
    have hpow : ((z : ℂˣ) : ℂ) ^ Nat.card θ.toMonoidHom.range = 1 := by
      exact (map_pow (Units.coeHom ℂ) (z : ℂˣ) _).symm.trans
        (congrArg (fun w : θ.toMonoidHom.range => ((w : ℂˣ) : ℂ)) hz)
    exact (IsAlgebraic.of_pow Nat.card_pos (hpow.symm ▸ isAlgebraic_one)).isIntegral
  -- Principal and integral values lie in this first field.
  let E := embeddingField K ⊔ IntermediateField.adjoin ℚ U
  let : FiniteDimensional ℚ (embeddingField K) := finiteDimensional_embeddingField
  let : FiniteDimensional ℚ (IntermediateField.adjoin ℚ U) :=
    IntermediateField.finiteDimensional_adjoin hU
  let : FiniteDimensional ℚ E := IntermediateField.finiteDimensional_sup _ _
  have hEmb : embeddingField K ≤ E := le_sup_left
  have hUnits : IntermediateField.adjoin ℚ U ≤ E := le_sup_right
  have hE (σ : K →+* ℂ) (x : K) : σ x ∈ E := hEmb (embedding_mem σ x)
  let ψ := χ.atFinite.toMonoidHom.comp (finitePart K).toMonoidHom
  have hkerValue (x : Ideles K) (hx : Langlands.Global.NormOneIdeleClass.toIntegralQuotient K x = 1) : (ψ x : ℂ) ∈ E := by
    obtain ⟨y, hy, a, ha⟩ := residualMap_eq_one hx
    obtain ⟨u, hu⟩ := finitePart_integral hy
    have hy' : (ψ y : ℂ) ∈ E := by
      change (χ.atFinite (finitePart K y) : ℂ) ∈ E
      rw [← hu]
      exact hUnits (IntermediateField.subset_adjoin ℚ U
        ⟨⟨θ u, ⟨u, rfl⟩⟩, rfl⟩)
    rw [ha, map_mul, Units.val_mul]
    exact E.mul_mem hy' (principalValue_mem χ t ht E hE a)
  -- Each representative has a positive power in the residual kernel.
  let : Finite (IntegralIdeleClassQuotient K) := integralIdeleClassQuotientFinite K
  obtain ⟨r, hr⟩ := (Langlands.Global.NormOneIdeleClass.toIntegralQuotient_surjective K).hasRightInverse
  let V : Set ℂ := Set.range fun i : IntegralIdeleClassQuotient K => (ψ (r i) : ℂ)
  let : Finite V := (Set.finite_range _).to_subtype
  have hV : ∀ z ∈ V, IsIntegral ℚ z := by
    rintro _ ⟨i, rfl⟩
    let n := Nat.card (IntegralIdeleClassQuotient K)
    have hn : 0 < n := Nat.card_pos
    have hq : Langlands.Global.NormOneIdeleClass.toIntegralQuotient K (r i ^ n) = 1 := by
      rw [map_pow]
      exact pow_card_eq_one'
    have hpow := hkerValue (r i ^ n) hq
    rw [map_pow, Units.val_pow_eq_pow_val] at hpow
    exact (IsAlgebraic.of_pow hn (mem_algebraicClosure_iff.mp
      (le_algebraicClosure ℚ ℂ E hpow))).isIntegral
  let F := E ⊔ IntermediateField.adjoin ℚ V
  let : FiniteDimensional ℚ (IntermediateField.adjoin ℚ V) :=
    IntermediateField.finiteDimensional_adjoin hV
  let : FiniteDimensional ℚ F := IntermediateField.finiteDimensional_sup _ _
  let : NumberField F := {}
  have hEF : E ≤ F := le_sup_left
  have hReps : IntermediateField.adjoin ℚ V ≤ F := le_sup_right
  have hfinite (x : FiniteIdeles K) : (χ.atFinite x : ℂ) ∈ F := by
    let z := finiteIdelesInclusion K x
    let i := Langlands.Global.NormOneIdeleClass.toIntegralQuotient K z
    have hd : Langlands.Global.NormOneIdeleClass.toIntegralQuotient K (z / r i) = 1 := by
      rw [map_div, hr i]
      exact div_self' _
    have hdecomp : z / r i * r i = z := div_mul_cancel _ _
    have hvalue : (ψ z : ℂ) ∈ F := by
      rw [← hdecomp, map_mul, Units.val_mul]
      exact F.mul_mem (hEF (hkerValue _ hd))
        (hReps (IntermediateField.subset_adjoin ℚ V ⟨i, rfl⟩))
    change (χ.atFinite (finitePart K z) : ℂ) ∈ F at hvalue
    rwa [finitePart_inclusion] at hvalue
  let e : F ≃+* ULift.{uL} F := ULift.ringEquiv.symm
  let ι : ULift.{uL} F →+* ℂ := F.val.toRingHom.comp e.symm.toRingHom
  let emb (σ : K →+* ℂ) : K →+* ULift.{uL} F :=
    e.toRingHom.comp (σ.codRestrict F.toSubfield fun x => hEF (hE σ x))
  have hι (σ : K →+* ℂ) : ι.comp (emb σ) = σ := by
    ext x
    rfl
  obtain ⟨φ, hφ⟩ := exists_lift_finitePart χ ι
    (fun x => ⟨e ⟨_, hfinite x⟩, rfl⟩) hopen
  obtain ⟨T, hT⟩ := HeckeFunctionalEquation.exists_finset_isUnramifiedAt K χ
  let S := T.filter fun v => ¬χ.IsUnramifiedAt v
  refine ⟨ULift.{uL} F, inferInstance, NumberField.of_ringEquiv F (ULift.{uL} F) e,
    ι, emb, φ, S, hι, hφ, ?_⟩
  intro v
  by_cases hv : v ∈ T
  · simp [S, hv]
  · simp [S, hv, hT v hv]

end Langlands.GaloisRepresentation
