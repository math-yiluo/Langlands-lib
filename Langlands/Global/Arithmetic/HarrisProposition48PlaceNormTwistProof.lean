import Langlands.Global.Arithmetic.HarrisParityLocalTransportStatement
import Langlands.Global.Arithmetic.HenniartCompletionConjugation
import Langlands.Global.Factors.RelativeWeilAssemblyCharacters
import Langlands.Correspondence.BaseReciprocityCoherence
import Langlands.LocalFactor.DeligneHenniartInductionStep
import Mathlib.Data.Nat.Prime.Infinite
import Mathlib.RingTheory.Henselian

/-! # Actual finite-place norm twist in the Proposition 4.8 parity correction -/

noncomputable section

universe uF

namespace Langlands.Global.Harris

open AdelicFunctoriality CompletionPadic IsDedekindDomain
open LocalFactor.CommonClosure GeneralPosition Weil.Local
open Filter IsLocalRing Polynomial
open scoped NumberField WithZero Topology ValuativeRel AdelicFunctoriality.FiniteExtension

/-- A sufficiently large prime exponent detects integrality by a field equation. -/
private theorem integral_iff_exists_pow {K : Type*} [Field K]
    (v : Valuation K ℤᵐ⁰) [HenselianLocalRing v.valuationSubring]
    {p l : ℕ} (hp : p.Prime) (hl : l.Prime) (hpl : p < l)
    (hp0 : (p : K) ≠ 0) (hpv : v (p : K) < 1)
    (he : -WithZero.log (v (p : K)) < (l : ℤ)) (x : K) :
    v x ≤ 1 ↔ ∃ y : K, y ^ l = 1 + (p : K) * x ^ l := by
  constructor
  · intro hx
    let O := v.valuationSubring
    let z : O := ⟨x, hx⟩
    have hpO : (p : O) ∈ maximalIdeal O := v.mem_maximalIdeal_iff.mpr (by simpa using hpv)
    have hpR : (p : ResidueField O) = 0 := by
      rw [← map_natCast (residue O), residue_eq_zero_iff]
      exact hpO
    let : CharP (ResidueField O) p := (CharP.charP_iff_prime_eq_zero hp).mpr hpR
    have hlO : IsUnit (l : O) := by
      rw [← residue_ne_zero_iff_isUnit, map_natCast]
      exact CharP.cast_ne_zero_of_ne_of_prime _ hl hpl.ne
    let f : O[X] := X ^ l - C (1 + (p : O) * z ^ l)
    have hroot : f.eval 1 ∈ maximalIdeal O := by
      simpa only [f, eval_sub, eval_pow, eval_X, one_pow, eval_C, sub_add_cancel_left,
        Ideal.neg_mem_iff] using (maximalIdeal O).mul_mem_right (z ^ l) hpO
    have hder : IsUnit (f.derivative.eval 1) := by
      simpa only [f, derivative_sub, derivative_X_pow, derivative_C, sub_zero, eval_mul,
        eval_natCast, eval_pow, eval_X, one_pow, mul_one, one_mul, eval_C] using hlO
    obtain ⟨y, hy, -⟩ := HenselianLocalRing.is_henselian f
      (monic_X_pow_sub_C _ hl.ne_zero) 1 hroot hder
    have hy' : y ^ l = 1 + (p : O) * z ^ l := by
      simpa only [f, IsRoot, eval_sub, eval_pow, eval_X, eval_C, sub_eq_zero] using hy
    exact ⟨y, by simpa [z] using congrArg (fun a : O => (a : K)) hy'⟩
  · rintro ⟨y, hy⟩
    by_contra! hx
    -- In this case the logarithm is positive on `x` and negative on `p`.
    have hpval : v (p : K) ≠ 0 := v.ne_zero_iff.mpr hp0
    have hxval : v x ≠ 0 := (zero_lt_one.trans hx).ne'
    have ha : WithZero.log (v (p : K)) < 0 :=
      (WithZero.log_lt_iff_lt_exp hpval).mpr (by simpa using hpv)
    have hb : 0 < WithZero.log (v x) :=
      (WithZero.lt_log_iff_exp_lt hxval).mpr (by simpa using hx)
    have hm : WithZero.log (v ((p : K) * x ^ l)) =
        WithZero.log (v (p : K)) + (l : ℤ) * WithZero.log (v x) := by
      rw [map_mul, map_pow, WithZero.log_mul hpval (pow_ne_zero _ hxval),
        WithZero.log_pow, nsmul_eq_mul]
    have hm0 : v ((p : K) * x ^ l) ≠ 0 := by
      rw [map_mul, map_pow]
      exact mul_ne_zero hpval (pow_ne_zero _ hxval)
    have hbig : 1 < v ((p : K) * x ^ l) := by
      rw [← WithZero.exp_zero (M := ℤ), ← WithZero.lt_log_iff_exp_lt hm0, hm]
      have h := mul_le_mul_of_nonneg_left (show (1 : ℤ) ≤ WithZero.log (v x) by omega)
        (Int.natCast_nonneg l)
      linarith
    have hv : v (1 + (p : K) * x ^ l) = v ((p : K) * x ^ l) :=
      v.map_add_eq_of_lt_right (by simpa only [map_one] using hbig)
    -- The order of an `l`-th power is a multiple of `l`, forcing `l ∣ log (v p)`.
    have hlog := congrArg WithZero.log ((congrArg v hy).trans hv)
    rw [map_pow, WithZero.log_pow, nsmul_eq_mul, hm] at hlog
    have hdvd : (l : ℤ) ∣ WithZero.log (v (p : K)) :=
      ⟨WithZero.log (v y) - WithZero.log (v x), by linear_combination -hlog⟩
    have hle := Nat.le_of_dvd (Int.natAbs_pos.mpr ha.ne) (Int.natAbs_dvd_natAbs.mpr hdvd)
    rw [Int.natAbs_natCast] at hle
    omega

/-- The canonical discrete valuation and spectral norm have the same unit ball. -/
private theorem discreteValuation_le_one_iff_norm {p : ℕ} [Fact p.Prime]
    (A : PadicField p) (x : A.Carrier) :
    A.canonicalTopologicalData.discreteValuation x ≤ 1 ↔ A.canonicalNorm x ≤ 1 := by
  let T := A.canonicalTopologicalData
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let e := IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt A.Carrier
  change e (ValuativeRel.valuation A.Carrier x) ≤ 1 ↔ A.canonicalNorm x ≤ 1
  rw [← map_one e, e.strictMono.le_iff_le, ← (ValuativeRel.valuation A.Carrier).vle_one_iff,
    A.canonicalTopologicalData_vle]
  let := A.canonicalNormedField
  change ‖x‖ ≤ ‖(1 : A.Carrier)‖ ↔ ‖x‖ ≤ 1
  rw [norm_one]

/-- The valuation ring of the canonical discrete valuation is Henselian. -/
private theorem henselian_discreteValuation {p : ℕ} [Fact p.Prime] (A : PadicField p) :
    HenselianLocalRing A.canonicalTopologicalData.discreteValuation.valuationSubring := by
  let T := A.canonicalTopologicalData
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let e := IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt A.Carrier
  have he : (ValuativeRel.valuation A.Carrier).IsEquiv T.discreteValuation :=
    (Valuation.isEquiv_map_self_of_strictMono (v := ValuativeRel.valuation A.Carrier)
      e.toMonoidWithZeroHom e.strictMono).symm
  change HenselianLocalRing T.discreteValuation.valuationSubring
  rw [← (Valuation.isEquiv_iff_valuationSubring _ _).mp he]
  change HenselianLocalRing 𝒪[A.Carrier]
  let := IsTopologicalAddGroup.rightUniformSpace A.Carrier
  let := isUniformAddGroup_of_addCommGroup (G := A.Carrier)
  refine { is_henselian := fun f hf a₀ hroot hder => ?_ }
  exact HenselianRing.is_henselian f hf a₀ hroot
    (hder.map (Ideal.Quotient.mk (maximalIdeal 𝒪[A.Carrier])))

/-- A bare ring isomorphism of the given p-adic fields is continuous for the canonical topologies. -/
private theorem continuous_padicRingEquiv {p : ℕ} [Fact p.Prime]
    (A B : PadicField p) (e : A.Carrier ≃+* B.Carrier) :
    @Continuous _ _ A.canonicalTopologicalData.topology B.canonicalTopologicalData.topology e := by
  let := A.canonicalNormedField
  let := B.canonicalNormedField
  let := Algebra.charZero_of_charZero (Padic p) A.Carrier
  let := Algebra.charZero_of_charZero (Padic p) B.Carrier
  have hp := (Fact.out : p.Prime)
  have hpA : (p : A.Carrier) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  have hpB : (p : B.Carrier) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  let TA := A.canonicalTopologicalData
  let TB := B.canonicalTopologicalData
  let := henselian_discreteValuation A
  let := henselian_discreteValuation B
  have ha := TA.ord_prime_pos
  have hb := TB.ord_prime_pos
  have hpa : TA.discreteValuation (p : A.Carrier) < 1 := by
    rw [← WithZero.exp_zero (M := ℤ), ← WithZero.log_lt_iff_lt_exp
      (TA.discreteValuation.ne_zero_iff.mpr hpA)]
    exact neg_pos.mp ha
  have hpb : TB.discreteValuation (p : B.Carrier) < 1 := by
    rw [← WithZero.exp_zero (M := ℤ), ← WithZero.log_lt_iff_lt_exp
      (TB.discreteValuation.ne_zero_iff.mpr hpB)]
    exact neg_pos.mp hb
  obtain ⟨l, hlb, hl⟩ := Nat.exists_infinite_primes
    (max p (max TA.ramificationIndex TB.ramificationIndex) + 1)
  have hpl : p < l := by omega
  have hla : TA.ord (p : A.Carrier) < (l : ℤ) := by rw [← TA.ramificationIndex_cast]; omega
  have hlb' : TB.ord (p : B.Carrier) < (l : ℤ) := by rw [← TB.ramificationIndex_cast]; omega
  have hball (x : A.Carrier) : ‖x‖ ≤ 1 ↔ ‖e x‖ ≤ 1 := by
    change A.canonicalNorm x ≤ 1 ↔ B.canonicalNorm (e x) ≤ 1
    rw [← discreteValuation_le_one_iff_norm A, ← discreteValuation_le_one_iff_norm B,
      integral_iff_exists_pow TA.discreteValuation hp hl hpl hpA hpa hla,
      integral_iff_exists_pow TB.discreteValuation hp hl hpl hpB hpb hlb']
    constructor
    · rintro ⟨y, hy⟩
      exact ⟨e y, by simpa only [map_pow, map_add, map_one, map_mul, map_natCast]
        using congrArg e hy⟩
    · rintro ⟨y, hy⟩
      exact ⟨e.symm y, by simpa only [map_pow, map_add, map_one, map_mul, map_natCast,
        RingEquiv.symm_apply_apply] using congrArg e.symm hy⟩
  have hna : ‖(p : A.Carrier)‖ < 1 := by
    change A.canonicalNorm (p : A.Carrier) < 1
    rw [← map_natCast (algebraMap (Padic p) A.Carrier), A.canonicalNorm_algebraMap]
    exact Padic.norm_p_lt_one
  have hnb : ‖(p : B.Carrier)‖ < 1 := by
    change B.canonicalNorm (p : B.Carrier) < 1
    rw [← map_natCast (algebraMap (Padic p) B.Carrier), B.canonicalNorm_algebraMap]
    exact Padic.norm_p_lt_one
  -- Multiples of the unit ball by `p^n` form a neighborhood basis at zero.
  change Continuous e
  apply continuous_of_tendsto_nhds_zero e
  have basisA := Metric.nhds_basis_closedBall_pow (x := (0 : A.Carrier))
    (norm_pos_iff.mpr hpA) hna
  have basisB := Metric.nhds_basis_closedBall_pow (x := (0 : B.Carrier))
    (norm_pos_iff.mpr hpB) hnb
  refine (basisA.tendsto_iff basisB).mpr ?_
  intro n _
  refine ⟨n, trivial, fun x hx => ?_⟩
  simp only [Metric.mem_closedBall, dist_zero_right] at hx ⊢
  have hx' : ‖x / (p : A.Carrier) ^ n‖ ≤ 1 := by
    rw [norm_div, norm_pow, div_le_one₀ (pow_pos (norm_pos_iff.mpr hpA) _)]
    exact hx
  have hy := (hball _).mp hx'
  rwa [map_div₀, map_pow, map_natCast, norm_div, norm_pow,
    div_le_one₀ (pow_pos (norm_pos_iff.mpr hpB) _)] at hy

/-- Continuity with the target's original finite completion topology. -/
private theorem continuous_to_completion {p : ℕ} [Fact p.Prime] (A : PadicField p)
    {K : Type*} [Field K] [NumberField K] (v : FinitePlace K) (h : residuePrime v = p)
    (e : A.Carrier ≃+* FiniteCompletion K v) :
    let := A.canonicalTopologicalData.topology
    Continuous e := by
  have ht : (padicFieldAt v h).canonicalTopologicalData.topology =
      inferInstanceAs (TopologicalSpace (FiniteCompletion K v)) := by
    subst p
    exact (completion_topology_eq v).symm
  let := A.canonicalTopologicalData.topology
  have hc := continuous_padicRingEquiv A (padicFieldAt v h) e
  rw [ht] at hc
  exact hc

/-- The range clause identifies the upper completion with the actual local extension. -/
private def placeCompletionEquiv (Q : Proposition48Problem.{uF})
    (P : PlaceDatum Q.F Q.F' Q.E Q.E' Q.L) (hP : P.IsCompatible) :
    FiniteCompletion Q.E' P.v' ≃+* Q.F'.field := by
  let embed : FiniteCompletion Q.E' P.v' →+* AlgebraicClosure Q.F.Carrier :=
    (galoisClosure Q.F Q.F').field.val.toRingHom.comp
      (P.isoTilde.toRingHom.comp (FiniteExtension.completionMap P.v' P.vTilde))
  have hrange : Set.range embed = (Q.F'.field : Set (AlgebraicClosure Q.F.Carrier)) := hP.2
  let toField := embed.codRestrict Q.F'.field (fun x => by
    change embed x ∈ (Q.F'.field : Set (AlgebraicClosure Q.F.Carrier))
    rw [← hrange]
    exact ⟨x, rfl⟩)
  apply RingEquiv.ofBijective toField
  constructor
  · intro x y hxy
    exact embed.injective (congrArg (fun z : Q.F'.field => (z : AlgebraicClosure Q.F.Carrier)) hxy)
  · intro y
    have hy : (y : AlgebraicClosure Q.F.Carrier) ∈ Set.range embed := by
      rw [hrange]
      exact y.property
    obtain ⟨x, hx⟩ := hy
    exact ⟨x, Subtype.ext hx⟩

/-- The actual corrected component has Weil character twisted by a continuous base character. -/
theorem proposition48PlaceNormTwist : Proposition48PlaceNormTwistStatement.{uF} := by
  intro Q P ν η he hp hP hold
  let base := Correspondence.baseExtension Q.F
  let hbase : base.field ≤ Q.F'.field := bot_le
  let : Algebra base.field Q.F'.field := (IntermediateField.inclusion hbase).toAlgebra
  let := (fieldData Q.F base).topology
  let := (fieldData Q.F Q.F').topology
  let baseIso : FiniteCompletion Q.E P.v ≃+* base.field :=
    P.iso.trans (IntermediateField.botEquiv Q.F.Carrier
      (AlgebraicClosure Q.F.Carrier)).symm.toRingEquiv
  let extIso := placeCompletionEquiv Q P hP
  have hcomm : (algebraMap base.field Q.F'.field).comp baseIso.toRingHom =
      extIso.toRingHom.comp (FiniteExtension.completionMap P.v P.v') := by
    apply RingHom.ext
    intro x
    apply Subtype.ext
    change ((baseIso x : base.field) : AlgebraicClosure Q.F.Carrier) =
      (P.isoTilde (FiniteExtension.completionMap P.v' P.vTilde
        (FiniteExtension.completionMap P.v P.v' x)) : AlgebraicClosure Q.F.Carrier)
    have h := DFunLike.congr_fun
      (ClassField.Global.CompletionTower.completionMap_comp P.v P.v' P.vTilde) x
    change FiniteExtension.completionMap P.v' P.vTilde
      (FiniteExtension.completionMap P.v P.v' x) = _ at h
    rw [h, hP.1]
    change (((IntermediateField.botEquiv Q.F.Carrier (AlgebraicClosure Q.F.Carrier)).symm
      (P.iso x) : base.field) : AlgebraicClosure Q.F.Carrier) = _
    rw [IntermediateField.botEquiv_symm]
    rfl
  have hnorm (x : (FiniteCompletion Q.E' P.v')ˣ) :
      FiniteExtension.localUnitNorm P.v P.v' x =
        Units.map baseIso.symm.toMonoidHom
          (base.unitsNorm Q.F' hbase (Units.map extIso.toMonoidHom x)) := by
    apply Units.ext
    exact Algebra.norm_eq_of_equiv_equiv baseIso extIso hcomm (x : FiniteCompletion Q.E' P.v')
  have hprime : residuePrime P.v = Q.p := residuePrime_eq_of_natCast_mem P.v hp
  have hprime' : residuePrime P.v' = Q.p := (residuePrime_eq P.v P.v').trans hprime
  have hb : Continuous baseIso.symm := continuous_to_completion (base.asPadicField (p := Q.p)) P.v hprime _
  have hext : Continuous extIso.symm := continuous_to_completion (Q.F'.asPadicField (p := Q.p)) P.v' hprime' _
  let η' : FieldCharacter Q.F Q.F' := (Q.correctedCharacter ν).finiteComponent P.v' |>.comp
    ⟨Units.map extIso.symm.toMonoidHom, hext.units_map _⟩
  have hnew : P.HasComponent (Q.correctedCharacter ν) η' := by
    intro x y hxy
    have hmap : (Units.mapEquiv extIso.toMulEquiv) x = y := by
      apply Units.ext
      apply Subtype.ext
      exact hxy.symm
    change (Q.correctedCharacter ν).finiteComponent P.v' x =
      (Q.correctedCharacter ν).finiteComponent P.v' ((Units.mapEquiv extIso.toMulEquiv).symm y)
    rw [← hmap, MulEquiv.symm_apply_apply]
  let mu : FieldCharacter Q.F base := (ν.finiteComponent P.v).comp
    ⟨Units.map baseIso.symm.toMonoidHom, hb.units_map _⟩
  let ψ : localWeilGroup Q.F →ₜ* ℂˣ := mu.comp ((reciprocityUnits Q.F Q.e base).comp
    (Correspondence.baseWeilEquiv Q.F : _ →ₜ* _))
  refine ⟨η', ψ, hnew, fun w => ?_⟩
  let y := reciprocityUnits Q.F Q.e Q.F' w
  obtain ⟨x, hx⟩ := (Units.mapEquiv extIso.toMulEquiv).surjective y
  have hxy : (y.val : AlgebraicClosure Q.F.Carrier) =
      P.isoTilde (FiniteExtension.completionMap P.v' P.vTilde x.val) := by
    rw [← hx]
    rfl
  have hχ := hnew x y hxy
  change (Q.ξ * HeckeCharacter.normComp (L := Q.E') ν).finiteComponent P.v' x = η' y at hχ
  rw [HeckeCharacter.finiteComponent_mul] at hχ
  change Q.ξ.finiteComponent P.v' x *
    (HeckeCharacter.normComp (L := Q.E') ν).finiteComponent P.v' x = η' y at hχ
  have hcomp := HeckeCharacter.normComp_finiteComponent ν P.v
    (⟨P.v', inferInstance⟩ : FinitePlacesAbove Q.E' P.v) x
  change (HeckeCharacter.normComp (L := Q.E') ν).finiteComponent P.v' x =
    ν.finiteComponent P.v (FiniteExtension.localUnitNorm P.v P.v' x) at hcomp
  rw [hold x y hxy, hcomp, hnorm x] at hχ
  change η' y = η y * mu (reciprocityUnits Q.F Q.e base
    (weilInclusion Q.F base Q.F' hbase w))
  rw [LocalFactor.NonabelianSystem.DeligneHenniart.reciprocityUnits_weilInclusion Q.F he]
  change η' y = η y * mu (base.unitsNorm Q.F' hbase y)
  have hmap : Units.map extIso.toMonoidHom x = y := hx
  rw [hmap] at hχ
  exact hχ.symm

end Langlands.Global.Harris
