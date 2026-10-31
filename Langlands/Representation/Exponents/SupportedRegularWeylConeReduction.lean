import Langlands.Representation.Exponents.SupportedRegularWeylConeComparisonStatement
import Langlands.Representation.Exponents.InducedCuspidalExponentPersistenceProof
import Langlands.Representation.Exponents.TemperedOppositeTwistConeProof
import Langlands.Representation.Exponents.SupportedRegularWeylParameterHelpers
import Langlands.Representation.Exponents.SupportedRegularWeylParameterNumericsProof
import Langlands.Representation.Classification.TemperedInductionPreservationStatement
import Langlands.Representation.Classification.RelativeCosocleAdmissibilityProof
import Langlands.Representation.Classification.FineTwistRegularityProof
import Langlands.Representation.Classification.CuspidalJacquetFunctors
import Langlands.Representation.Parabolic.FineAmbientQuotientTransportProof
import Langlands.Representation.Parabolic.SecondAdjointnessProof
import Langlands.Representation.Jacquet.ExactProof
import Langlands.Group.GL.CentralQuotientTopologyProof

/-!
# Reduction of the supported regular Weyl and cone comparison

The comparison follows from tempered induction, using the published
cuspidal-exponent persistence and tempered opposite-twist cone proofs.
-/

noncomputable section

namespace Langlands.SupportedRegularWeylCone

open GeneralLinear Geometric CuspidalJacquetMultiplicity RelativeJacquetMultiplicity
open RelativeRegularComparison

universe uF uV uW uJ uVa uWa uVb uWb uV1 uV2 uM1 uM2 uW1 uW2

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData) {n : ℕ}

/-- An injective intertwiner from an irreducible admissible representation
into the opposite Jacquet module exhibits a class exponent. -/
theorem classExponent_of_injective (B : BlockShape n)
    (A : Rep.{uV} ℂ (GeneralLinear n F.Carrier)) (S : Rep.{uW} ℂ (B.Levi F.Carrier))
    (hS : Representation.IsIrreducible S.ρ) (hSa : letI := T.topology; IsAdmissible S.ρ)
    (j : S.ρ.IntertwiningMap (oppositeJacquet T B A).ρ) (hj : Function.Injective j) :
    T.IsOppositeJacquetClassExponent B A S := by
  let := T.topology
  refine ⟨hS, hSa, j.range, ?_⟩
  let e : S ≃ₗ[ℂ] j.range.toSubmodule :=
    LinearEquiv.ofInjective j.toLinearMap hj
  have he : ∀ y, j (e.symm y) = (y : oppositeJacquet T B A) := fun y => by
    have h1 : ((e (e.symm y) : j.range.toSubmodule) : oppositeJacquet T B A) =
        j (e.symm y) := rfl
    rw [LinearEquiv.apply_symm_apply] at h1
    exact h1.symm
  refine ⟨{ toLinearMap := e.symm.toLinearMap, isIntertwining' := ?_ }, e.symm.surjective⟩
  intro g
  ext u
  apply hj
  change j (e.symm _) = j (S.ρ g (e.symm u))
  rw [he, Representation.IntertwiningMap.isIntertwining _ _ j g, he]
  rfl

/-- A class exponent of a quotient is a class exponent of the source. -/
theorem classExponent_of_surjective (B : BlockShape n)
    {A : Rep.{uV} ℂ (GeneralLinear n F.Carrier)} {C : Rep.{uJ} ℂ (GeneralLinear n F.Carrier)}
    (f : A.ρ.IntertwiningMap C.ρ) (hf : Function.Surjective f)
    (S : Rep.{uW} ℂ (B.Levi F.Carrier)) (hC : T.IsOppositeJacquetClassExponent B C S) :
    T.IsOppositeJacquetClassExponent B A S := by
  let := T.topology
  obtain ⟨hS, hSa, U, q, hq⟩ := hC
  have hsurj : Function.Surjective (oppositeMap T B f) :=
    coinvariants_map_surjective
      (Jacquet.restrictMap f (B.oppositeUnipotentSubgroup F.Carrier)) hf
  let φ := oppositeMap T B f
  let U' : Subrepresentation (oppositeJacquet T B A).ρ :=
    { toSubmodule := U.toSubmodule.comap φ.toLinearMap
      apply_mem_toSubmodule := fun g v hv => by
        change φ ((oppositeJacquet T B A).ρ g v) ∈ U.toSubmodule
        rw [Representation.IntertwiningMap.isIntertwining _ _ φ g v]
        exact U.apply_mem_toSubmodule g hv }
  let r : U'.toRepresentation.IntertwiningMap U.toRepresentation :=
    { toLinearMap := φ.toLinearMap.restrict (fun v hv => hv)
      isIntertwining' := fun g => by
        ext v
        exact Representation.IntertwiningMap.isIntertwining _ _ φ g v }
  refine ⟨hS, hSa, U', q.comp r, ?_⟩
  intro y
  obtain ⟨u, rfl⟩ := hq y
  obtain ⟨v, hv⟩ := hsurj u
  refine ⟨⟨v, ?_⟩, ?_⟩
  · change φ v ∈ U.toSubmodule
    rw [hv]
    exact u.2
  · change q ⟨φ v, _⟩ = q u
    congr 1
    exact Subtype.ext hv

/-- A surjection from a fine cuspidal induction onto an irreducible admissible
representation exhibits the inducing data as a class exponent. -/
theorem classExponent_of_inducedQuotient (hn : 0 < n) (C : BlockShape n)
    (τ : Rep.{uV} ℂ (C.Levi F.Carrier)) (hτi : Representation.IsIrreducible τ.ρ)
    (hτa : letI := T.topology; IsAdmissible τ.ρ)
    (J : Rep.{uJ} ℂ (GeneralLinear n F.Carrier)) (hJi : Representation.IsIrreducible J.ρ)
    (hJa : letI := T.topology; IsAdmissible J.ρ)
    (qf : (induced T C τ).ρ.IntertwiningMap J.ρ) (hqf : Function.Surjective qf) :
    T.IsOppositeJacquetClassExponent C J τ := by
  let := T.topology
  obtain ⟨E, -, -⟩ := (Parabolic.normalizedSecondAdjointness.{uF, uV, uJ}).1 p F T n hn C
  let j := E τ J hτa hJa qf
  have hJnt : Nontrivial J := by
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    apply hJi.bot_ne_top
    apply SetLike.ext
    intro v
    rw [Subsingleton.elim v 0]
    exact ⟨fun _ => Submodule.mem_top,
      fun _ => (⊥ : Subrepresentation J.ρ).toSubmodule.zero_mem⟩
  have hqf0 : qf ≠ 0 := by
    intro h0
    obtain ⟨y, hy⟩ := exists_ne (0 : J)
    obtain ⟨x, rfl⟩ := hqf y
    rw [h0] at hy
    exact hy rfl
  have hj0 : j ≠ 0 := by
    intro h0
    exact hqf0 ((E τ J hτa hJa).map_eq_zero_iff.mp h0)
  have hj : Function.Injective j := by
    have := hτi
    exact (Representation.IsIrreducible.injective_or_eq_zero j).resolve_right hj0
  exact classExponent_of_injective T C J τ hτi hτa j hj

/-- One-sided comparison. The fine twist of the second side is a cuspidal
class exponent of the common quotient, hence of the first twisted induction;
persistence moves the responsible transport to the untwisted tempered
induction of the first side, where the tempered cone bound applies. -/
theorem oneSided
    (hOS : GLInducedCuspidalExponentPersistenceStatement.{uF, uVa, uWa, uVb})
    (hTI : GLTemperedInductionPreservationStatement.{uF, uWa})
    (hn : 0 < n) (B : BlockShape n) (S : BlockRefinement B)
    (ω : Rep.{uVa} ℂ ((B.flatten S).Levi F.Carrier))
    (hωi : Representation.IsIrreducible ω.ρ)
    (hωc : letI := T.topology; CuspidalSupport.IsLeviCuspidal (B.flatten S) ω.ρ)
    (hωu : IsUnitarizable ω.ρ) (v : Fin (B.flatten S).length → ℝ)
    (π : Rep.{uWa} ℂ (B.Levi F.Carrier)) (hπi : Representation.IsIrreducible π.ρ)
    (hπt : IsLeviTempered T B π)
    (hq : ∃ q : (innerInduced T B S (fineTwist T B S ω v 0)).ρ.IntertwiningMap π.ρ,
      Function.Surjective q)
    (t : Fin B.length → ℝ)
    (B' : BlockShape n) (S' : BlockRefinement B')
    (ω' : Rep.{uVb} ℂ ((B'.flatten S').Levi F.Carrier))
    (hω'i : Representation.IsIrreducible ω'.ρ)
    (hω'c : letI := T.topology; CuspidalSupport.IsLeviCuspidal (B'.flatten S') ω'.ρ)
    (v' : Fin (B'.flatten S').length → ℝ)
    (π' : Rep.{uWb} ℂ (B'.Levi F.Carrier)) (hπ't : IsLeviTempered T B' π')
    (hq' : ∃ q : (innerInduced T B' S' (fineTwist T B' S' ω' v' 0)).ρ.IntertwiningMap π'.ρ,
      Function.Surjective q)
    (t' : Fin B'.length → ℝ)
    (J : Rep.{uJ} ℂ (GeneralLinear n F.Carrier)) (hJi : Representation.IsIrreducible J.ρ)
    (hJ : ∃ q : (CuspidalJacquetMultiplicity.induced T B
        (Rep.of (T.leviRealPowerTwist B t π.ρ))).ρ.IntertwiningMap J.ρ,
      Function.Surjective q)
    (hJ' : ∃ q : (CuspidalJacquetMultiplicity.induced T B'
        (Rep.of (T.leviRealPowerTwist B' t' π'.ρ))).ρ.IntertwiningMap J.ρ,
      Function.Surjective q) :
    ∃ (s : Equiv.Perm (Fin n))
      (hs : CuspidalSupport.ConjugatesLevi (F := F.Carrier) (B.flatten S) (B'.flatten S') s),
      Nonempty ((CuspidalSupport.transport (F := F.Carrier) (B.flatten S) (B'.flatten S') s hs
          (T.leviRealPowerTwist (B.flatten S)
            (RealTwistFamilies.nestedParameter B S v t) ω.ρ)).Equiv
        (T.leviRealPowerTwist (B'.flatten S')
          (RealTwistFamilies.nestedParameter B' S' v' t') ω'.ρ)) ∧
      Exponents.IsClosedPositiveRootCone
        (fun a => v (blockIndex (B.flatten S) (s.symm a))) := by
  let := T.topology
  obtain ⟨q', hq'⟩ := hq'
  obtain ⟨qJ', hqJ'⟩ := hJ'
  obtain ⟨qJ, hqJ⟩ := hJ
  obtain ⟨qf, hqf⟩ := fineAmbientQuotientTransport.{uF, uVb, uWb, uJ} p F T n B' S' ω'
    hω'c.1.1 v' t' π' q' hq' J qJ' hqJ'
  let τ : Rep.{uVb} ℂ ((B'.flatten S').Levi F.Carrier) :=
    Rep.of (T.leviRealPowerTwist (B'.flatten S')
      (RealTwistFamilies.nestedParameter B' S' v' t') ω'.ρ)
  have hτi : Representation.IsIrreducible τ.ρ :=
    (T.isIrreducible_leviRealPowerTwist_iff (B'.flatten S') _ ω'.ρ).2 hω'i
  have hτc : CuspidalSupport.IsLeviCuspidal (B'.flatten S') τ.ρ :=
    (T.isLeviCuspidal_leviRealPowerTwist_iff (B'.flatten S') _ ω'.ρ).2 hω'c
  have hJa : IsAdmissible J.ρ :=
    ((relativeCosocleAdmissibility.{uF, uWb, uJ} p F T n B' π').2.2
      hπ't.isAdmissible t').2.2 J qJ' hqJ'
  have hexpJ : T.IsOppositeJacquetClassExponent (B'.flatten S') J τ :=
    classExponent_of_inducedQuotient T hn (B'.flatten S') τ hτi hτc.1 J hJi hJa qf hqf
  have hexpA : T.IsOppositeJacquetClassExponent (B'.flatten S')
      (RealTwistFamilies.induced T B π t) τ :=
    classExponent_of_surjective T (B'.flatten S') qJ hqJ τ hexpJ
  obtain ⟨s, hs, ⟨e⟩, hocc⟩ :=
    hOS p F T n hn B S ω hωi hωc v π hπi hq t (B'.flatten S') τ hτc hexpA
  refine ⟨s, hs, ⟨e⟩, ?_⟩
  rw [RealTwistFamilies.Occurs, RealTwistFamilies.induced_zero,
    RealTwistFamilies.transported_apply, RealTwistFamilies.nestedParameter_zero] at hocc
  have hzero : (fun k => -((v k : ℝ) : ℂ) + Complex.I * ((0 : ℝ) : ℂ)) =
      fun k => (((-v) k : ℝ) : ℂ) := by
    funext k
    simp
  rw [← T.leviComplexPowerTwist_ofReal, ← hzero] at hocc
  have hA : T.IsTempered (CuspidalJacquetMultiplicity.induced T B π).ρ := by
    let := T.leviTopologicalGroup B
    let Z := B.Levi F.Carrier ⧸ Subgroup.center (B.Levi F.Carrier)
    let := borel Z
    have : BorelSpace Z := ⟨rfl⟩
    obtain ⟨μ, hμ⟩ := T.exists_isHaarMeasure_leviCentralQuotient B
    exact hTI p F T n hn B μ π π.ρ hπi (hπt μ)
  exact glTemperedOppositeTwistCone.{uF, uVa, max uF uWa} p F T n hn (B.flatten S)
    (B'.flatten S') s hs ω hωi hωc.1 hωu v 0 _ hA hocc

/-- Transporting irreducible unitarizable cuspidal data along an equality of
block shapes keeps all three properties. -/
theorem cast_cuspidalData {C C' : BlockShape n} (h : C = C')
    (ω : Rep.{uV} ℂ (C.Levi F.Carrier)) (ω' : Rep.{uV} ℂ (C'.Levi F.Carrier))
    (hω' : ω' = h ▸ ω) (hi : Representation.IsIrreducible ω.ρ)
    (hc : letI := T.topology; CuspidalSupport.IsLeviCuspidal C ω.ρ)
    (hu : IsUnitarizable ω.ρ) :
    Representation.IsIrreducible ω'.ρ ∧
      (letI := T.topology; CuspidalSupport.IsLeviCuspidal C' ω'.ρ) ∧
      IsUnitarizable ω'.ρ := by
  subst hω'
  subst h
  exact ⟨hi, hc, hu⟩

/-- The supported regular comparison follows from tempered induction
preservation on both sides, using the published persistence and numerical
comparison proofs. -/
theorem reduction
    (hTI1 : GLTemperedInductionPreservationStatement.{uF, uW1})
    (hTI2 : GLTemperedInductionPreservationStatement.{uF, uW2}) :
    GLSupportedRegularWeylConeComparisonStatement.{uF, uV1, uV2, uM1, uM2, uW1, uW2, uJ} := by
  have hOS12 := glInducedCuspidalExponentPersistence.{uF, uV1, uW1, uV2}
  have hOS21 := glInducedCuspidalExponentPersistence.{uF, uV2, uW2, uV1}
  have hNum := Exponents.supportedRegularWeylParameterNumerics
  intro p _ F T n hn B1 Q1 D1 R1 S1 h1 ω1 hω1i hω1c hω1u v1 hv1 ωB1 vB1 σ1 _ _ _
    π1 hπ1i hπ1t _ hq1 t1 ht1 B2 Q2 D2 R2 S2 h2 ω2 hω2i hω2c hω2u v2 hv2 ωB2 vB2
    σ2 _ _ _ π2 hπ2i hπ2t _ hq2 t2 ht2 J hJi hJ1 hJ2 C1 C2 V1 V2 A1 A2
  obtain ⟨hB1i, hB1c, hB1u⟩ := cast_cuspidalData T h1 ω1 ωB1 rfl hω1i hω1c hω1u
  obtain ⟨hB2i, hB2c, hB2u⟩ := cast_cuspidalData T h2 ω2 ωB2 rfl hω2i hω2c hω2u
  obtain ⟨s, hs, he, hcone1⟩ := oneSided T hOS12 hTI1 hn B1 S1 ωB1 hB1i hB1c hB1u vB1
    π1 hπ1i hπ1t hq1 t1 B2 S2 ωB2 hB2i hB2c vB2 π2 hπ2t hq2 t2 J hJi hJ1 hJ2
  obtain ⟨r, hr, he', hcone2⟩ := oneSided T hOS21 hTI2 hn B2 S2 ωB2 hB2i hB2c hB2u vB2
    π2 hπ2i hπ2t hq2 t2 B1 S1 ωB1 hB1i hB1c vB1 π1 hπ1t hq1 t1 J hJi hJ2 hJ1
  have hrel1 := SupportedRegularWeylComparison.fixedRelation_of_twistedEquiv T B1 B2 S1 S2
    ωB1.ρ ωB2.ρ hB1i hB1c hB1u hB2i hB2c hB2u vB1 t1 vB2 t2 s hs he
  have hrel2 := SupportedRegularWeylComparison.fixedRelation_of_twistedEquiv T B2 B1 S2 S1
    ωB2.ρ ωB1.ρ hB2i hB2c hB2u hB1i hB1c hB1u vB2 t2 vB1 t1 r hr he'
  obtain ⟨hV1, hO1, hA1⟩ := hNum.2.1 n B1 Q1 R1 S1 h1 v1 t1 hv1
  obtain ⟨hV2, hO2, hA2⟩ := hNum.2.1 n B2 Q2 R2 S2 h2 v2 t2 hv2
  have hfin := (hNum.2.2 n V1 V2 A1 A2 s r hO1 hO2 (hA1 ht1) (hA2 ht2) hcone1 hcone2 hrel1 hrel2 hV1).2
  exact ⟨s, hs, he, hrel1, hcone1, hfin⟩

end Langlands.SupportedRegularWeylCone
