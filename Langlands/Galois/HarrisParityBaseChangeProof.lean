import Langlands.Automorphic.ConjugateSelfDualCriterion
import Langlands.Galois.HarrisParityBaseChangeStatement
import Langlands.Automorphic.ContragredientSphericalSpectrum
import Langlands.Automorphic.ContragredientUniqueness
import Langlands.Automorphic.CuspidalArithmeticSpectralTransportProof
import Langlands.Automorphic.CuspidalDualPresentationExistenceProof
import Langlands.Automorphic.CuspidalUnitaryContragredientExistenceProof
import Langlands.Automorphic.OperatorCMUnitaryForm
import Langlands.Automorphic.Unramified.CyclicPrimeSingletonBaseChange
import Langlands.Global.Arithmetic.HarrisDatumCharacterRealizationProof

/-! # Automorphic base change for the Harris parity reduction -/

noncomputable section

universe uE uV uW

set_option autoImplicit false

namespace Langlands.GaloisRepresentation

open Langlands.Automorphic Langlands.Automorphic.Unramified Langlands.Global
open Langlands.Global.AdelicFunctoriality Langlands.Global.AdelicFunctoriality.FiniteExtension
open Langlands.Global.CMConjugation Langlands.LocalFactor.Archimedean Langlands.Unramified
open Langlands.ClassFieldTheory.Global.RelativeWeilGroup (HasUnitaryCentralCharacter)
open NumberField
open scoped NumberField NumberField.LiesOver

section CMPairing

variable {F : Type uE} [Field F] [NumberField F] [IsCMField F] {n : ℕ}

local instance (n : ℕ) : AddCommGroup (RationalInvariantFunctions F n) :=
  Submodule.addCommGroup _
local instance (n : ℕ) : AddCommGroup (ContinuousRationalFunctions F n) :=
  Submodule.addCommGroup _
local instance (n : ℕ) : AddCommGroup (FiniteSmoothRationalFunctions F n) :=
  Submodule.addCommGroup _
local instance (n : ℕ) : AddCommGroup (AutomorphicForms F n) :=
  Submodule.addCommGroup _
local instance (n : ℕ) : AddCommGroup (StableAutomorphicFunctions F n) :=
  Submodule.addCommGroup _
local instance (S : OperatorRealization F n) : AddCommGroup S.Space := Submodule.addCommGroup _

private theorem fieldConj_trans : (fieldConj F).trans (fieldConj F) = RingEquiv.refl F :=
  RingEquiv.ext (IsCMField.complexConj_apply_apply F)

private theorem fieldConj_symm : (fieldConj F).symm = fieldConj F := by
  apply RingEquiv.ext
  intro x
  apply (fieldConj F).injective
  exact ((fieldConj F).apply_symm_apply x).trans (IsCMField.complexConj_apply_apply F x).symm

private theorem finiteConj_twice (d : FiniteAdelicGL F n) :
    finiteConj F n (finiteConj F n d) = d := by
  apply Units.ext
  apply Matrix.ext
  intro i j
  simp only [finiteConj_apply]
  change ((finiteAdeleEquiv (fieldConj F)).trans (finiteAdeleEquiv (fieldConj F))) (d i j) = d i j
  rw [← finiteAdeleEquiv_trans, fieldConj_trans, finiteAdeleEquiv_refl, RingEquiv.refl_apply]

private theorem compactConj_twice (k : standardInfiniteCompact F n) :
    compactConj F n (compactConj F n k) = k := by
  apply Subtype.ext
  apply Units.ext
  apply Matrix.ext
  intro i j
  simp only [compactConj_val, infiniteConj_apply]
  exact infiniteComplexConj_involutive (K := F) _

omit [NumberField F] [IsCMField F] in
private theorem lieConj_twice (X : ArchimedeanGL.RealLieAlgebra F n) :
    lieConj F n (lieConj F n X) = X := by
  apply (ArchimedeanGL.realLieAlgebraToMatrix F n).injective
  apply Matrix.ext
  intro i j
  simp only [lieConj_apply, mixedConj_apply, star_star, Prod.eta]

private theorem complexConjEquiv_lieAction (S : OperatorRealization F n)
    (X : ArchimedeanGL.RealLieAlgebra F n) (x : S.Space) :
    S.complexConj.lieAction X (S.complexConjEquiv x) =
      S.complexConjEquiv (S.lieAction (lieConj F n X) x) := by
  have h : ArchimedeanLieTransport.realLieEquiv n (fieldConj F) X = lieConj F n X := by
    apply (ArchimedeanGL.realLieAlgebraToMatrix F n).injective
    apply Matrix.ext
    intro i j
    rw [ArchimedeanLieTransport.realLieEquiv_entry, lieConj_apply]
    let y := ArchimedeanGL.realLieAlgebraToMatrix F n X i j
    simpa only [ArchimedeanGLTransport.mixedEquiv, RingEquiv.trans_apply,
      RingEquiv.apply_symm_apply, infiniteComplexConj] using
      mixedSpace_infiniteComplexConj F ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm y)
  simpa only [OperatorRealization.lieAction, ArchimedeanLieTransport.envelopingEquiv_generator,
    ArchimedeanLieTransport.complexLieEquiv_complexify, h] using
    S.complexConjEquiv_differential
      (ArchimedeanGL.envelopingGenerator F n (ArchimedeanGL.complexify F n X)) x

set_option maxHeartbeats 1000000 in
set_option maxHeartbeats 2000000 in
private theorem isContragredientOf_complexConj (S : OperatorRealization F n)
    (h : S.IsConjugateSelfDual) : S.complexConj.IsContragredientOf S := by
  let e := S.complexConjEquiv.toLinearEquiv
  obtain ⟨C, ⟨hf, hk, hLie⟩, hC, hinj, hsurj⟩ := h
  let B := C.compl₁₂ LinearMap.id e.symm.toLinearMap
  have hflip (x : S.complexConj.Space) : B.flip x = C.flip (e.symm x) := rfl
  refine ⟨B, ⟨?_, ?_, ?_⟩, fun x => hC (e.symm x), ?_, ?_⟩
  · intro d y x
    obtain ⟨f, rfl⟩ := e.surjective x
    have h : e.symm (S.complexConj.finiteRepresentation d (e f)) =
        S.finiteRepresentation (finiteConj F n d) f :=
      (congrArg e.symm (S.complexConjEquiv_finite d f)).trans (e.symm_apply_apply _)
    have hinv : C (S.finiteRepresentation d y)
        (S.finiteRepresentation (finiteConj F n d) f) = C y f := by
      simpa only [finiteConj_twice] using hf (finiteConj F n d) y f
    change C (S.finiteRepresentation d y)
      (e.symm (S.complexConj.finiteRepresentation d (e f))) = C y (e.symm (e f))
    exact (congrArg (C (S.finiteRepresentation d y)) h).trans
      (hinv.trans (congrArg (C y) (e.symm_apply_apply f)).symm)
  · intro k y x
    obtain ⟨f, rfl⟩ := e.surjective x
    have h : e.symm (S.complexConj.compactRepresentation k (e f)) =
        S.compactRepresentation (compactConj F n k) f :=
      (congrArg e.symm (S.complexConjEquiv_compact k f)).trans (e.symm_apply_apply _)
    have hinv : C (S.compactRepresentation k y)
        (S.compactRepresentation (compactConj F n k) f) = C y f := by
      simpa only [compactConj_twice] using hk (compactConj F n k) y f
    change C (S.compactRepresentation k y)
      (e.symm (S.complexConj.compactRepresentation k (e f))) = C y (e.symm (e f))
    exact (congrArg (C (S.compactRepresentation k y)) h).trans
      (hinv.trans (congrArg (C y) (e.symm_apply_apply f)).symm)
  · intro X y x
    obtain ⟨f, rfl⟩ := e.surjective x
    have h : e.symm (S.complexConj.lieAction X (e f)) = S.lieAction (lieConj F n X) f :=
      (congrArg e.symm (complexConjEquiv_lieAction S X f)).trans (e.symm_apply_apply _)
    change C (S.lieAction X y) (e.symm (e f)) +
      C y (e.symm (S.complexConj.lieAction X (e f))) = 0
    exact (congrArg₂ (fun a b => C (S.lieAction X y) a + C y b)
      (e.symm_apply_apply f) h).trans (by
        simpa only [lieConj_twice] using hLie (lieConj F n X) y f)
  · intro x x' hx
    exact e.symm.injective (hinj ((hflip x).symm.trans (hx.trans (hflip x'))))
  · intro l hl
    obtain ⟨x, hx⟩ := hsurj l hl
    exact ⟨e x, (hflip _).trans ((congrArg C.flip (e.symm_apply_apply x)).trans hx)⟩

end CMPairing

section ComplexPlaces

variable {E N : Type uE} [Field E] [NumberField E] [IsCMField E]
  [Field N] [NumberField N] [IsCMField N] [Algebra E N]
  [CompactSpace (AdeleQuotient E)] [CompactSpace (AdeleQuotient N)] {r : ℕ}

omit [IsCMField E] [IsCMField N] [CompactSpace (AdeleQuotient E)]
  [CompactSpace (AdeleQuotient N)] in
private theorem regularAlgebraic_transport {n : ℕ}
    (v : {v : NumberField.InfinitePlace E // v.IsComplex}) (w : InfinitePlacesAbove N v.1)
    {ds : List ComplexCharacterData} (h : ComplexPlaceParameter.IsClozelRegularAlgebraic n ds) :
    ComplexPlaceParameter.IsClozelRegularAlgebraic n (complexPlaceParameterTransport v w ds) := by
  classical
  unfold complexPlaceParameterTransport
  split
  · exact h
  · have hz (d : ComplexCharacterData) : d.conj.zExponent = d.zBarExponent := by
      simp [ComplexCharacterData.zExponent, ComplexCharacterData.zBarExponent,
        ComplexCharacterData.conj, sub_eq_add_neg, neg_div]
    have hzBar (d : ComplexCharacterData) : d.conj.zBarExponent = d.zExponent := by
      simp [ComplexCharacterData.zExponent, ComplexCharacterData.zBarExponent,
        ComplexCharacterData.conj, sub_eq_add_neg, neg_div]
    rcases h with ⟨hlen, hint, hnodup, hnodupBar⟩
    refine ⟨(List.length_map _).trans hlen, ?_, ?_, ?_⟩
    · intro d hd
      obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hd
      obtain ⟨p, q, hp, hq⟩ := hint c hc
      exact ⟨q, p, (hz c).trans hq, (hzBar c).trans hp⟩
    · rwa [List.map_map, show ComplexCharacterData.zExponent ∘ ComplexCharacterData.conj =
        ComplexCharacterData.zBarExponent from funext hz]
    · rwa [List.map_map, show ComplexCharacterData.zBarExponent ∘ ComplexCharacterData.conj =
        ComplexCharacterData.zExponent from funext hzBar]

private theorem regularAlgebraic_of_complexPlaceTransport
    (hBridge : CuspidalComplexParameterBridgeTCStatement.{uE})
    {S : CuspidalOperatorRealization E r} {T : CuspidalOperatorRealization N r}
    (hS : S.isoClass.IsRegularAlgebraic)
    (hTransport : ∀ (v : {v : NumberField.InfinitePlace E // v.IsComplex}) (w : InfinitePlacesAbove N v.1)
      (ds : List ComplexCharacterData),
      S.isoClass.HasComplexPlaceParameter v ds →
        T.isoClass.HasComplexPlaceParameter (complexPlaceAbove v w)
          (complexPlaceParameterTransport v w ds)) :
    T.isoClass.IsRegularAlgebraic := by
  classical
  choose ds hds using (hBridge.1 E r S).2
  obtain ⟨χ, hχ, hSχ⟩ := S.isoClass_isRegularAlgebraic_iff.mp hS
  obtain ⟨⟨θ, hθ, _⟩, hAct⟩ := hBridge.2.1 E r S ds hds
  obtain ⟨x, hx⟩ := exists_ne (0 : S.Space)
  have hθχ : θ = χ := (hAct θ hθ).unique hx hSχ
  have hReg := (hBridge.2.2 E (r + 1) ds θ hθ).mp (hθχ.symm ▸ hχ)
  let lower (w : {w : NumberField.InfinitePlace N // w.IsComplex}) :
      {v : NumberField.InfinitePlace E // v.IsComplex} :=
    ⟨w.1.comap (algebraMap E N), IsTotallyComplex.isComplex _⟩
  let above (w : {w : NumberField.InfinitePlace N // w.IsComplex}) :
      InfinitePlacesAbove N (lower w).1 :=
    ⟨w.1, ⟨rfl⟩⟩
  let dt (w : {w : NumberField.InfinitePlace N // w.IsComplex}) :=
    complexPlaceParameterTransport (lower w) (above w) (ds (lower w))
  have hdt (w : {w : NumberField.InfinitePlace N // w.IsComplex}) :
      T.realization.HasComplexPlaceParameter w (dt w) := by
    have hw : complexPlaceAbove (lower w) (above w) = w := Subtype.ext rfl
    have h := hTransport (lower w) (above w) (ds (lower w))
      ((S.isoClass_hasComplexPlaceParameter _ _).mpr (hds (lower w)))
    change T.isoClass.HasComplexPlaceParameter (complexPlaceAbove (lower w) (above w)) (dt w) at h
    rw [hw] at h
    exact (T.isoClass_hasComplexPlaceParameter _ _).mp h
  obtain ⟨⟨ψ, hψ, _⟩, hActT⟩ := hBridge.2.1 N r T dt hdt
  exact T.isoClass_isRegularAlgebraic_iff.mpr
    ⟨ψ, (hBridge.2.2 N (r + 1) dt ψ hψ).mpr
      (fun w => regularAlgebraic_transport (lower w) (above w) (hReg (lower w))), hActT ψ hψ⟩

end ComplexPlaces

section DualBaseChange

variable {E N : Type uE} [Field E] [NumberField E] [Field N] [NumberField N]
  [Algebra E N] [CompactSpace (AdeleQuotient E)] [CompactSpace (AdeleQuotient N)] {r : ℕ}

private theorem dual_isWeakBaseChangeOf
    {S Sd : CuspidalOperatorRealization E r} {T Td : CuspidalOperatorRealization N r}
    (hbc : T.isoClass.IsWeakBaseChangeOf.{uE, uE, uV, uW} S.isoClass)
    (hS : Sd.realization.IsContragredientOf S.realization)
    (hT : Td.realization.IsContragredientOf T.realization) :
    Td.isoClass.IsWeakBaseChangeOf.{uE, uE, uV, uW} Sd.isoClass := by
  obtain ⟨P, Q, hPQ⟩ :=
    (CuspidalOperatorRealization.IsoClass.isWeakBaseChangeOf_isoClass_iff T S).mp hbc
  obtain ⟨Pd⟩ := cuspidalDualPresentationExistence.{uE, uV, uV} E r S Sd hS P
  obtain ⟨Qd⟩ := cuspidalDualPresentationExistence.{uE, uW, uW} N r T Td hT Q
  refine (CuspidalOperatorRealization.IsoClass.isWeakBaseChangeOf_isoClass_iff Td Sd).mpr
    ⟨Pd, Qd, ?_⟩
  filter_upwards [hPQ, Pd.exceptional.eventually_cofinite_notMem,
    SpectralSystem.eventually_avoidsAbove (F := E) Qd.exceptional] with v hv hvd hwd
  obtain ⟨hp, hq, he, hs⟩ := hv
  refine ⟨hvd, hwd, he, fun w => ?_⟩
  rw [T.eigenvalues_eq_map_inv_of_isContragredientOf Td Q Qd hT w.1 (hq w) (hwd w),
    S.eigenvalues_eq_map_inv_of_isContragredientOf Sd P Pd hS v hp hvd, hs w]
  simp only [Eigenvalues.power, Sym.map_map, Function.comp_def, inv_pow]

end DualBaseChange

section CMBaseChange

variable {E N : Type uE} [Field E] [NumberField E] [IsCMField E]
  [Field N] [NumberField N] [IsCMField N] [Algebra E N]

private theorem integersConj_algebraMap (x : 𝓞 E) :
    RingOfIntegers.mapRingEquiv (fieldConj N).symm (algebraMap (𝓞 E) (𝓞 N) x) =
      algebraMap (𝓞 E) (𝓞 N) (RingOfIntegers.mapRingEquiv (fieldConj E).symm x) := by
  apply RingOfIntegers.ext
  change (fieldConj N).symm (algebraMap E N (x : E)) =
    algebraMap E N ((fieldConj E).symm (x : E))
  rw [fieldConj_symm, fieldConj_symm]
  exact HarrisDatum.complexConj_algebraMap (E' := N) (x : E)

private def conjugatePlaceAbove (v : Global.FinitePlace E) (w : FinitePlacesAbove N v) :
    FinitePlacesAbove N (finitePlaceEquiv (fieldConj E).symm v) := by
  letI := w.2
  refine ⟨finitePlaceEquiv (fieldConj N).symm w.1, ?_⟩
  simpa only [fieldConj_symm, Harris.conjPlace] using HarrisDatum.conjPlace_liesOver v w.1

private theorem map_placeIdeal {F : Type uE} [Field F] (g : F ≃+* F) (v : Global.FinitePlace F) :
    (finitePlaceEquiv g v).asIdeal.map (RingOfIntegers.mapRingEquiv g).toRingHom = v.asIdeal :=
  Ideal.map_comap_of_surjective _ (RingOfIntegers.mapRingEquiv g).surjective _

private theorem conjugatePlaceAbove_inertiaDeg (v : Global.FinitePlace E)
    (w : FinitePlacesAbove N v) :
    (conjugatePlaceAbove v w).1.asIdeal.inertiaDeg (𝓞 E) = w.1.asIdeal.inertiaDeg (𝓞 E) := by
  let := w.2
  let := (conjugatePlaceAbove v w).2
  rw [Ideal.inertiaDeg_eq_of_isMaximal (finitePlaceEquiv (fieldConj E).symm v).asIdeal,
    Ideal.inertiaDeg_eq_of_isMaximal v.asIdeal]
  let ev := Ideal.quotientEquiv (finitePlaceEquiv (fieldConj E).symm v).asIdeal v.asIdeal
    (RingOfIntegers.mapRingEquiv (fieldConj E).symm) (map_placeIdeal (fieldConj E).symm v).symm
  let fw := Ideal.quotientEquiv (conjugatePlaceAbove v w).1.asIdeal w.1.asIdeal
    (RingOfIntegers.mapRingEquiv (fieldConj N).symm) (map_placeIdeal (fieldConj N).symm w.1).symm
  apply Algebra.finrank_eq_of_equiv_equiv ev fw
  apply RingHom.ext
  intro x
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
  change Ideal.Quotient.mk w.1.asIdeal
      (algebraMap (𝓞 E) (𝓞 N) (RingOfIntegers.mapRingEquiv (fieldConj E).symm y)) =
    Ideal.Quotient.mk w.1.asIdeal
      (RingOfIntegers.mapRingEquiv (fieldConj N).symm (algebraMap (𝓞 E) (𝓞 N) y))
  rw [integersConj_algebraMap]

private theorem conjugatePlaceAbove_ramificationIdx (v : Global.FinitePlace E)
    (w : FinitePlacesAbove N v) :
    (conjugatePlaceAbove v w).1.asIdeal.ramificationIdx (𝓞 E) =
      w.1.asIdeal.ramificationIdx (𝓞 E) := by
  let := w.2
  let := (conjugatePlaceAbove v w).2
  let g := RingOfIntegers.mapRingEquiv (fieldConj N).symm
  let m : Ideal (𝓞 N) ≃* Ideal (𝓞 N) :=
    { (Ideal.relIsoOfBijective g.toRingHom g.bijective).symm.toEquiv with
      map_mul' := fun I J => Ideal.map_mul _ _ _ }
  have hmap (I : Ideal (𝓞 N)) : m I = I.map g.toRingHom := rfl
  have hc : g.toRingHom.comp (algebraMap (𝓞 E) (𝓞 N)) =
      (algebraMap (𝓞 E) (𝓞 N)).comp (RingOfIntegers.mapRingEquiv (fieldConj E).symm).toRingHom :=
    RingHom.ext integersConj_algebraMap
  rw [Ideal.IsDedekindDomain.ramificationIdx_eq_multiplicity
        (finitePlaceEquiv (fieldConj E).symm v).asIdeal _
        (Ideal.map_ne_bot_of_ne_bot (finitePlaceEquiv (fieldConj E).symm v).ne_bot),
      Ideal.IsDedekindDomain.ramificationIdx_eq_multiplicity v.asIdeal
        _ (Ideal.map_ne_bot_of_ne_bot v.ne_bot), ← multiplicity_map_eq m, hmap, hmap]
  change multiplicity ((finitePlaceEquiv (fieldConj N).symm w.1).asIdeal.map g.toRingHom)
      (((finitePlaceEquiv (fieldConj E).symm v).asIdeal.map
        (algebraMap (𝓞 E) (𝓞 N))).map g.toRingHom) =
    multiplicity w.1.asIdeal (v.asIdeal.map (algebraMap (𝓞 E) (𝓞 N)))
  rw [map_placeIdeal (fieldConj N).symm, Ideal.map_map, hc, ← Ideal.map_map, map_placeIdeal]

variable [CompactSpace (AdeleQuotient E)] [CompactSpace (AdeleQuotient N)] {r : ℕ}

private theorem complexConj_isWeakBaseChangeOf
    {S : CuspidalOperatorRealization E r} {T : CuspidalOperatorRealization N r}
    (hbc : T.isoClass.IsWeakBaseChangeOf.{uE, uE, uV, uW} S.isoClass) :
    T.complexConj.isoClass.IsWeakBaseChangeOf.{uE, uE, uV, uW} S.complexConj.isoClass := by
  obtain ⟨P, Q, hPQ⟩ :=
    (CuspidalOperatorRealization.IsoClass.isWeakBaseChangeOf_isoClass_iff T S).mp hbc
  rw [← CuspidalOperatorRealization.arithmeticComap_fieldConj S, ← CuspidalOperatorRealization.arithmeticComap_fieldConj T]
  refine (CuspidalOperatorRealization.IsoClass.isWeakBaseChangeOf_isoClass_iff _ _).mpr
    ⟨P.arithmeticComap (fieldConj E), Q.arithmeticComap (fieldConj N), ?_⟩
  have hplaces := (finitePlaceEquiv (fieldConj E).symm).injective.tendsto_cofinite.eventually hPQ
  filter_upwards [hplaces] with v hv
  obtain ⟨hp, hq, he, hs⟩ := hv
  have hp' : v ∉ (P.arithmeticComap (fieldConj E)).exceptional := by
    simpa only [CuspidalSpectralPresentation.arithmeticComap,
      CuspidalSpectralPresentation.spectralSystem_exceptional, FiniteAdelicGL.transportExceptional,
      Finset.mem_map_equiv, Equiv.symm_symm] using hp
  have hq' (w : FinitePlacesAbove N v) : w.1 ∉ (Q.arithmeticComap (fieldConj N)).exceptional := by
    simpa only [CuspidalSpectralPresentation.arithmeticComap,
      CuspidalSpectralPresentation.spectralSystem_exceptional, FiniteAdelicGL.transportExceptional,
      Finset.mem_map_equiv, Equiv.symm_symm, conjugatePlaceAbove] using hq (conjugatePlaceAbove v w)
  refine ⟨hp', hq', fun w => (conjugatePlaceAbove_ramificationIdx v w).symm.trans
    (he (conjugatePlaceAbove v w)), fun w => ?_⟩
  change Q.spectralSystem.eigenvalues (conjugatePlaceAbove v w).1 (hq (conjugatePlaceAbove v w)) =
    (P.spectralSystem.eigenvalues (finitePlaceEquiv (fieldConj E).symm v) hp).power
      (w.1.asIdeal.inertiaDeg (𝓞 E))
  rw [← conjugatePlaceAbove_inertiaDeg v w]
  exact hs (conjugatePlaceAbove v w)

end CMBaseChange

/-- The four parity base change premises give the actual cuspidal lift with
regular algebraicity, conjugate self-duality and the split square-integrable components. -/
theorem harrisParityBaseChange : HarrisParityBaseChangeStatement.{uE, uW} := by
  intro hIsobaric hSplitComparison hInfinity hBridge E N _ _ _ _ _ _ _ _ _ _
    hDegree r S v hCentral hReg hSelf hSquare hSplit
  classical
  have hPrime : (Module.finrank E N).Prime := hDegree.symm ▸ Nat.prime_two
  let : Fact (Module.finrank E N).Prime := ⟨hPrime⟩
  let : IsCyclic (N ≃ₐ[E] N) := isCyclic_of_prime_card (IsGalois.card_aut_eq_finrank E N)
  let B := IsobaricData.ofCuspidal (PositiveRankCuspidalClass.ofFixedRank S.isoClass)
  have hB : B.IsUnitary :=
    IsobaricData.isUnitary_ofCuspidal.mpr (S.isUnitarizable_of_hasUnitaryCentralCharacter hCentral)
  obtain ⟨D, hD, hDB, hUnique⟩ := hIsobaric E N hPrime B hB
  obtain ⟨P, hP⟩ := (CuspidalOperatorRealization.IsoClass.hasSquareIntegrableComponent_iff S v).mp
    hSquare
  obtain ⟨T, Q, hSingleton, hAtSplit⟩ :=
    hSplitComparison E N hDegree r S P D v hP hSplit hB hD hDB
  have hBC : T.isoClass.IsWeakBaseChangeOf.{uE, uE, uW, uW} S.isoClass :=
    (IsobaricData.isWeakBaseChangeOf_ofCuspidal_iff T.isoClass S.isoClass).mp (hSingleton ▸ hDB)
  refine ⟨T, hBC, ?_, ?_, fun w =>
    (CuspidalOperatorRealization.IsoClass.hasSquareIntegrableComponent_iff T w.1).mpr
      ⟨Q, (hAtSplit w).1⟩⟩
  · exact regularAlgebraic_of_complexPlaceTransport hBridge hReg fun x w ds =>
      ((hInfinity E N hPrime).1 r S T hCentral hBC x w ds).mp
  · have hUnitSingleton :
        (IsobaricData.ofCuspidal (PositiveRankCuspidalClass.ofFixedRank T.isoClass)).IsUnitary :=
      hSingleton ▸ hD
    have hUnitT : T.realization.IsUnitarizable :=
      IsobaricData.isUnitary_ofCuspidal.mp hUnitSingleton
    obtain ⟨Sd, hSd, _⟩ := cuspidalUnitaryContragredientExistence E r S hCentral
    obtain ⟨Td, hTd, hCentralTd⟩ := cuspidalUnitaryContragredientExistence N r T
      (T.hasUnitaryCentralCharacter_of_isUnitarizable hUnitT)
    have hSdClass : Sd.isoClass = S.complexConj.isoClass :=
      (Sd.isoClass_eq_iff S.complexConj).mpr (hSd.nonempty_equivalence
        (isContragredientOf_complexConj S.realization (S.isoClass_isConjugateSelfDual_iff.mp hSelf)))
    have hSdConj : Sd.complexConj.isoClass = S.isoClass := by
      simpa only [CuspidalOperatorRealization.IsoClass.complexConj_isoClass,
        CuspidalOperatorRealization.complexConj_complexConj] using
        congrArg CuspidalOperatorRealization.IsoClass.complexConj hSdClass
    have hDualBC := complexConj_isWeakBaseChangeOf (dual_isWeakBaseChangeOf hBC hSd hTd)
    rw [hSdConj] at hDualBC
    let Dd := IsobaricData.ofCuspidal (PositiveRankCuspidalClass.ofFixedRank Td.complexConj.isoClass)
    have hUnitDd : Dd.IsUnitary := IsobaricData.isUnitary_ofCuspidal.mpr
      (Td.isUnitarizable_of_hasUnitaryCentralCharacter hCentralTd).complexConj
    have hDdBC : Dd.IsWeakBaseChangeOf.{uE, uE, uW, uW} B :=
      (IsobaricData.isWeakBaseChangeOf_ofCuspidal_iff _ _).mpr hDualBC
    have hDd : Dd = IsobaricData.ofCuspidal (PositiveRankCuspidalClass.ofFixedRank T.isoClass) :=
      (hUnique Dd hUnitDd hDdBC).trans hSingleton
    have hTdConj : Td.complexConj.isoClass = T.isoClass :=
      (PositiveRankCuspidalClass.ofFixedRank_injective r) (Multiset.singleton_inj.mp hDd)
    have hTdClass : Td.isoClass = T.complexConj.isoClass := by
      simpa only [CuspidalOperatorRealization.IsoClass.complexConj_isoClass,
        CuspidalOperatorRealization.complexConj_complexConj] using
        congrArg CuspidalOperatorRealization.IsoClass.complexConj hTdConj
    apply T.isoClass_isConjugateSelfDual_iff.mpr
    apply OperatorRealization.isConjugateSelfDual_of_complexConj_isContragredientOf
    exact (T.complexConj.isoClass_isContragredientOf_iff T).mp
      (hTdClass ▸ (Td.isoClass_isContragredientOf_iff T).mpr hTd)

end Langlands.GaloisRepresentation
