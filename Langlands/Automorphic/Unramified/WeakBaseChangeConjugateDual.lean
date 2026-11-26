import Langlands.Automorphic.ConjugateSelfDualCriterion
import Langlands.Automorphic.ConjugateContragredient
import Langlands.Automorphic.ContragredientSphericalSpectrum
import Langlands.Automorphic.CuspidalArithmeticSpectralTransportProof
import Langlands.Automorphic.CuspidalDualPresentationExistenceProof
import Langlands.Automorphic.OperatorCMTransport
import Langlands.Automorphic.Unramified.WeakTransfer

/-! # Weak base change under contragredients and CM conjugation

For a conjugate self-dual realization, the actual CM image is a contragredient.
Weak base change of actual cuspidal classes is preserved by passing to supplied
contragredients on both levels, and by actual CM conjugation on both levels of
an extension of CM fields.
-/

noncomputable section

universe uF uE uD uV uW

set_option autoImplicit false

namespace Langlands.Automorphic

open NumberField Langlands.Global Langlands.Global.AdelicFunctoriality
open Langlands.Global.CMConjugation Langlands.Unramified
open scoped NumberField

section CMPairing

variable {F : Type uF} [Field F] [NumberField F] [IsCMField F] {n : ℕ}

local instance weakConjDualRationalGroup (n : ℕ) :
    AddCommGroup (RationalInvariantFunctions F n) := Submodule.addCommGroup _
local instance weakConjDualContinuousGroup (n : ℕ) :
    AddCommGroup (ContinuousRationalFunctions F n) := Submodule.addCommGroup _
local instance weakConjDualSmoothGroup (n : ℕ) :
    AddCommGroup (FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _
local instance weakConjDualFormsGroup (n : ℕ) :
    AddCommGroup (AutomorphicForms F n) := Submodule.addCommGroup _
local instance weakConjDualStableGroup (n : ℕ) :
    AddCommGroup (StableAutomorphicFunctions F n) := Submodule.addCommGroup _
local instance weakConjDualSpaceGroup (S : OperatorRealization F n) : AddCommGroup S.Space :=
  Submodule.addCommGroup _

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

namespace OperatorRealization

set_option maxHeartbeats 2000000 in
/-- If `S` is conjugate self-dual, its actual CM image `S.complexConj` realizes the
contragredient of `S`. The pairing is the conjugate-contragredient pairing of `S`
composed with the inverse of the actual CM equivalence `S ≃ S.complexConj` in the
second variable. -/
theorem complexConj_isContragredientOf_of_isConjugateSelfDual (S : OperatorRealization F n)
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

end OperatorRealization

end CMPairing

section DualBaseChange

variable {E : Type uE} {D : Type uD} [Field E] [NumberField E] [Field D] [NumberField D]
  [Algebra E D] [CompactSpace (AdeleQuotient E)] [CompactSpace (AdeleQuotient D)] {r : ℕ}

namespace CuspidalOperatorRealization.IsoClass

/-- Weak base change passes to supplied contragredients on both levels. At almost every
base place the spectra of both contragredients are the reciprocal spectra, and taking
reciprocals commutes with the residue-degree power. -/
theorem isWeakBaseChangeOf_of_isContragredientOf
    {S Sd : CuspidalOperatorRealization E r} {T Td : CuspidalOperatorRealization D r}
    (hbc : T.isoClass.IsWeakBaseChangeOf.{uE, uD, uV, uW} S.isoClass)
    (hS : Sd.realization.IsContragredientOf S.realization)
    (hT : Td.realization.IsContragredientOf T.realization) :
    Td.isoClass.IsWeakBaseChangeOf.{uE, uD, uV, uW} Sd.isoClass := by
  obtain ⟨P, Q, hPQ⟩ := (isWeakBaseChangeOf_isoClass_iff T S).mp hbc
  obtain ⟨Pd⟩ := cuspidalDualPresentationExistence.{uE, uV, uV} E r S Sd hS P
  obtain ⟨Qd⟩ := cuspidalDualPresentationExistence.{uD, uW, uW} D r T Td hT Q
  refine (isWeakBaseChangeOf_isoClass_iff Td Sd).mpr ⟨Pd, Qd, ?_⟩
  filter_upwards [hPQ, Pd.exceptional.eventually_cofinite_notMem,
    SpectralSystem.eventually_avoidsAbove (F := E) Qd.exceptional] with v hv hvd hwd
  obtain ⟨hp, hq, he, hs⟩ := hv
  refine ⟨hvd, hwd, he, fun w => ?_⟩
  rw [T.eigenvalues_eq_map_inv_of_isContragredientOf Td Q Qd hT w.1 (hq w) (hwd w),
    S.eigenvalues_eq_map_inv_of_isContragredientOf Sd P Pd hS v hp hvd, hs w]
  simp only [Eigenvalues.power, Sym.map_map, Function.comp_def, inv_pow]

end CuspidalOperatorRealization.IsoClass

end DualBaseChange

section CMBaseChange

variable {E : Type uE} {D : Type uD} [Field E] [NumberField E] [IsCMField E]
  [Field D] [NumberField D] [IsCMField D] [Algebra E D]

private theorem complexConj_algebraMap_of_isCM (x : E) :
    IsCMField.complexConj D (algebraMap E D x) = algebraMap E D (IsCMField.complexConj E x) := by
  let φ : D →+* ℂ := Classical.choice inferInstance
  apply φ.injective
  rw [IsCMField.complexEmbedding_complexConj]
  have h := IsCMField.complexEmbedding_complexConj (K := E) (φ.comp (algebraMap E D)) x
  simp only [RingHom.comp_apply] at h
  rw [h]

private theorem integersConj_algebraMap (x : 𝓞 E) :
    RingOfIntegers.mapRingEquiv (fieldConj D).symm (algebraMap (𝓞 E) (𝓞 D) x) =
      algebraMap (𝓞 E) (𝓞 D) (RingOfIntegers.mapRingEquiv (fieldConj E).symm x) := by
  apply RingOfIntegers.ext
  change (fieldConj D).symm (algebraMap E D (x : E)) =
    algebraMap E D ((fieldConj E).symm (x : E))
  rw [fieldConj_symm, fieldConj_symm]
  exact complexConj_algebraMap_of_isCM (x : E)

private theorem fieldConj_liesOver (v : Global.FinitePlace E) (w : Global.FinitePlace D)
    [w.asIdeal.LiesOver v.asIdeal] :
    (finitePlaceEquiv (fieldConj D) w).asIdeal.LiesOver
      (finitePlaceEquiv (fieldConj E) v).asIdeal := by
  constructor
  ext x
  have hv := Ideal.over_def w.asIdeal v.asIdeal
  change RingOfIntegers.mapRingEquiv (fieldConj E) x ∈ v.asIdeal ↔
    RingOfIntegers.mapRingEquiv (fieldConj D) (algebraMap _ _ x) ∈ w.asIdeal
  rw [hv, Ideal.mem_comap]
  have heq : algebraMap (𝓞 E) (𝓞 D) (RingOfIntegers.mapRingEquiv (fieldConj E) x) =
      RingOfIntegers.mapRingEquiv (fieldConj D) (algebraMap (𝓞 E) (𝓞 D) x) := by
    apply RingOfIntegers.ext
    exact (complexConj_algebraMap_of_isCM (x : E)).symm
  rw [heq]

private def conjugatePlaceAbove (v : Global.FinitePlace E) (w : FinitePlacesAbove D v) :
    FinitePlacesAbove D (finitePlaceEquiv (fieldConj E).symm v) := by
  letI := w.2
  refine ⟨finitePlaceEquiv (fieldConj D).symm w.1, ?_⟩
  simpa only [fieldConj_symm] using fieldConj_liesOver v w.1

private theorem map_placeIdeal {K : Type*} [Field K] (g : K ≃+* K) (v : Global.FinitePlace K) :
    (finitePlaceEquiv g v).asIdeal.map (RingOfIntegers.mapRingEquiv g).toRingHom = v.asIdeal :=
  Ideal.map_comap_of_surjective _ (RingOfIntegers.mapRingEquiv g).surjective _

private theorem conjugatePlaceAbove_inertiaDeg (v : Global.FinitePlace E)
    (w : FinitePlacesAbove D v) :
    (conjugatePlaceAbove v w).1.asIdeal.inertiaDeg (𝓞 E) = w.1.asIdeal.inertiaDeg (𝓞 E) := by
  let := w.2
  let := (conjugatePlaceAbove v w).2
  rw [Ideal.inertiaDeg_eq_of_isMaximal (finitePlaceEquiv (fieldConj E).symm v).asIdeal,
    Ideal.inertiaDeg_eq_of_isMaximal v.asIdeal]
  let ev := Ideal.quotientEquiv (finitePlaceEquiv (fieldConj E).symm v).asIdeal v.asIdeal
    (RingOfIntegers.mapRingEquiv (fieldConj E).symm) (map_placeIdeal (fieldConj E).symm v).symm
  let fw := Ideal.quotientEquiv (conjugatePlaceAbove v w).1.asIdeal w.1.asIdeal
    (RingOfIntegers.mapRingEquiv (fieldConj D).symm) (map_placeIdeal (fieldConj D).symm w.1).symm
  apply Algebra.finrank_eq_of_equiv_equiv ev fw
  apply RingHom.ext
  intro x
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
  change Ideal.Quotient.mk w.1.asIdeal
      (algebraMap (𝓞 E) (𝓞 D) (RingOfIntegers.mapRingEquiv (fieldConj E).symm y)) =
    Ideal.Quotient.mk w.1.asIdeal
      (RingOfIntegers.mapRingEquiv (fieldConj D).symm (algebraMap (𝓞 E) (𝓞 D) y))
  rw [integersConj_algebraMap]

private theorem conjugatePlaceAbove_ramificationIdx (v : Global.FinitePlace E)
    (w : FinitePlacesAbove D v) :
    (conjugatePlaceAbove v w).1.asIdeal.ramificationIdx (𝓞 E) =
      w.1.asIdeal.ramificationIdx (𝓞 E) := by
  let := w.2
  let := (conjugatePlaceAbove v w).2
  let g := RingOfIntegers.mapRingEquiv (fieldConj D).symm
  let m : Ideal (𝓞 D) ≃* Ideal (𝓞 D) :=
    { (Ideal.relIsoOfBijective g.toRingHom g.bijective).symm.toEquiv with
      map_mul' := fun I J => Ideal.map_mul _ _ _ }
  have hmap (I : Ideal (𝓞 D)) : m I = I.map g.toRingHom := rfl
  have hc : g.toRingHom.comp (algebraMap (𝓞 E) (𝓞 D)) =
      (algebraMap (𝓞 E) (𝓞 D)).comp (RingOfIntegers.mapRingEquiv (fieldConj E).symm).toRingHom :=
    RingHom.ext integersConj_algebraMap
  rw [Ideal.IsDedekindDomain.ramificationIdx_eq_multiplicity
        (finitePlaceEquiv (fieldConj E).symm v).asIdeal _
        (Ideal.map_ne_bot_of_ne_bot (finitePlaceEquiv (fieldConj E).symm v).ne_bot),
      Ideal.IsDedekindDomain.ramificationIdx_eq_multiplicity v.asIdeal
        _ (Ideal.map_ne_bot_of_ne_bot v.ne_bot), ← multiplicity_map_eq m, hmap, hmap]
  change multiplicity ((finitePlaceEquiv (fieldConj D).symm w.1).asIdeal.map g.toRingHom)
      (((finitePlaceEquiv (fieldConj E).symm v).asIdeal.map
        (algebraMap (𝓞 E) (𝓞 D))).map g.toRingHom) =
    multiplicity w.1.asIdeal (v.asIdeal.map (algebraMap (𝓞 E) (𝓞 D)))
  rw [map_placeIdeal (fieldConj D).symm, Ideal.map_map, hc, ← Ideal.map_map, map_placeIdeal]

variable [CompactSpace (AdeleQuotient E)] [CompactSpace (AdeleQuotient D)] {r : ℕ}

namespace CuspidalOperatorRealization.IsoClass

/-- For an extension of CM fields, weak base change passes to the actual CM images on
both levels. The witnessing presentations are the arithmetic pullbacks along the CM
involutions; the involutions match the places above each base place together with
their ramification indices and residue degrees. -/
theorem isWeakBaseChangeOf_complexConj
    {S : CuspidalOperatorRealization E r} {T : CuspidalOperatorRealization D r}
    (hbc : T.isoClass.IsWeakBaseChangeOf.{uE, uD, uV, uW} S.isoClass) :
    T.complexConj.isoClass.IsWeakBaseChangeOf.{uE, uD, uV, uW} S.complexConj.isoClass := by
  obtain ⟨P, Q, hPQ⟩ := (isWeakBaseChangeOf_isoClass_iff T S).mp hbc
  rw [← CuspidalOperatorRealization.arithmeticComap_fieldConj S,
    ← CuspidalOperatorRealization.arithmeticComap_fieldConj T]
  refine (isWeakBaseChangeOf_isoClass_iff _ _).mpr
    ⟨P.arithmeticComap (fieldConj E), Q.arithmeticComap (fieldConj D), ?_⟩
  have hplaces :=
    (finitePlaceEquiv (fieldConj E).symm).injective.tendsto_cofinite.eventually hPQ
  filter_upwards [hplaces] with v hv
  obtain ⟨hp, hq, he, hs⟩ := hv
  have hp' : v ∉ (P.arithmeticComap (fieldConj E)).exceptional := by
    simpa only [CuspidalSpectralPresentation.arithmeticComap,
      CuspidalSpectralPresentation.spectralSystem_exceptional,
      FiniteAdelicGL.transportExceptional, Finset.mem_map_equiv, Equiv.symm_symm] using hp
  have hq' (w : FinitePlacesAbove D v) :
      w.1 ∉ (Q.arithmeticComap (fieldConj D)).exceptional := by
    simpa only [CuspidalSpectralPresentation.arithmeticComap,
      CuspidalSpectralPresentation.spectralSystem_exceptional,
      FiniteAdelicGL.transportExceptional, Finset.mem_map_equiv, Equiv.symm_symm,
      conjugatePlaceAbove] using hq (conjugatePlaceAbove v w)
  refine ⟨hp', hq', fun w => (conjugatePlaceAbove_ramificationIdx v w).symm.trans
    (he (conjugatePlaceAbove v w)), fun w => ?_⟩
  change Q.spectralSystem.eigenvalues (conjugatePlaceAbove v w).1 (hq (conjugatePlaceAbove v w)) =
    (P.spectralSystem.eigenvalues (finitePlaceEquiv (fieldConj E).symm v) hp).power
      (w.1.asIdeal.inertiaDeg (𝓞 E))
  rw [← conjugatePlaceAbove_inertiaDeg v w]
  exact hs (conjugatePlaceAbove v w)

end CuspidalOperatorRealization.IsoClass

end CMBaseChange

end Langlands.Automorphic
