import Langlands.Automorphic.FiniteLocalCMTransport
import Langlands.Automorphic.ArithmeticTransportRelation
import Langlands.Automorphic.AssociatedPresentationComparison
import Langlands.BaseChange.LocalGaloisStabilizer
import Langlands.Global.AdelicFunctoriality.UniquePlaceCompletion
import Langlands.Representation.CuspidalSupport.AssociationReduction

/-! # Arithmetic transport of irreducible local components -/

noncomputable section

universe uK uL uV uW

set_option autoImplicit false

namespace Langlands.Global.AdelicGLTransport

open NumberField IsDedekindDomain.HeightOneSpectrum AdelicFunctoriality

variable {K : Type uK} {L : Type uL} [Field K] [NumberField K] [Field L] [NumberField L]

/-- A continuous completion equivalence extending the field equivalence can be
used for the transported local inclusion. -/
theorem finiteEquiv_localInclusion_of_extends (n : ℕ) (e : K ≃+* L)
    (v : FinitePlace L) {p : FinitePlace K} (hp : finitePlaceEquiv e v = p)
    (a : p.adicCompletion K ≃+* v.adicCompletion L) (ha : Continuous a)
    (he : ∀ x : K, a (algebraMap K (p.adicCompletion K) x) =
      algebraMap L (v.adicCompletion L) (e x))
    (g : FiniteLocalGL K n p) :
    finiteEquiv n e (FiniteAdelicGL.localInclusion K n p g) =
      FiniteAdelicGL.localInclusion L n v (Matrix.GeneralLinearGroup.map a.toRingHom g) := by
  subst p
  rw [finiteEquiv_localInclusion]
  have h := (denseRange_algebraMap K (finitePlaceEquiv e v)).equalizer
    (continuous_finiteCompletionEquiv e v) ha (funext fun x =>
      (finiteCompletionEquiv_coe e v x).trans (he x).symm)
  congr 1
  apply Units.ext
  apply Matrix.ext
  intro i j
  exact congrFun h (g i j)

end Langlands.Global.AdelicGLTransport

namespace Langlands.Automorphic.CuspidalSpectralPresentation

open Langlands.Global Langlands.Global.AdelicFunctoriality
open CuspidalOperatorRealization
open scoped NumberField FiniteExtension Valued

variable {K : Type uK} {L : Type uL} [Field K] [NumberField K] [Field L] [NumberField L]
  [CompactSpace (AdeleQuotient K)] [CompactSpace (AdeleQuotient L)] {r : ℕ}

variable {M : Type*} [Field M] [NumberField M] {n : ℕ}

local instance : AddCommGroup (RationalInvariantFunctions M n) := Submodule.addCommGroup _
local instance : AddCommGroup (ContinuousRationalFunctions M n) := Submodule.addCommGroup _
local instance : AddCommGroup (FiniteSmoothRationalFunctions M n) := Submodule.addCommGroup _
local instance : AddCommGroup (AutomorphicForms M n) := Submodule.addCommGroup _
local instance : AddCommGroup (StableAutomorphicFunctions M n) := Submodule.addCommGroup _
local instance (S : OperatorRealization M n) : AddCommGroup S.Space := Submodule.addCommGroup _
local instance {v : FinitePlace M} (A : LocalRealization M n v) :
    AddCommGroup A.Space := Submodule.addCommGroup _

set_option maxHeartbeats 800000 in
/-- Arithmetic transport identifies irreducible local components via inverse
pullback along the isomorphism that transports their local inclusions. -/
theorem nonempty_localComponent_equiv_of_arithmeticTransport
    {S : CuspidalOperatorRealization K r} {T : CuspidalOperatorRealization L r}
    (P : CuspidalSpectralPresentation.{uK, uV} S) (Q : CuspidalSpectralPresentation.{uL, uW} T)
    (p : FinitePlace K) (v : FinitePlace L)
    (e : K ≃+* L) (a : FiniteLocalGL K (r + 1) p ≃* FiniteLocalGL L (r + 1) v)
    (ha : ∀ g, AdelicGLTransport.finiteEquiv (r + 1) e
        (FiniteAdelicGL.localInclusion K (r + 1) p g) =
      FiniteAdelicGL.localInclusion L (r + 1) v (a g))
    (h : S.IsArithmeticTransport e T)
    (hP : (P.localComponent p).IsIrreducible) (hQ : (Q.localComponent v).IsIrreducible) :
    Nonempty (Representation.Equiv ((P.localComponent p).representation.comp a.symm.toMonoidHom)
      (Q.localComponent v).representation) := by
  obtain ⟨φ, hφ⟩ := h
  have : T.realization.IsIrreducible := T.irreducible
  have : Representation.IsIrreducible ((P.localComponent p).representation.comp a.symm.toMonoidHom) :=
    (CuspidalSupport.isIrreducible_comp_mulEquiv_iff _ a.symm).mpr hP
  have : (Q.localComponent v).representation.IsIrreducible := hQ
  let f₀ := S.realization.localSubspaceInclusion p _ (P.localComponent_le_full p)
  let f : Representation.IntertwiningMap
      ((P.localComponent p).representation.comp a.symm.toMonoidHom)
      (T.realization.localRepresentation v) :=
    { toLinearMap := φ.toLinearMap.comp f₀.toLinearMap
      isIntertwining' := fun g => by
        apply LinearMap.ext
        intro x
        change φ (f₀ ((P.localComponent p).representation (a.symm g) x)) =
          T.realization.finiteRepresentation (FiniteAdelicGL.localInclusion L (r + 1) v g)
            (φ (f₀ x))
        have hf₀ := Representation.IntertwiningMap.isIntertwining _ _ f₀ (a.symm g) x
        have hφ₀ := hφ.1 (FiniteAdelicGL.localInclusion K (r + 1) p (a.symm g)) (f₀ x)
        have hg := (ha (a.symm g)).trans
          (congrArg (FiniteAdelicGL.localInclusion L (r + 1) v) (a.apply_symm_apply g))
        exact (congrArg φ hf₀).trans (hφ₀.trans
          (congrArg (fun d => T.realization.finiteRepresentation d (φ (f₀ x))) hg)) }
  have hf : Function.Injective f :=
    φ.injective.comp (S.realization.localSubspaceInclusion_injective p _
      (P.localComponent_le_full p))
  exact T.realization.nonempty_local_equiv_of_injective v _ _ f hf
    (T.realization.localSubspaceInclusion v _ (Q.localComponent_le_full v))
    (T.realization.localSubspaceInclusion_injective v _ (Q.localComponent_le_full v))

section UniquePlace

variable {F : Type uK} {E : Type uL} [Field F] [NumberField F] [Field E] [NumberField E]
  [Algebra F E] [IsGalois F E] [CompactSpace (AdeleQuotient E)]
  {v : FinitePlace F} (w : FinitePlacesAbove E v)
  {T U : CuspidalOperatorRealization E r}
  (P : CuspidalSpectralPresentation.{uL, uV} T)
  (Q : CuspidalSpectralPresentation.{uL, uW} U)

local instance : w.1.asIdeal.LiesOver v.asIdeal := w.2

/-- At the unique place, the local action in arithmetic transport is inverse
pullback by the actual extension of the global automorphism to the completion. -/
theorem nonempty_localComponent_equiv_of_galoisConjugate
    (hw : ∀ w' : FinitePlacesAbove E v, w' = w) (σ : E ≃ₐ[F] E)
    (h : T.isoClass.IsGaloisConjugate σ U.isoClass)
    (hP : (P.localComponent w.1).IsIrreducible) (hQ : (Q.localComponent w.1).IsIrreducible) :
    Nonempty (Representation.Equiv ((P.localComponent w.1).representation.comp
      (BaseChange.entrywiseAut ((uniquePlaceCompletionAutEquiv w hw σ)⁻¹) (r + 1)).toMonoidHom)
      (Q.localComponent w.1).representation) := by
  let τ := uniquePlaceCompletionAutEquiv w hw σ
  have hτ : Continuous τ := τ.toLinearMap.continuous_of_finiteDimensional
  exact P.nonempty_localComponent_equiv_of_arithmeticTransport Q w.1 w.1
    σ.toRingEquiv (BaseChange.entrywiseAut τ (r + 1))
    (AdelicGLTransport.finiteEquiv_localInclusion_of_extends (r + 1) σ.toRingEquiv w.1
      (finitePlaceEquiv_eq_of_unique w hw σ) τ.toRingEquiv hτ
      (uniquePlaceCompletionAutEquiv_algebraMap w hw σ))
    ((IsoClass.isArithmeticTransport_isoClass_iff _ T U).mp h) hP hQ

omit [IsGalois F E] [NumberField F] in
/-- Distinct smooth classes of the supplied irreducible local factors exclude
arithmetic stability of the global cuspidal class under the same automorphism. -/
theorem not_isGaloisStable_of_localComponent_isoClass_ne
    (σ : E ≃ₐ[F] E) (h : T.isoClass.IsGaloisConjugate σ U.isoClass)
    (hP : (P.localComponent w.1).IsIrreducible) (hQ : (Q.localComponent w.1).IsIrreducible)
    (hne : (Q.localComponent w.1).isoClass ≠ (P.localComponent w.1).isoClass) :
    ¬ T.isoClass.IsGaloisStable σ := by
  intro hstable
  have hc : U.isoClass = T.isoClass := h.target_unique hstable
  obtain ⟨e⟩ := (U.isoClass_eq_iff T).mp hc
  have htransport := Q.transport_localComponent_isoClass e w.1
  have hQ' : ((Q.transport e).localComponent w.1).IsIrreducible := by
    obtain ⟨f⟩ := (((Q.transport e).localComponent w.1).isoClass_eq_iff _).mp htransport
    exact (Langlands.isIrreducible_iff_of_equiv f).mpr hQ
  exact hne (htransport.symm.trans ((Q.transport e).localComponent_isoClass_eq P w.1 hQ' hP))

set_option maxHeartbeats 800000 in
/-- The distinct arithmetic conjugates in the unique-place hypothesis force
trivial stabilizer for the actual irreducible local factor. -/
theorem hasTrivialGaloisStabilizer_of_distinct_conjugates
    (hw : ∀ w' : FinitePlacesAbove E v, w' = w) (σ : E ≃ₐ[F] E)
    (hgen : ∀ τ : E ≃ₐ[F] E, τ ∈ Subgroup.zpowers σ)
    (hP : (P.localComponent w.1).IsIrreducible)
    (hconj : ∀ i : ℕ, 0 < i → i < Module.finrank F E →
      ∃ (U : CuspidalOperatorRealization E r) (Q : CuspidalSpectralPresentation.{uL, uW} U),
        T.isoClass.IsGaloisConjugate (σ ^ i) U.isoClass ∧
        (Q.localComponent w.1).IsIrreducible ∧
        (Q.localComponent w.1).isoClass ≠ (P.localComponent w.1).isoClass) :
    BaseChange.HasTrivialGaloisStabilizer (v.adicCompletion F) (E := w.1.adicCompletion E) (n := r + 1)
      (P.localComponent w.1).representation := by
  intro τ hτ hstable
  have hτ' : τ⁻¹ ≠ 1 := inv_ne_one.mpr hτ
  obtain ⟨i, hi, hi', he⟩ := exists_pow_of_completionAut_ne_one w hw σ hgen τ⁻¹ hτ'
  obtain ⟨U, Q, hTQ, hQ, hne⟩ := hconj i hi hi'
  have h := P.nonempty_localComponent_equiv_of_galoisConjugate w Q hw (σ ^ i) hTQ hP hQ
  rw [he, inv_inv] at h
  obtain ⟨f⟩ := h
  obtain ⟨e⟩ := hstable
  exact hne (((Q.localComponent w.1).isoClass_eq_iff _).mpr ⟨f.symm.trans e.symm⟩)

end UniquePlace

end Langlands.Automorphic.CuspidalSpectralPresentation
