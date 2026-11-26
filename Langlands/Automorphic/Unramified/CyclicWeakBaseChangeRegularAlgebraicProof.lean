import Langlands.Global.AdelicFunctoriality.AlmostEverywhereSplitNormProof
import Langlands.Automorphic.Unramified.CyclicWeakBaseChangeRegularAlgebraicStatement
import Langlands.Automorphic.Unramified.ComplexPlaceParameterTransportInvolution

/-! # Regular algebraicity of a weak cyclic descent at a conjugate pair -/

noncomputable section

universe uK uE uV uW

set_option autoImplicit false

namespace Langlands.Automorphic.Unramified

open NumberField Langlands.Global Langlands.Global.AdelicFunctoriality
open Langlands.LocalFactor.Archimedean

/-- Transport of a complex-place parameter list between the selected coordinates at a
complex place and at a place above it preserves Clozel regular algebraicity: conjugation
interchanges the `z` and conjugate-`z` exponents of every block. -/
theorem isClozelRegularAlgebraic_complexPlaceParameterTransport
    {F : Type uK} {E : Type uE} [Field F] [Field E] [NumberField F] [NumberField E]
    [Algebra F E] (v : {v : NumberField.InfinitePlace F // v.IsComplex})
    (w : InfinitePlacesAbove E v.1) {n : ℕ} {ds : List ComplexCharacterData}
    (h : ComplexPlaceParameter.IsClozelRegularAlgebraic n ds) :
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

/-- Restricted complex-place compatibility of cyclic weak base change and the totally
complex infinitesimal-character bridges over both fields give regular algebraicity of an
actual weak descent of a regular algebraic class. -/
theorem cyclicWeakBaseChangeRegularAlgebraicTC :
    CyclicWeakBaseChangeRegularAlgebraicTCStatement.{uK, uE, uV, uW} := by
  intro hB7 hBridgeK hBridgeE K E _ _ _ _ _ _ _ _ _ _ hPrime v₀ hv₀ w₀ wc hw₀ hwc r S T
    hSu hTu hSv hSc hTw hTc hbc hT
  classical
  have : IsTotallyComplex E := isTotallyComplex_of_algebra K E
  -- The upstairs parameters, their infinitesimal character and their regularity.
  choose dsT hdsT using (hBridgeE.1 E r T).2
  obtain ⟨χ, hχ, hTχ⟩ := T.isoClass_isRegularAlgebraic_iff.mp hT
  obtain ⟨⟨θ, hθ, _⟩, hActT⟩ := hBridgeE.2.1 E r T dsT hdsT
  obtain ⟨x, hx⟩ := exists_ne (0 : T.Space)
  have hθχ : θ = χ := (hActT θ hθ).unique hx hTχ
  have hReg := (hBridgeE.2.2 E (r + 1) dsT θ hθ).mp (hθχ.symm ▸ hχ)
  -- A place of `E` above every complex place of `K`, and the transported lists there.
  let wv (v : {v : NumberField.InfinitePlace K // v.IsComplex}) : InfinitePlacesAbove E v.1 :=
    Classical.choice (Langlands.Global.AdelicFunctoriality.exists_infinitePlace_above v.1)
  let dsS (v : {v : NumberField.InfinitePlace K // v.IsComplex}) : List ComplexCharacterData :=
    complexPlaceParameterTransport v (wv v) (dsT (complexPlaceAbove v (wv v)))
  have hdsS (v : {v : NumberField.InfinitePlace K // v.IsComplex}) :
      S.realization.HasComplexPlaceParameter v (dsS v) := by
    have hTv : T.isoClass.HasComplexPlaceParameter (complexPlaceAbove v (wv v))
        (complexPlaceParameterTransport v (wv v) (dsS v)) := by
      have hinv := complexPlaceParameterTransport_involutive v (wv v)
        (dsT (complexPlaceAbove v (wv v)))
      change T.isoClass.HasComplexPlaceParameter _ (complexPlaceParameterTransport v (wv v)
        (complexPlaceParameterTransport v (wv v) (dsT (complexPlaceAbove v (wv v)))))
      rw [hinv]
      exact (T.isoClass_hasComplexPlaceParameter _ _).mpr (hdsT _)
    exact (S.isoClass_hasComplexPlaceParameter _ _).mp
      (((hB7 K E hPrime v₀ hv₀ w₀ wc hw₀ hwc).1 r S T hSu hTu hSv hSc hTw hTc hbc
        v (wv v) (dsS v)).mpr hTv)
  -- The downstairs infinitesimal character and its regularity.
  obtain ⟨⟨ψ, hψ, _⟩, hActS⟩ := hBridgeK.2.1 K r S dsS hdsS
  exact S.isoClass_isRegularAlgebraic_iff.mpr
    ⟨ψ, (hBridgeK.2.2 K (r + 1) dsS ψ hψ).mpr
      (fun v => isClozelRegularAlgebraic_complexPlaceParameterTransport v (wv v) (hReg _)),
      hActS ψ hψ⟩

end Langlands.Automorphic.Unramified
