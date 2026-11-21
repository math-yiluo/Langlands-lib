import Langlands.Automorphic.Unramified.QuadraticWeakBaseChangeSplitSquareIntegrableStatement
import Langlands.Automorphic.Unramified.CyclicStrongBaseChangeSupportStatement
import Langlands.Automorphic.Unramified.CyclicPrimeSingletonBaseChange
import Langlands.Automorphic.Unramified.SplitCompletionSquareIntegrability
import Langlands.Automorphic.AssociatedPresentationComparison
import Langlands.Automorphic.CuspidalAllLocalIrreduciblePresentationProof
import Langlands.Automorphic.CuspidalPresentationUniverse
import Langlands.Automorphic.CuspidalUnitaryLocalGenericity
import Langlands.Automorphic.OperatorLocalUnitaryForm
import Langlands.HarmonicAnalysis.PadicUnitaryAdditiveCharacterExistsProof
import Langlands.Representation.Aubert.SupportGrading
import Langlands.Representation.CuspidalSupport.FixedSupportDetectedEquiv
import Langlands.Representation.CuspidalSupport.UnitaryProductSupport
import Langlands.Representation.Exponents.SquareIntegrableUnitaryProduct
import Langlands.Representation.RankinSelberg.FieldTransport.Factors
import Langlands.Representation.Whittaker.FiniteProductCriterion
import Langlands.Representation.Whittaker.Transport

/-! # The split square-integrable comparison from strong split support -/

noncomputable section

open scoped BigOperators NumberField Langlands.Global.AdelicFunctoriality.FiniteExtension

universe uF uE uV uW uK uR

namespace Langlands.Automorphic.Unramified

open Langlands.Global Langlands.Global.AdelicFunctoriality
open Langlands.Global.AdelicFunctoriality.FiniteExtension
open Langlands.HarmonicAnalysis Langlands.Correspondence

variable {A : Type*} [Field A] [NumberField A]

local instance splitSupportRationalAddCommGroup (n : ℕ) :
    AddCommGroup (RationalInvariantFunctions A n) :=
  Submodule.addCommGroup _
local instance splitSupportContinuousAddCommGroup (n : ℕ) :
    AddCommGroup (ContinuousRationalFunctions A n) :=
  Submodule.addCommGroup _
local instance splitSupportSmoothAddCommGroup (n : ℕ) :
    AddCommGroup (FiniteSmoothRationalFunctions A n) :=
  Submodule.addCommGroup _
local instance splitSupportFormsAddCommGroup (n : ℕ) : AddCommGroup (AutomorphicForms A n) :=
  Submodule.addCommGroup _
local instance splitSupportLocalAddCommGroup {n : ℕ} {v : FinitePlace A} (L : LocalRealization A n v) :
    AddCommGroup L.Space :=
  Submodule.addCommGroup _

section Completions

open CompletionPadic

variable {F : Type uF} {E : Type uE} [Field F] [Field E] [NumberField F] [NumberField E]
  [Algebra F E] (v : FinitePlace F) (w : FinitePlace E) [w.asIdeal.LiesOver v.asIdeal]

private theorem split_rationalPlace_eq : rationalPlace w = rationalPlace v := by
  have := Ideal.LiesOver.trans w.asIdeal v.asIdeal (rationalPlace v).asIdeal
  exact IsDedekindDomain.HeightOneSpectrum.ext
    (Ideal.over_def w.asIdeal (rationalPlace v).asIdeal).symm

private theorem split_residuePrime_eq : residuePrime w = residuePrime v :=
  congrArg (fun q => (Rat.HeightOneSpectrum.primesEquiv q : ℕ)) (split_rationalPlace_eq v w)

private theorem split_completionMap_comp_padicMap :
    (completionMap v w).comp (padicMap v) = padicMapAt w (split_residuePrime_eq v w) := by
  have := Ideal.LiesOver.trans w.asIdeal v.asIdeal (rationalPlace v).asIdeal
  rw [padicMapAt_eq_of_rationalPlace_eq w (rationalPlace v) (split_rationalPlace_eq v w)]
  unfold padicMap
  rw [← RingHom.comp_assoc, ClassField.Global.CompletionTower.completionMap_comp]

private def splitPadicEquiv (hs : SplitsCompletelyAt (N := E) v) :
    letI := (padicField v).algebra
    letI := (padicFieldAt w (split_residuePrime_eq v w)).algebra
    (padicField v).Carrier ≃ₐ[Padic (residuePrime v)]
      (padicFieldAt w (split_residuePrime_eq v w)).Carrier :=
  letI := (padicField v).algebra
  letI := (padicFieldAt w (split_residuePrime_eq v w)).algebra
  { splitCompletionEquiv v w hs with
    commutes' x := DFunLike.congr_fun (split_completionMap_comp_padicMap v w) x }

end Completions

section LocalSupport

open CompletionPadic VirtualRepresentation.PadicSupercuspidal

variable {F : Type uF} [Field F] [NumberField F]
  {p : ℕ} [Fact p.Prime] (K : PadicField.{uK} p)
  (v : FinitePlace F) (hp : residuePrime v = p)

private abbrev completionGroupEquiv (n : ℕ)
    (α : letI := (padicFieldAt v hp).algebra
      K.Carrier ≃ₐ[Padic p] (padicFieldAt v hp).Carrier) :
    letI := K.canonicalTopologicalData.topology
    letI := (padicFieldAt v hp).canonicalTopologicalData.topology
    GeneralLinear n K.Carrier ≃ₜ* GeneralLinear n (padicFieldAt v hp).Carrier :=
  letI := K.canonicalTopologicalData.topology
  letI := (padicFieldAt v hp).canonicalTopologicalData.topology
  letI := (padicFieldAt v hp).algebra
  GeneralLinear.fieldEquiv n α.toRingEquiv
    (continuous_algEquiv K (padicFieldAt v hp) α)
    (continuous_algEquiv (padicFieldAt v hp) K α.symm)

private def supportLabel (d : K.canonicalTopologicalData.CuspidalDatum.{uR, uK}) :
    Σ k : ℕ, SupercuspidalAutomorphicClass.{uK, uR} K k.succPNat := by
  rcases d with ⟨r | r, hr, c⟩
  · exact (Nat.not_lt_zero _ hr).elim
  · exact ⟨r, c⟩

private theorem supportLabel_recovers (d : K.canonicalTopologicalData.CuspidalDatum.{uR, uK}) :
    supercuspidalSupportDatum K (supportLabel K d) = d := by
  rcases d with ⟨r | r, hr, c⟩
  · exact (Nat.not_lt_zero _ hr).elim
  · rfl

variable [CompactSpace (AdeleQuotient F)]

private theorem localComponent_hasFunctional_at
    {r : ℕ} {S : CuspidalOperatorRealization F r}
    (P : CuspidalSpectralPresentation.{uF, uV} S)
    (hS : ClassField.Global.RelativeWeilGroup.HasUnitaryCentralCharacter S)
    (hI : (P.localComponent v).IsIrreducible)
    (hA : letI := (padicFieldAt v hp).canonicalTopologicalData.topology
      IsAdmissible (P.localComponent v).representation)
    (ψ : @UnitaryAdditiveCharacter (padicFieldAt v hp).Carrier _
      (padicFieldAt v hp).canonicalTopologicalData.topology) :
    letI := (padicFieldAt v hp).canonicalTopologicalData.topology
    Whittaker.HasFunctional (N := GeneralLinear.upperUnipotent (r + 1) (padicFieldAt v hp).Carrier)
      (θ := Whittaker.standardCharacter ψ r) (P.localComponent v).representation := by
  subst p
  exact (cuspidalUnitaryLocalGenericity F r S hS P v hI
    ((P.localComponent v).isAdmissible_canonical_iff.mp hA) ψ).2.2

set_option maxHeartbeats 650000 in
private theorem attached_component_properties
    {r : ℕ} {c : CuspidalOperatorRealization.IsoClass F r}
    (α : letI := (padicFieldAt v hp).algebra
      K.Carrier ≃ₐ[Padic p] (padicFieldAt v hp).Carrier)
    (ρ : letI := K.canonicalTopologicalData.topology
      SmoothRep.{0, uK, uR} ℂ (GeneralLinear (r + 1) K.Carrier))
    (hc : c.toOperatorClass.IsUnitarizable)
    (hρ : letI := K.canonicalTopologicalData.topology; ρ.IsIrreducible)
    (h : c.HasPadicLocalComponent.{uF, uV, uK, uR} v hp K α ρ)
    (ψ : @UnitaryAdditiveCharacter K.Carrier _ K.canonicalTopologicalData.topology) :
    letI := K.canonicalTopologicalData.topology
    IsUnitarizable ρ.representation ∧
      Whittaker.HasFunctional (N := GeneralLinear.upperUnipotent (r + 1) K.Carrier)
        (θ := Whittaker.entrywiseCharacter ψ.complex (r + 1)) ρ.representation := by
  let := K.canonicalTopologicalData.topology
  let := (padicFieldAt v hp).canonicalTopologicalData.topology
  let := (padicFieldAt v hp).algebra
  obtain ⟨S, P, hS, ⟨e⟩⟩ := h
  let g := completionGroupEquiv K v hp (r + 1) α
  change Representation.Equiv ((P.localComponent v).representation.comp g.toMonoidHom)
    ρ.representation at e
  have hunit : S.realization.IsUnitarizable := by
    rw [← hS] at hc
    exact hc
  have hLocalUnit : IsUnitarizable (P.localComponent v).representation :=
    (hunit.localRestriction v).of_injective
      (S.realization.localSubspaceInclusion v _ (P.localComponent_le_full v))
      (S.realization.localSubspaceInclusion_injective v _ (P.localComponent_le_full v))
  refine ⟨(isUnitarizable_iff_of_equiv e).mp (hLocalUnit.comp g.toMonoidHom), ?_⟩
  have hI : (P.localComponent v).IsIrreducible :=
    (isIrreducible_comp_continuousMulEquiv_iff _ g).mp ((isIrreducible_iff_of_equiv e).mpr hρ)
  have hAdmρ := (CuspidalSupport.cuspidalEmbedding K K.canonicalTopologicalData (r + 1) ρ hρ).1
  have hAdm := (isAdmissible_comp_continuousMulEquiv_iff _ g).mp
    ((isAdmissible_iff_of_equiv e).mpr hAdmρ)
  let hα := continuous_algEquiv K (padicFieldAt v hp) α
  let hαs := continuous_algEquiv (padicFieldAt v hp) K α.symm
  let ψ' := HarmonicAnalysis.FieldTransport.additiveCharacter α.toRingEquiv hαs ψ
  have hψ : ∀ x, ψ' (α.toRingEquiv x) = ψ x := fun x =>
    congrArg ψ (α.symm_apply_apply x)
  obtain ⟨ℓ, hℓ⟩ := localComponent_hasFunctional_at v hp P
    (S.hasUnitaryCentralCharacter_of_isUnitarizable hunit) hI hAdm ψ'
  let f := RankinSelberg.FieldTransport.glFunctionalEquiv α.toRingEquiv hα hαs hψ r
    (P.localComponent v).representation
  rw [Whittaker.entrywiseCharacter_eq_standardCharacter]
  exact (Whittaker.hasFunctional_iff_of_equiv e).mp
    ⟨f.symm ℓ, show (f.symm ℓ).val ≠ 0 from hℓ⟩

private theorem irreducible_of_support {n : ℕ}
    {ρ : letI := K.canonicalTopologicalData.topology
      SmoothRep.{0, uK, max uK uR} ℂ (GeneralLinear n K.Carrier)}
    {s : Multiset (K.canonicalTopologicalData.CuspidalDatum.{uR, uK})}
    (h : K.canonicalTopologicalData.IsSupercuspidalSupport ρ s) :
    letI := K.canonicalTopologicalData.topology
    ρ.IsIrreducible := by
  obtain ⟨_, _, _, _, _, _, hI, _⟩ := h
  exact hI

set_option maxHeartbeats 900000 in
private theorem isobaric_card_eq_one_of_support
    {r : ℕ} {D : IsobaricData F} (hRank : D.rank = r + 1)
    (hD : D.IsUnitary)
    (α : letI := (padicFieldAt v hp).algebra
      K.Carrier ≃ₐ[Padic p] (padicFieldAt v hp).Carrier)
    {s : Multiset (Σ k : ℕ, SupercuspidalAutomorphicClass.{uK, uR} K k.succPNat)}
    (h : D.HasLocalSupercuspidalSupport.{uF, uV, uK, uR} v hp K α s)
    (ψ : @UnitaryAdditiveCharacter K.Carrier _ K.canonicalTopologicalData.topology)
    (π : letI := K.canonicalTopologicalData.topology
      SmoothRep.{0, uK, max uK uR} ℂ (GeneralLinear (r + 1) K.Carrier))
    (hπ : K.canonicalTopologicalData.IsSupercuspidalSupport π
      (s.map (supercuspidalSupportDatum K)))
    (hπsq : letI := K.canonicalTopologicalData.topology
      K.canonicalTopologicalData.IsSquareIntegrable π.representation)
    (hπgen : letI := K.canonicalTopologicalData.topology
      Whittaker.HasFunctional (N := GeneralLinear.upperUnipotent (r + 1) K.Carrier)
      (θ := Whittaker.entrywiseCharacter ψ.complex (r + 1)) π.representation) :
    D.card = 1 := by
  let T := K.canonicalTopologicalData
  let := T.topology
  obtain ⟨b, c, hc, ρ, t, hAttach, hρ, ht⟩ := h
  let B : GeneralLinear.BlockShape (r + 1) :=
    { length := b
      size := fun j => (c j).rank
      positive := fun j => (c j).rank_pos
      sum_eq := by
        rw [← hRank, IsobaricData.rank_eq_sum, ← hc, Multiset.map_map]
        rfl }
  have hProps (j : Fin b) := attached_component_properties K v hp α (ρ j)
    (hD (c j) (hc ▸ Multiset.mem_map_of_mem c (Finset.mem_univ_val j)))
    (irreducible_of_support K (hρ j)) (hAttach j) ψ
  have hU (j : Fin B.length) : (ρ j).IsIrreducible ∧ IsUnitarizable (ρ j).representation :=
    ⟨irreducible_of_support K (hρ j), (hProps j).1⟩
  let prod := (T.normalizedProductInductionFunctor B).obj ρ
  have hSupport : T.IsSupercuspidalSupport prod
      (s.map (supercuspidalSupportDatum K)) := by
    change T.IsSupercuspidalSupport prod ((Multiset.mapAddMonoidHom (supercuspidalSupportDatum K)) s)
    rw [ht, map_sum (Multiset.mapAddMonoidHom (supercuspidalSupportDatum K))]
    exact T.normalizedUnitaryProduct_hasSupercuspidalSupport.{uK, uR}
      (r + 1) (Nat.succ_pos r) B ρ hU (fun j => (t j).map (supercuspidalSupportDatum K)) hρ
  have hProdFunctional :=
    (Whittaker.hasFunctional_finiteProduct_iff.{uK, uR} T ψ B ρ).mpr
      (fun j => (hProps j).2)
  let e := CuspidalSupport.fixedSupportDetectedEquiv T ψ (Nat.succ_pos r) π prod
    _ hπ hSupport ((Whittaker.hasFunctional_iff_nontrivial_topDerivative T ψ _ π).mp hπgen)
    ((Whittaker.hasFunctional_iff_nontrivial_topDerivative T ψ _ prod).mp hProdFunctional)
  have hNT : Nontrivial π :=
    Classification.SegmentHeadSupport.nontrivial_of_isIrreducible (irreducible_of_support K hπ)
  have hOne : B.length = 1 :=
    squareIntegrableUnitaryProduct.{uK, uR} p K T (r + 1) (Nat.succ_pos r) B ρ hU π
      hπsq ⟨SmoothRep.ofHom e.toIntertwiningMap, e.injective⟩
  simpa [← hc, B] using hOne

private theorem singleton_support_component {r : ℕ} {c : CuspidalOperatorRealization.IsoClass F r}
    (α : letI := (padicFieldAt v hp).algebra
      K.Carrier ≃ₐ[Padic p] (padicFieldAt v hp).Carrier)
    {s : Multiset (Σ k : ℕ, SupercuspidalAutomorphicClass.{uK, uR} K k.succPNat)}
    (h : IsobaricData.HasLocalSupercuspidalSupport.{uF, uV, uK, uR}
      (IsobaricData.ofCuspidal (PositiveRankCuspidalClass.ofFixedRank c)) v hp K α s) :
    letI := K.canonicalTopologicalData.topology
    ∃ ρ : SmoothRep.{0, uK, max uK uR} ℂ (GeneralLinear (r + 1) K.Carrier),
      c.HasPadicLocalComponent.{uF, uV, uK, max uK uR} v hp K α ρ ∧
      K.canonicalTopologicalData.IsSupercuspidalSupport ρ (s.map (supercuspidalSupportDatum K)) := by
  let := K.canonicalTopologicalData.topology
  obtain ⟨b, d, hd, ρ, t, hAttach, hρ, ht⟩ := h
  have hb : b = 1 := by
    simpa [IsobaricData.ofCuspidal] using congrArg Multiset.card hd
  subst b
  have hd0 : d 0 = PositiveRankCuspidalClass.ofFixedRank c := by
    have hmem := Multiset.mem_map_of_mem d (Finset.mem_univ_val (0 : Fin 1))
    rw [hd, IsobaricData.ofCuspidal, Multiset.mem_singleton] at hmem
    exact hmem
  have ht0 : s = t 0 := ht.trans (Fin.sum_univ_one _)
  have aux (a : PositiveRankCuspidalClass F)
      (ha : a = PositiveRankCuspidalClass.ofFixedRank c)
      (τ : SmoothRep.{0, uK, max uK uR} ℂ (GeneralLinear a.rank K.Carrier))
      (hτ : a.2.HasPadicLocalComponent.{uF, uV, uK, max uK uR} v hp K α τ)
      (hτs : K.canonicalTopologicalData.IsSupercuspidalSupport τ
        (s.map (supercuspidalSupportDatum K))) :
      ∃ ρ : SmoothRep.{0, uK, max uK uR} ℂ (GeneralLinear (r + 1) K.Carrier),
        c.HasPadicLocalComponent.{uF, uV, uK, max uK uR} v hp K α ρ ∧
        K.canonicalTopologicalData.IsSupercuspidalSupport ρ
          (s.map (supercuspidalSupportDatum K)) := by
    subst a
    exact ⟨τ, hτ, hτs⟩
  exact aux _ hd0 (ρ 0) (hAttach 0) (ht0.symm ▸ hρ 0)

end LocalSupport

open CompletionPadic

/-- Strong split support suffices for singleton cuspidality and the actual
split square-integrable comparison in the quadratic case. -/
def QuadraticWeakBaseChangeSplitSupportReductionStatement : Prop :=
  CyclicStrongBaseChangeSupportStatement.{uF, max uF uE, uF, uE, uV, uW} →
    QuadraticWeakBaseChangeSplitSquareIntegrableStatement.{uF, uE, uV, uW}

set_option maxHeartbeats 2200000 in
set_option backward.isDefEq.respectTransparency.types false in
/-- Recover the actual split comparison from the support clause, using the
nonzero top derivative to identify the irreducible local actions. -/
theorem quadraticWeakBaseChangeSplitSquareIntegrable_of_strongSupport :
    QuadraticWeakBaseChangeSplitSupportReductionStatement.{uF, uE, uV, uW} := by
  classical
  intro hStrong F E _ _ _ _ _ _ _ _ _ hDegree r S P D v hSq hSplit B hB hD hWeak
  obtain ⟨_, hStrongSplit, _, _⟩ := hStrong
  let p := residuePrime v
  let K := padicField v
  let T₀ := K.canonicalTopologicalData
  let := K.algebra
  let := T₀.topology
  let αF : K.Carrier ≃ₐ[Padic p] (padicFieldAt v (rfl : residuePrime v = p)).Carrier :=
    AlgEquiv.refl
  let π₀ : SmoothRep.{0, uF, uF} ℂ (GeneralLinear (r + 1) K.Carrier) :=
    SmoothRep.of (P.localComponent v).representation (P.localComponent v).isSmooth_canonical
  let π := π₀.universeLift.{uE}
  let eπ := π₀.universeLiftEquiv.{uE}
  have hπI : π.IsIrreducible := (isIrreducible_iff_of_equiv eπ).mp hSq.1
  have hπSq : T₀.IsSquareIntegrable π.representation :=
    (T₀.isSquareIntegrable_iff_of_equiv eπ).mp hSq.2
  have hAttachF : S.isoClass.HasPadicLocalComponent.{uF, uV, uF, max uF uE}
      v rfl K αF π := by
    refine ⟨S, P, rfl, ?_⟩
    let g := completionGroupEquiv K v rfl (r + 1) αF
    change Nonempty (Representation.Equiv ((P.localComponent v).representation.comp g.toMonoidHom)
      π.representation)
    have hg : g.toMonoidHom = MonoidHom.id (GeneralLinear (r + 1) K.Carrier) :=
      Matrix.GeneralLinearGroup.map_id
    simpa only [hg, MonoidHom.comp_id] using (show Nonempty (π₀.representation.Equiv π.representation)
      from ⟨eπ⟩)
  obtain ⟨s₀, hs₀⟩ := Aubert.SupportGrading.exists_isSupercuspidalSupport.{uF, uE} π hπI
  let s := s₀.map (supportLabel K)
  have hs : T₀.IsSupercuspidalSupport π (s.map (supercuspidalSupportDatum K)) := by
    simpa [s, Multiset.map_map, Function.comp_def, supportLabel_recovers] using hs₀
  have hSupportF : B.HasLocalSupercuspidalSupport.{uF, uV, uF, max uF uE} v rfl K αF s := by
    exact ⟨1, fun _ => PositiveRankCuspidalClass.ofFixedRank S.isoClass,
      by simp [B, IsobaricData.ofCuspidal], fun _ => π, fun _ => s, fun _ => hAttachF,
      fun _ => hs, (Fin.sum_univ_one (fun _ : Fin 1 => s)).symm⟩
  obtain ⟨ψ⟩ := padicUnitaryAdditiveCharacterExists K T₀
  have hπG := (attached_component_properties K v rfl αF π
    (IsobaricData.isUnitary_ofCuspidal.mp hB) hπI hAttachF ψ).2
  have hPrime : (Module.finrank F E).Prime := hDegree ▸ Nat.prime_two
  let : Fact (Module.finrank F E).Prime := ⟨hPrime⟩
  let : IsCyclic (E ≃ₐ[F] E) := isCyclic_of_prime_card (IsGalois.card_aut_eq_finrank F E)
  have hAbove (w : FinitePlacesAbove E v) :
      letI : w.1.asIdeal.LiesOver v.asIdeal := w.2
      D.HasLocalSupercuspidalSupport.{uE, uW, uF, max uF uE}
        w.1 (split_residuePrime_eq v w.1) K (splitPadicEquiv v w.1 hSplit) s := by
    let : w.1.asIdeal.LiesOver v.asIdeal := w.2
    exact hStrongSplit F E hPrime B D hB hD hWeak v w p rfl
      (split_residuePrime_eq v w.1) K αF (splitPadicEquiv v w.1 hSplit)
      (fun _ => rfl) s hSupportF
  have hRank : D.rank = r + 1 := hWeak.rank_eq.trans (IsobaricData.rank_ofCuspidal _)
  let w₀ := placeAbove E v
  let : w₀.1.asIdeal.LiesOver v.asIdeal := w₀.2
  have hCard := isobaric_card_eq_one_of_support K w₀.1 (split_residuePrime_eq v w₀.1)
    hRank hD (splitPadicEquiv v w₀.1 hSplit) (hAbove w₀) ψ π hs hπSq hπG
  obtain ⟨⟨m, c⟩, hc⟩ := Multiset.card_eq_one.mp hCard
  have hm : m = r := Nat.succ.inj <| by
    simpa [hc, PositiveRankCuspidalClass.rank, PositiveRankCuspidalClass.rankIndex] using hRank
  subst m
  have hSingleton : D = IsobaricData.ofCuspidal (PositiveRankCuspidalClass.ofFixedRank c) := hc
  have hUnitC : c.toOperatorClass.IsUnitarizable :=
    IsobaricData.isUnitary_ofCuspidal.mp (hSingleton ▸ hD)
  have hAtEach (w : FinitePlacesAbove E v) :
      letI : w.1.asIdeal.LiesOver v.asIdeal := w.2
      ∃ ρ : SmoothRep.{0, uF, max uF uE} ℂ (GeneralLinear (r + 1) K.Carrier),
        c.HasPadicLocalComponent.{uE, uW, uF, max uF uE} w.1
          (split_residuePrime_eq v w.1) K (splitPadicEquiv v w.1 hSplit) ρ ∧
        T₀.IsSupercuspidalSupport ρ (s.map (supercuspidalSupportDatum K)) := by
    let : w.1.asIdeal.LiesOver v.asIdeal := w.2
    exact singleton_support_component K w.1 (split_residuePrime_eq v w.1)
      (splitPadicEquiv v w.1 hSplit) (hSingleton ▸ hAbove w)
  obtain ⟨_, ⟨U, Q₀, hUc, _⟩, _⟩ := hAtEach w₀
  obtain ⟨R, hR⟩ := cuspidalAllLocalIrreduciblePresentationExistence E r U Q₀
  obtain ⟨Q, hQ⟩ : ∃ Q : CuspidalSpectralPresentation.{uE, uW} U,
      ∀ w, (Q.localComponent w).IsIrreducible ∧ (Q.localComponent w).IsAdmissible :=
    R.exists_small hR
  refine ⟨U, Q, hSingleton.trans (congrArg
    (IsobaricData.ofCuspidal ∘ PositiveRankCuspidalClass.ofFixedRank) hUc.symm), ?_⟩
  intro w
  let : w.1.asIdeal.LiesOver v.asIdeal := w.2
  let := (padicFieldAt w.1 (split_residuePrime_eq v w.1)).canonicalTopologicalData.topology
  obtain ⟨ρ, hAttachE, hρS⟩ := hAtEach w
  have hρI := irreducible_of_support K hρS
  have hρG := (attached_component_properties K w.1 (split_residuePrime_eq v w.1)
    (splitPadicEquiv v w.1 hSplit) ρ hUnitC hρI hAttachE ψ).2
  let eSupport := CuspidalSupport.fixedSupportDetectedEquiv T₀ ψ (Nat.succ_pos r) π ρ
    _ hs hρS ((Whittaker.hasFunctional_iff_nontrivial_topDerivative T₀ ψ _ π).mp hπG)
    ((Whittaker.hasFunctional_iff_nontrivial_topDerivative T₀ ψ _ ρ).mp hρG)
  obtain ⟨U', Q', hU'c, ⟨eρ⟩⟩ := hAttachE
  let g := completionGroupEquiv K w.1 (split_residuePrime_eq v w.1)
    (r + 1) (splitPadicEquiv v w.1 hSplit)
  have hQ'I : (Q'.localComponent w.1).IsIrreducible :=
    (isIrreducible_comp_continuousMulEquiv_iff _ g).mp ((isIrreducible_iff_of_equiv eρ).mpr hρI)
  obtain ⟨eU⟩ := (U'.isoClass_eq_iff U).mp (hU'c.trans hUc.symm)
  obtain ⟨eQ'⟩ := ((Q'.localComponent w.1).isoClass_eq_iff _).mp
    (Q'.transport_localComponent_isoClass eU w.1).symm
  obtain ⟨eQ⟩ := (Q'.transport eU).nonempty_localComponent_equiv Q w.1
    ((isIrreducible_iff_of_equiv eQ').mp hQ'I) (hQ w.1).1
  let e := eπ.trans (eSupport.trans (eρ.symm.trans (SmoothRep.pullbackEquiv g (eQ'.trans eQ))))
  exact ⟨LocalRealization.isSquareIntegrable_of_splitCompletion_equiv hSplit e hSq, ⟨e⟩⟩

end Langlands.Automorphic.Unramified
