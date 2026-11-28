import Langlands.Automorphic.AssociatedCentralCharacter.GoodPlaces
import Langlands.Automorphic.CentralCharacterTopCoefficient
import Langlands.Automorphic.Unramified.WeakTransfer
import Langlands.Global.Factors.HeckeFiniteRamification
import Langlands.Global.FiniteAdelicGL.SphericalArithmeticTransport
import Langlands.Global.HeckeCharacterUnramifiedNorm

/-! # Central characters under arithmetic weak base change -/

noncomputable section

universe u uV uW

set_option autoImplicit false

open scoped NumberField

namespace Langlands.Global.HeckeCharacter

open NumberField Langlands.Global.AdelicFunctoriality

variable {F E : Type u} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

/-- At an unramified place, norm pullback raises the canonical uniformizer value of an
unramified Hecke character to the residue degree. -/
theorem normComp_finiteUniformizerValue (ω : HeckeCharacter F) (v : FinitePlace F)
    (w : FinitePlacesAbove E v) (he : w.1.asIdeal.ramificationIdx (𝓞 F) = 1)
    (hω : ω.IsUnramifiedAt v) :
    (ω.normComp (L := E)).finiteUniformizerValue w.1 =
      ω.finiteUniformizerValue v ^ w.1.asIdeal.inertiaDeg (𝓞 F) :=
  normComp_finiteComponent_uniformizer ω v w he hω _
    (FiniteAdelicGL.completion_uniformizer_value w.1) _
    (FiniteAdelicGL.completion_uniformizer_value v)

end Langlands.Global.HeckeCharacter

namespace Langlands.Automorphic.CuspidalOperatorRealization

open NumberField Langlands.Global Langlands.Global.AdelicFunctoriality Langlands.Unramified

private theorem topCoefficient_power {n : ℕ} (s : Eigenvalues n) (d : ℕ) :
    elementaryCoefficient (s.power d) n = elementaryCoefficient s n ^ d := by
  rw [elementaryCoefficient_rank, elementaryCoefficient_rank, Eigenvalues.power, Sym.coe_map]
  have h := Multiset.prod_map_pow (m := (s : Multiset ℂˣ)) (f := id) (n := d)
  rw [Multiset.map_id] at h
  simp only [id_eq] at h
  rw [h, Units.val_pow_eq_pow_val]

section Realizations

variable {F E : Type u} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  [CompactSpace (AdeleQuotient F)] [CompactSpace (AdeleQuotient E)] {r : ℕ}

/-- The central character of a cuspidal arithmetic weak base change is the norm pullback
of the central character of the lower realization. -/
theorem hasCentralCharacter_normComp_of_isWeakBaseChangeOf
    {S : CuspidalOperatorRealization F r} {T : CuspidalOperatorRealization E r}
    {ω : HeckeCharacter F} (hω : S.HasCentralCharacter ω)
    (hbase : IsoClass.IsWeakBaseChangeOf.{u, u, uV, uW} T.isoClass S.isoClass) :
    T.HasCentralCharacter (ω.normComp (L := E)) := by
  obtain ⟨P, Q, hPQ⟩ := (IsoClass.isWeakBaseChangeOf_isoClass_iff.{u, u, uV, uW} T S).mp hbase
  obtain ⟨A, hA⟩ := HeckeFunctionalEquation.exists_finset_isUnramifiedAt F ω
  apply T.hasCentralCharacter_of_eventually_elementaryCoefficient Q
  have hgood := (AdelicFunctoriality.tendsto_under_cofinite (K := F) (L := E)).eventually
    (hPQ.and A.eventually_cofinite_notMem)
  filter_upwards [hgood] with q hq
  let v := q.under (𝓞 F)
  let w : FinitePlacesAbove E v := ⟨q, AdelicFunctoriality.liesOver_under q⟩
  obtain ⟨⟨hP, hQ, he, hpow⟩, hvA⟩ := hq
  have hωv := hA v hvA
  refine ⟨HeckeCharacter.normComp_isUnramifiedAt ω v hωv w, hQ w, ?_⟩
  rw [HeckeCharacter.normComp_finiteUniformizerValue ω v w (he w) hωv,
    Units.val_pow_eq_pow_val, finiteUniformizerValue_eq_elementaryCoefficient v hω P hP,
    hpow w, topCoefficient_power]

end Realizations

/-- Central-character compatibility for actual cuspidal arithmetic weak base change. -/
def WeakBaseChangeCentralCharacterStatement : Prop :=
  ∀ (F E : Type u) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    [CompactSpace (AdeleQuotient F)] [CompactSpace (AdeleQuotient E)]
    (r : ℕ) (S : CuspidalOperatorRealization F r) (T : CuspidalOperatorRealization E r)
    (ω : HeckeCharacter F),
    S.HasCentralCharacter ω → IsoClass.IsWeakBaseChangeOf.{u, u, uV, uW} T.isoClass S.isoClass →
      T.HasCentralCharacter (ω.normComp (L := E))

/-- The cofinite Satake comparison determines the upper central character. -/
theorem weakBaseChangeCentralCharacter : WeakBaseChangeCentralCharacterStatement.{u, uV, uW} :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ hω hbase =>
    hasCentralCharacter_normComp_of_isWeakBaseChangeOf hω hbase

end Langlands.Automorphic.CuspidalOperatorRealization
