import Langlands.Automorphic.AssociatedCentralCharacter.GoodPlaces
import Langlands.Automorphic.IrreducibleCentralCharacterProof
import Langlands.Automorphic.OperatorScalarCentralCharacter
import Langlands.Global.AdelicFunctoriality.LocalDegree
import Langlands.Global.Arithmetic.HarrisProposition48SingletonDescentStatement
import Langlands.Global.Factors.HeckeFiniteRamification

/-! # Unitary central characters descend under arithmetic weak base change -/

noncomputable section

universe uF uE uV uW

set_option autoImplicit false

open scoped NumberField

namespace Langlands.Global.Harris

open Langlands.Automorphic Langlands.Unramified AdelicFunctoriality

section TopCoefficient

variable {F : Type uF} [Field F] [NumberField F]

private local instance (n : ℕ) : AddCommGroup (RationalInvariantFunctions F n) := Submodule.addCommGroup _
private local instance (n : ℕ) : AddCommGroup (ContinuousRationalFunctions F n) := Submodule.addCommGroup _
private local instance (n : ℕ) : AddCommGroup (FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _
private local instance (n : ℕ) : AddCommGroup (AutomorphicForms F n) := Submodule.addCommGroup _
private local instance (n : ℕ) : AddCommGroup (StableAutomorphicFunctions F n) := Submodule.addCommGroup _
private local instance {n : ℕ} (S : OperatorRealization F n) : AddCommGroup S.Space :=
  Submodule.addCommGroup _

/-- Compare the central scalar and the top spherical Hecke scalar on a nonzero vector. -/
private theorem finiteUniformizerValue_eq_satakeProduct [CompactSpace (AdeleQuotient F)]
    {r : ℕ} {S : CuspidalOperatorRealization F r} {ω : HeckeCharacter F}
    (hω : S.HasCentralCharacter ω) (P : CuspidalSpectralPresentation.{uF, uV} S)
    (v : FinitePlace F) (hv : v ∉ P.exceptional) :
    ω.finiteUniformizerValue v = (P.spectralSystem.eigenvalues v hv : Multiset ℂˣ).prod := by
  let π := (CompletionPadic.padicField v).canonicalTopologicalData.uniformizerUnit
  have hz : finiteIdeleInclusion F v π ∈ S.realization.centralCharacterSubgroup ω :=
    (S.realization.mem_centralCharacterSubgroup ω _).mpr
      (fun b x => S.realization.centralCharacter_evaluate ω hω b _ x)
  obtain ⟨b, hb⟩ := P.exists_spherical_ne_zero v hv
  have hb₀ : (b : S.realization.Space) ≠ 0 := fun h => hb (Subtype.ext h)
  have hωb := (S.realization.finiteIdeleInclusion_mem_centralCharacterSubgroup_iff ω v π).mp hz
    (b : S.realization.Space)
  have hcorner := congrArg Subtype.val (P.corner_eq_smul v hv b (Fin.last (r + 1)))
  have htop := standardHecke_cornerAction_last (CompletionPadic.padicField v)
    (S.realization.localRepresentation v)
    (S.realization.localRepresentation_isSmooth_canonical v) b
  have hdiag := standardDiagonal_last (CompletionPadic.padicField v) (r := r)
  have hs := standardHeckeScalar_last (CompletionPadic.padicField v) (P.spectralSystem.eigenvalues v hv)
  apply Units.ext
  refine smul_left_injective ℂ hb₀ ?_
  have hscalar := congrArg
    (fun g => S.realization.localRepresentation v g (b : S.realization.Space)) hdiag
  calc
    (ω.finiteUniformizerValue v : ℂ) • (b : S.realization.Space) = _ := hωb.symm
    _ = _ := hscalar.symm
    _ = _ := htop.symm
    _ = _ := hcorner
    _ = _ := Submodule.coe_smul _ b
    _ = _ := congrArg (fun c : ℂ => c • (b : S.realization.Space))
      (hs.trans (elementaryCoefficient_rank _))

end TopCoefficient

/-- Local unitarity on the unramified components at cofinitely many places suffices,
by closed-subgroup density on the full idele group. -/
private theorem isUnitary_of_cofinite_uniformizer {F : Type uF} [Field F] [NumberField F]
    (ω : HeckeCharacter F)
    (h : ∀ᶠ v in Filter.cofinite, ω.IsUnramifiedAt v ∧ ‖(ω.finiteUniformizerValue v : ℂ)‖ = 1) :
    ω.IsUnitary := by
  let H : Subgroup (Ideles F) := {
    carrier := {z | ‖(ω.onIdeles z : ℂ)‖ = 1}
    one_mem' := by simp
    mul_mem' := by
      intro a b ha hb
      simp only [Set.mem_ofPred_eq] at ha hb ⊢
      rw [map_mul, Units.val_mul, norm_mul, ha, hb, one_mul]
    inv_mem' := by
      intro a ha
      simp only [Set.mem_ofPred_eq] at ha ⊢
      rw [map_inv, Units.val_inv_eq_inv_val, norm_inv, ha, inv_one] }
  have hclosed : IsClosed (H : Set (Ideles F)) :=
    isClosed_eq (Units.continuous_val.comp ω.onIdeles.continuous).norm continuous_const
  have hfin := Filter.eventually_cofinite.mp h
  have htop : H = ⊤ := by
    refine IdeleDensity.eq_top_of_isClosed H hfin.toFinset hclosed ?_ ?_
    · intro a
      change ‖(ω.onIdeles (diagonalUnits F a) : ℂ)‖ = 1
      simp
    · intro v hv a
      have hgood : ω.IsUnramifiedAt v ∧ ‖(ω.finiteUniformizerValue v : ℂ)‖ = 1 := by
        by_contra hc
        exact hv (hfin.mem_toFinset.mpr hc)
      let G := H.comap (finiteIdeleInclusion F v).toMonoidHom
      have hG : G = ⊤ := by
        refine CompletionPadic.subgroup_eq_top_of_uniformizer_mem F v G ?_ hgood.2
        intro u hu
        change ‖(ω.finiteComponent v u : ℂ)‖ = 1
        rw [hgood.1 u hu, Units.val_one, norm_one]
      exact (hG ▸ Subgroup.mem_top a : a ∈ G)
  intro x
  obtain ⟨z, rfl⟩ := QuotientGroup.mk'_surjective (principalIdeles F) x
  exact (htop ▸ Subgroup.mem_top z : z ∈ H)

/-- For actual cuspidal realizations, a unitary central character upstairs forces
unitarity downstairs under the cofinite Satake power comparison. -/
theorem weakBaseChangeUnitaryCentralCharacter :
    WeakBaseChangeUnitaryCentralCharacterStatement.{uF, uE, uV, uW} := by
  intro F E _ _ _ _ _ _ _ r S T hT hbase
  obtain ⟨ξ, hξunit, hξ⟩ := hT
  obtain ⟨ω, hω, -⟩ := S.realization.existsUnique_hasCentralCharacter S.irreducible
  obtain ⟨P, Q, hPQ⟩ :=
    (CuspidalOperatorRealization.IsoClass.isWeakBaseChangeOf_isoClass_iff.{uF, uE, uV, uW}
      T S).mp hbase
  refine ⟨ω, isUnitary_of_cofinite_uniformizer ω ?_, hω⟩
  obtain ⟨A, hA⟩ := HeckeFunctionalEquation.exists_finset_isUnramifiedAt F ω
  filter_upwards [hPQ, A.eventually_cofinite_notMem] with v hv hvA
  obtain ⟨hP, hQ, _, hpow⟩ := hv
  let w := placeAbove E v
  let f := w.1.asIdeal.inertiaDeg (𝓞 F)
  have hf : f ≠ 0 := (w.1.asIdeal.inertiaDeg_pos (𝓞 F)).ne'
  have hprod : HeckeCharacter.finiteUniformizerValue ξ w.1 =
      HeckeCharacter.finiteUniformizerValue ω v ^ f := by
    rw [finiteUniformizerValue_eq_satakeProduct hξ Q w.1 (hQ w),
      finiteUniformizerValue_eq_satakeProduct hω P v hP, hpow w, Eigenvalues.power, Sym.coe_map]
    have hm := Multiset.prod_map_pow (m := (P.spectralSystem.eigenvalues v hP : Multiset ℂˣ))
      (f := id) (n := f)
    rw [Multiset.map_id] at hm
    exact hm
  have hup : ‖(HeckeCharacter.finiteUniformizerValue ξ w.1 : ℂ)‖ = 1 := hξunit _
  rw [hprod, Units.val_pow_eq_pow_val, norm_pow] at hup
  refine ⟨hA v hvA, (pow_left_inj₀ (norm_nonneg _) zero_le_one hf).mp ?_⟩
  simpa only [one_pow] using hup

end Langlands.Global.Harris
