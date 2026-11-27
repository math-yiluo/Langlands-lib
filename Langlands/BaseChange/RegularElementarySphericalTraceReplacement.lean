import Langlands.BaseChange.CommonShintaniLiftNonvanishing
import Langlands.BaseChange.RegularElementaryNormalizedJacquet
import Langlands.BaseChange.SphericalTraceReplacementOfJacquetData
import Langlands.BaseChange.UnramifiedGenericSigmaNormalizationStatement
import Langlands.BaseChange.UnramifiedJacquetDetection
import Langlands.Representation.Classification.JuxtaposedJacquetImage
import Langlands.Representation.Unramified.HeckeComparisonProof
import Langlands.Representation.Unramified.SphericalHeckeSpectrumExistenceProof

/-! # Spherical replacement for finite sums of generic local distributions -/

noncomputable section

namespace Langlands.BaseChange

open Correspondence HarmonicAnalysis Unramified GeneralLinear.BlockShape
open scoped BigOperators

universe u v uV uW uI uJ

attribute [local instance] heckeFieldTopology heckeFieldValuativeRel heckeFieldLocalField
  heckeGeneralLinearTopology heckeGeneralLinearTopologicalGroup heckeGeneralLinearT2
  heckeGeneralLinearMeasurable heckeGeneralLinearBorel

private local instance {p : ℕ} [Fact p.Prime] (F : PadicField p) (n : ℕ) :
    LocallyCompactSpace (GeneralLinear n F.Carrier) :=
  F.canonicalGeneralLinearLocallyCompactSpace n

private local instance {p : ℕ} [Fact p.Prime] (F : PadicField p) (n : ℕ) :
    TotallyDisconnectedSpace (GeneralLinear n F.Carrier) :=
  LocalFieldTopology.generalLinear_totallyDisconnectedSpace F.Carrier n

section LocalData

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{u} p) {r : ℕ}

set_option backward.isDefEq.respectTransparency false in
private theorem borelIntegralDiagonal_eq_normOneLevi :
    borelIntegralDiagonal F r = F.canonicalTopologicalData.normOneLevi (borelShape r) := by
  let D := F.canonicalTopologicalData
  ext m
  obtain ⟨a, ha⟩ := (mem_singletonLevi_iff_diagonalUnits F _).mp ⟨m, rfl⟩
  have hm : m = singletonLevi F.Carrier a :=
    (borelShape r).leviEmbedding_injective F.Carrier
      (ha.trans (leviEmbedding_singletonLevi_eq_diagonalUnits F a).symm)
  rw [hm, singletonLevi_mem_borelIntegralDiagonal_iff F a, D.mem_normOneLevi]
  apply forall_congr'
  intro i
  change D.ord (a i : F.Carrier) = 0 ↔
    D.determinantNorm 1 (GeneralLinear.scalar (n := 1) (a i)) = 1
  rw [D.determinantNorm_scalar, pow_one]
  change a i ∈ D.ordUnits.ker ↔ a i ∈ D.normalizedAbsUnits.ker
  rw [D.ker_ordUnits]

private theorem exists_inducing_tuple_or_fixed_zero
    (P : AutomorphicObject.{u, uV} F r.succPNat) :
    ∃ z : Fin (r + 1) → ℂˣ,
      IsSubquotientOf (principalSeriesOfTuple F z) P.obj.representation ∨
        (borelJacquetIntegralFixed F P.obj.representation = ⊥ ∧
          fixedVectors P.obj.representation (sphericalSubgroup F r) = ⊥) := by
  by_cases hS : fixedVectors P.obj.representation (sphericalSubgroup F r) = ⊥
  · by_cases hJ : borelJacquetIntegralFixed F P.obj.representation = ⊥
    · exact ⟨fun _ => 1, Or.inr ⟨hJ, hS⟩⟩
    have hW : fixedVectors (F.canonicalNormalizedJacquet (borelShape r) P.obj.representation)
        (F.canonicalTopologicalData.normOneLevi (borelShape r)) =
        borelJacquetIntegralFixed F P.obj.representation := by
      rw [← borelIntegralDiagonal_eq_normOneLevi F]
      rfl
    have hFin := finiteDimensional_borelJacquetIntegralFixed F P.obj.representation P.property.2
    have hNT := Submodule.nontrivial_iff_ne_bot.mpr hJ
    obtain ⟨z, j, hj⟩ := unramifiedJacquetDetection p F r P (hW.symm ▸ hFin) (hW.symm ▸ hNT)
    let e := Classification.JuxtaposedShuffle.rangeEquivOfInjective j hj
    exact ⟨z, Or.inl ⟨j.range, e.symm.toIntertwiningMap, e.symm.toLinearEquiv.surjective⟩⟩
  · obtain ⟨s, hs⟩ := sphericalHeckeSpectrumExistence p F r P hS
    obtain ⟨z, _, hP⟩ := (sphericalHeckeComparison F r P s).mpr hs
    exact ⟨z, Or.inl hP.2⟩

private theorem borelJacquetMultiset_eq_zero_of_fixed_eq_bot
    (P : AutomorphicObject.{u, uV} F r.succPNat)
    (hJ : borelJacquetIntegralFixed F P.obj.representation = ⊥) :
    borelJacquetMultiset F P.obj.representation = 0 := by
  classical
  let : Subsingleton (borelJacquetIntegralFixed F P.obj.representation) :=
    Submodule.subsingleton_iff_eq_bot.mpr hJ
  apply Multiset.ext.mpr
  intro z
  rw [Multiset.count_zero, count_borelJacquetMultiset_automorphicObject]
  exact Module.finrank_zero_of_subsingleton

set_option backward.isDefEq.respectTransparency false in
private theorem family_weyl_support_and_spectra
    (hWeyl : UnramifiedWeylJacquetSupportStatement.{u, uV}) {I : Type*}
    (P : I → AutomorphicObject.{u, uV} F r.succPNat) (z : I → Fin (r + 1) → ℂˣ)
    (ψ : I → NontrivialAdditiveCharacter F) (hGen : ∀ i, Whittaker.IsGeneric (ψ i) r (P i).obj.representation)
    (hData : ∀ i, IsSubquotientOf (principalSeriesOfTuple F (z i)) (P i).obj.representation ∨
        (borelJacquetIntegralFixed F (P i).obj.representation = ⊥ ∧
          fixedVectors (P i).obj.representation (sphericalSubgroup F r) = ⊥)) :
    let spherical i := fixedVectors (P i).obj.representation (sphericalSubgroup F r) ≠ ⊥
    (∀ i, spherical i → HasSphericalHeckeSpectrum F (P i) (Eigenvalues.ofTuple (z i))) ∧
      HasWeylJacquetSupport z spherical (fun i => borelJacquetMultiset F (P i).obj.representation) := by
  intro spherical
  constructor
  · intro i hi
    rcases hData i with h | ⟨_, h⟩
    · exact hasSphericalHeckeSpectrum_of_isSphericalConstituent F ⟨hi, h⟩
    · exact (hi h).elim
  · intro i
    rcases hData i with h | ⟨hJ, hS⟩
    · obtain ⟨hle, hgen⟩ := (hWeyl p F r (z i)).2 (P i) h
      obtain ⟨hsph, hnon⟩ := hgen (ψ i) (hGen i)
      exact ⟨hle, hsph, fun h => hnon (not_ne_iff.mp h)⟩
    · dsimp only
      rw [borelJacquetMultiset_eq_zero_of_fixed_eq_bot F (P i) hJ]
      exact ⟨Multiset.zero_le _, fun h => (h hS).elim, by simp⟩

end LocalData

set_option backward.isDefEq.respectTransparency false in
/-- Equality on the regular elementary pairs implies equality on all spherical
base-change pairs in finite weighted sums of generic local distributions. -/
def RegularElementarySphericalTraceReplacementStatement : Prop :=
  RegularElementaryJacquetTraceStatement.{u, uW} →
  RegularElementaryJacquetTraceStatement.{v, uV} →
  UnramifiedWeylJacquetSupportStatement.{u, uW} →
  UnramifiedWeylJacquetSupportStatement.{v, uV} →
  UnramifiedGenericSigmaNormalizationStatement.{u, v, uV} →
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{u} p) (E : PadicField.{v} p)
    [Algebra F.Carrier E.Carrier] [IsScalarTower (Padic p) F.Carrier E.Carrier]
    (σ : E.Carrier ≃ₐ[F.Carrier] E.Carrier) (l r : ℕ) (hcyc : IsCyclicAlgebra σ l)
    (he : E.canonicalTopologicalData.ramificationIndex =
      F.canonicalTopologicalData.ramificationIndex)
    (b : SphericalHeckeAlgebra E r →ₐ[ℂ] SphericalHeckeAlgebra F r),
    IsUnramifiedBaseChangeHom F E l r b →
    ∀ (I : Type uI) (J : Type uJ) [Fintype I] [Fintype J]
      (upper : I → AutomorphicObject.{v,uV} E r.succPNat)
      (lower : J → AutomorphicObject.{u,uW} F r.succPNat)
      (A : ∀ i, SigmaIntertwiner σ (r + 1) (upper i).obj.representation),
    (∀ i, ∃ ψ : NontrivialAdditiveCharacter E, Whittaker.IsGeneric ψ r (upper i).obj.representation) →
    (∀ j, ∃ ψ : NontrivialAdditiveCharacter F, Whittaker.IsGeneric ψ r (lower j).obj.representation) →
    let distE i := twistedDistribution (sphericalHaar E r) (upper i).obj.representation
      (upper i).property.2 (A i).toLinearMap
    let distF j := Character.distribution (sphericalHaar F r) (lower j).obj.representation
      (lower j).property.2
    let tests (w : StrictWeight (r + 1)) :=
      regularElementaryBaseChangeTests F E σ l hcyc he w.val w.property
    ∀ (a : I → ℂ) (c : J → ℂ),
      (∀ w, ∑ i, a i * distE i (tests w).1 = ∑ j, c j * distF j (tests w).2) →
      ∀ φ : SphericalHeckeAlgebra E r,
        ∑ i, a i * distE i φ.val = ∑ j, c j * distF j (b φ).val

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1400000 in
theorem regularElementarySphericalTraceReplacement :
    RegularElementarySphericalTraceReplacementStatement.{u, v, uV, uW, uI, uJ} := by
  classical
  intro hTraceF hTraceE hWeylF hWeylE hSigma p _ F E _ _ σ l r hcyc he b hb
    I J _ _ upper lower A hGenE hGenF distE distF tests a c heq φ
  choose zE hzE using fun i => exists_inducing_tuple_or_fixed_zero E (upper i)
  choose zF hzF using fun j => exists_inducing_tuple_or_fixed_zero F (lower j)
  choose ψE hψE using hGenE
  choose ψF hψF using hGenF
  obtain ⟨hsE, hwE⟩ := family_weyl_support_and_spectra E hWeylE upper zE ψE hψE hzE
  obtain ⟨hsF, hwF⟩ := family_weyl_support_and_spectra F hWeylF lower zF ψF hψF hzF
  have hA (i : I) :
      ∃ A' : SigmaIntertwiner σ (r + 1) (upper i).obj.representation,
        (∀ x : borelJacquetFixed E (upper i).obj.representation,
          jacquetSigmaIntertwiner σ (borelShape r) A' x.val = x.val) ∧
        ∀ x : fixedVectors (upper i).obj.representation (sphericalSubgroup E r), A' x.val = x.val := by
    let ρ := (upper i).obj.representation
    rcases hzE i with hsub | ⟨hJ, hK⟩
    · obtain ⟨A', hA', hSph⟩ := hSigma p F E σ l r hcyc he (zE i) _ ρ (ψE i) (hψE i) hsub
      refine ⟨A', fun x => ?_, fun x => hSph x.val x.property⟩
      obtain ⟨y, hy⟩ := (borelShape r).jacquetMk_surjective ρ x.val
      rw [← hy, hA' y]
    · refine ⟨A i, fun x => ?_, fun x => ?_⟩
      · have hx : x.val = 0 := (Submodule.mem_bot ℂ).mp
          ((borelJacquetNormalization p E r _ ρ).trans hJ ▸ x.property)
        rw [hx, map_zero]
      · have hx : x.val = 0 := (Submodule.mem_bot ℂ).mp (hK ▸ x.property)
        rw [hx, map_zero]
  choose A' hAJ hAK using hA
  choose d hd using fun i =>
    (A' i).exists_smul_toLinearMap (A i) (upper i).property.2 (upper i).property.1
  let distE' i := twistedDistribution (sphericalHaar E r) (upper i).obj.representation
    (upper i).property.2 (A' i).toLinearMap
  have hDist (i : I) (f : SchwartzBruhat (GeneralLinear (r + 1) E.Carrier)) :
      distE i f = d i * distE' i f := by
    simp only [distE, distE', (hd i).2, twistedDistribution_smul, LinearMap.smul_apply, smul_eq_mul]
  obtain ⟨hFactor, hUpper, hLower⟩ :=
    regularElementaryNormalizedJacquet hTraceF hTraceE p F E σ l r hcyc he
  let factor (w : StrictWeight (r + 1)) := regularElementaryNormalizedFactor E w.val
  let exponentsE i := borelJacquetMultiset E (upper i).obj.representation
  let exponentsF j := borelJacquetMultiset F (lower j).obj.representation
  have hExpE : HasJacquetElementaryTraceExpansion 1 exponentsE factor (fun i w => distE' i (tests w).1) :=
    fun i => hUpper _ _ (upper i).property.2 (upper i).property.1 (A' i) (hAJ i)
  have hExpF : HasJacquetElementaryTraceExpansion l exponentsF factor (fun j w => distF j (tests w).2) :=
    fun j => hLower _ _ (lower j).property.2 (lower j).property.1
  simp_rw [hDist, ← mul_assoc] at heq ⊢
  exact sphericalTraceReplacementOfJacquetData p F E σ l r hcyc he b hb I J upper lower A' zE zF
    exponentsE exponentsF factor hAK hsE hsF hwE hwF hFactor hExpE hExpF
    (fun i => a i * d i) c heq φ

end Langlands.BaseChange
