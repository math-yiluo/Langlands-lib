import Langlands.BaseChange.CyclicNormLemma
import Langlands.BaseChange.SigmaLiftCharacterIdentity.Parameters
import Langlands.Global.PrincipalAdelesDiscreteProof
import Langlands.LinearAlgebra.MatrixSquarefreeCharpolyConjugacy
import Langlands.TraceFormula.TwistedEllipticClassFinitenessStatement

/-! # Finiteness of rational σ-elliptic classes meeting a compact adelic set -/

namespace Langlands.TraceFormula

open Langlands.BaseChange Langlands.Global Langlands.Global.AdelicGLTransport
open SigmaLiftCharacterIdentity (coefficients coefficients_baseChange coefficients_conj
  continuous_coefficients)

universe u v

section AdelicNorm

variable {K : Type u} {L : Type v} [Field K] [Field L] [NumberField L] [Algebra K L]

/-- Arithmetic transport on the adele ring preserves the integer scalars, so the ordered
cyclic norm applies to its action on adelic matrix units. -/
private noncomputable def adeleIntAut : (L ≃ₐ[K] L) →* (Adeles L ≃ₐ[ℤ] Adeles L) where
  toFun σ := (AdelicFunctoriality.adeleEquiv σ.toRingEquiv).toIntAlgEquiv
  map_one' := AlgEquiv.ext fun a => by
    change AdelicFunctoriality.adeleEquiv (RingEquiv.refl L) a = a
    rw [AdelicFunctoriality.adeleEquiv_refl, RingEquiv.refl_apply]
  map_mul' σ τ := AlgEquiv.ext fun a => by
    change AdelicFunctoriality.adeleEquiv (τ.toRingEquiv.trans σ.toRingEquiv) a =
      AdelicFunctoriality.adeleEquiv σ.toRingEquiv
        (AdelicFunctoriality.adeleEquiv τ.toRingEquiv a)
    rw [AdelicFunctoriality.adeleEquiv_trans, RingEquiv.trans_apply]

private theorem entrywiseAut_adeleIntAut (σ : L ≃ₐ[K] L) (n : ℕ) (g : AdelicGL L n) :
    entrywiseAut (adeleIntAut σ) n g = adelicEquiv n σ.toRingEquiv g :=
  Units.ext rfl

private theorem cyclicNorm_rational (σ : L ≃ₐ[K] L) (l n : ℕ) (δ : RationalGL L n) :
    cyclicNorm (adeleIntAut σ) l (AdelicGL.rational L n δ) =
      AdelicGL.rational L n (cyclicNorm σ l δ) := by
  induction l with
  | zero => simp
  | succ l ih =>
    rw [cyclicNorm_succ, cyclicNorm_succ, map_mul, ih, ← map_pow, entrywiseAut_adeleIntAut]
    exact congrArg (AdelicGL.rational L n (cyclicNorm σ l δ) * ·)
      (adelicEquiv_rational n (σ ^ l).toRingEquiv δ)

private theorem continuous_adelicNorm (σ : L ≃ₐ[K] L) (l n : ℕ) :
    Continuous (fun g : AdelicGL L n => cyclicNorm (adeleIntAut σ) l g) := by
  induction l with
  | zero => simp only [cyclicNorm_zero, continuous_const]
  | succ l ih =>
    simp only [cyclicNorm_succ, ← map_pow, entrywiseAut_adeleIntAut]
    exact ih.mul (adelicEquiv n (σ ^ l).toRingEquiv).continuous

end AdelicNorm

/-- A compact adelic set meets only finitely many rational σ-elliptic twisted classes. -/
theorem twistedEllipticClassFiniteness : TwistedEllipticClassFinitenessStatement.{u, v} := by
  classical
  intro K _ _ L _ _ _ σ l hσ n Ω hΩ meets
  let S : Set (RationalGL L n) := {δ | IsSigmaElliptic σ l δ ∧ meets δ}
  let values (δ : RationalGL L n) : Fin n → Adeles L :=
    coefficients (AdelicGL.rational L n (cyclicNorm σ l δ))
  have hdiag (δ : RationalGL L n) (i : Fin n) :
      values δ i = algebraMap L (Adeles L) (coefficients (cyclicNorm σ l δ) i) :=
    coefficients_baseChange (cyclicNorm σ l δ) i
  have hfinite : (values '' S).Finite := by
    let adelicValues (g : AdelicGL L n) := coefficients (cyclicNorm (adeleIntAut σ) l g)
    have hcompact : IsCompact (adelicValues '' Ω) :=
      hΩ.image (continuous_coefficients.comp (continuous_adelicNorm σ l n))
    let includeCoefficients : (Fin n → principalAdeles L) → (Fin n → Adeles L) :=
      fun a i => (a i).val
    have hembedding : Topology.IsClosedEmbedding includeCoefficients :=
      Topology.IsClosedEmbedding.piMap
        (fun _ => (principalAdeles_isClosed L).isClosedEmbedding_subtypeVal)
    let : DiscreteTopology (principalAdeles L) := principalAdeles_discreteTopology L
    have hprincipal : (includeCoefficients ⁻¹' (adelicValues '' Ω)).Finite :=
      (hembedding.isCompact_preimage hcompact).finite_of_discrete
    refine (hprincipal.image includeCoefficients).subset ?_
    rintro _ ⟨δ, hδ, rfl⟩
    obtain ⟨x, hx⟩ := hδ.2
    let a : Fin n → principalAdeles L :=
      fun i => ⟨values δ i, ⟨coefficients (cyclicNorm σ l δ) i, (hdiag δ i).symm⟩⟩
    refine ⟨a, ?_, rfl⟩
    change values δ ∈ adelicValues '' Ω
    refine ⟨_, hx, ?_⟩
    have hpow : adeleIntAut σ ^ l = 1 := by rw [← map_pow, hσ.pow_eq_one, map_one]
    change coefficients (cyclicNorm (adeleIntAut σ) l
      (x⁻¹ * AdelicGL.rational L n δ * adelicEquiv n σ.toRingEquiv x)) = values δ
    rw [← entrywiseAut_adeleIntAut, cyclicNorm_twistedConj, hpow, entrywiseAut_one_apply,
      cyclicNorm_rational, coefficients_conj]
  obtain ⟨T, hTS, hT, hcover⟩ :=
    (Set.exists_subset_image_finite_and (f := values) (s := S)
      (p := fun t => values '' S ⊆ t)).mp ⟨_, subset_rfl, hfinite, subset_rfl⟩
  refine ⟨hT.toFinset, fun r hr => hTS (hT.mem_toFinset.mp hr), ?_⟩
  intro δ hδ hmeets
  have hmem : δ ∈ S := ⟨hδ, hmeets⟩
  obtain ⟨r, hr, heq⟩ := hcover (Set.mem_image_of_mem values hmem)
  refine ⟨r, hT.mem_toFinset.mpr hr, ?_⟩
  apply (cyclicNormLemma K L σ l n hσ).2.2
  have hcharpoly : (cyclicNorm σ l δ).val.charpoly = (cyclicNorm σ l r).val.charpoly := by
    apply HarmonicAnalysis.Distribution.charpoly_eq_of_coeff_eq
    intro i
    apply NumberField.AdeleRing.algebraMap_injective (NumberField.RingOfIntegers L) L
    have hi := congrFun heq.symm i
    rwa [hdiag, hdiag] at hi
  obtain ⟨γ, ⟨a, ha⟩, hγ⟩ := hδ
  have hreg := isRegularSemisimple_baseChange (E := L) hγ.1
  rw [← ha] at hreg
  have hsep := (isRegularSemisimple_conj_iff a _).mp hreg
  obtain ⟨g, hg⟩ :=
    matrixConj_of_squarefree_charpoly_eq _ _ (Polynomial.Separable.squarefree hsep) hcharpoly
  exact ⟨g⁻¹, by simpa only [inv_inv] using Units.ext hg⟩

end Langlands.TraceFormula
