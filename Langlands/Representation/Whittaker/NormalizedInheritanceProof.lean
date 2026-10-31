import Langlands.Representation.Whittaker.NormalizedInheritanceStatement
import Langlands.Representation.Whittaker.InducedWhittakerTypeProof
import Langlands.Representation.Whittaker.MultiplicityOneProof
import Langlands.Representation.Whittaker.EntrywiseCharacter
import Langlands.Representation.Whittaker.Transport
import Langlands.Representation.Induction.BlockCharacterAbsorption
import Langlands.Representation.RankinSelberg.WhittakerTypeTwist
import Langlands.LocalField.Normalization.Proof
import Langlands.LocalField.CanonicalProof

/-! # Nonzero Whittaker inheritance under normalized upper block induction -/

noncomputable section
namespace Langlands.Whittaker
open GeneralLinear HarmonicAnalysis
universe uF uV
variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

private theorem genericFactorData :
    letI := T.topology
    ∀ (d : ℕ) (σ : SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear d F.Carrier))
      (ψ : UnitaryAdditiveCharacter F.Carrier),
      (∃ (m : ℕ) (h : d = m + 1), IsGeneric ψ m (h ▸ σ).representation) →
      IsAdmissible σ.representation ∧
      Module.Finite (MonoidAlgebra ℂ (GeneralLinear d F.Carrier)) σ.representation.asModule ∧
      ∃ ℓ : functionals (upperUnipotent d F.Carrier) (entrywiseCharacter ψ.complex d)
          σ.representation,
        ℓ.val ≠ 0 ∧ ∀ ℓ', ∃ c : ℂ, ℓ' = c • ℓ := by
  have ht := T.topology_eq_canonicalNormTopology
  rcases T with ⟨t, v, ve, mt, lf⟩
  dsimp only at ht
  cases ht
  rename_i v ve mt lf
  let T : F.TopologicalData :=
    { topology := F.canonicalNormedField.toUniformSpace.toTopologicalSpace
      valuativeRel := v
      valuativeExtension := ve
      moduleTopology := mt
      localField := lf }
  let := T.topology
  intro d σ ψ hg
  obtain ⟨m, h, hg⟩ := hg
  subst d
  obtain ⟨hirr, hadm, ℓ, hℓ⟩ := hg
  let := hirr
  have hm := multiplicityOne.{uF, max uF uV} p inferInstance F
  refine ⟨hadm, inferInstance, ?_⟩
  rw [entrywiseCharacter_eq_standardCharacter]
  refine ⟨ℓ, hℓ, ?_⟩
  intro ℓ'
  exact (hm m σ ψ σ.representation hadm hirr ℓ ℓ' hℓ).exists

/-- Generic block factors yield a nonzero standard Whittaker functional on their
actual normalized upper block induction, for every compatible field topology. -/
theorem normalizedInheritance :
    NormalizedInheritanceStatement.{uF,uV} F T := by
  have ht := T.topology_eq_canonicalNormTopology
  rcases T with ⟨t, v, ve, mt, lf⟩
  dsimp only at ht
  cases ht
  rename_i v ve mt lf
  let T : F.TopologicalData :=
    { topology := F.canonicalNormedField.toUniformSpace.toTopologicalSpace
      valuativeRel := v
      valuativeExtension := ve
      moduleTopology := mt
      localField := lf }
  let := T.topology
  intro n B σ ψ hg
  let := T.generalLinearTopologicalGroup (n + 1)
  let ρ := fun i => (σ i).representation
  let τ := T.blockHalfTwist B ρ
  have hfactor := fun i => genericFactorData F T (B.size i) (σ i) ψ (hg i)
  have hadm : ∀ i, IsAdmissible (τ i) := fun i =>
    (T.isAdmissible_blockHalfTwist_iff B ρ i).mpr (hfactor i).1
  have hfinite : ∀ i, Module.Finite
      (MonoidAlgebra ℂ (GeneralLinear (B.size i) F.Carrier)) (τ i).asModule := fun i =>
    (finite_asModule_twist_iff _ _).mpr (hfactor i).2.1
  have hspan : ∀ i, ∃ ℓ : functionals (upperUnipotent (B.size i) F.Carrier)
      (entrywiseCharacter ψ.complex (B.size i)) (τ i),
      ℓ.val ≠ 0 ∧ ∀ ℓ', ∃ c : ℂ, ℓ' = c • ℓ := by
    intro i
    dsimp only [τ, PadicField.TopologicalData.blockHalfTwist]
    obtain ⟨ℓ, hℓ, hspan⟩ := (hfactor i).2.2
    let e := twistFunctionalEquiv _ (entrywiseCharacter ψ.complex (B.size i))
      (T.blockHalfModulus B i)
      (T.blockHalfModulus_upperUnipotent B i) (ρ i)
    refine ⟨e ℓ, hℓ, ?_⟩
    intro ℓ'
    obtain ⟨c, hc⟩ := hspan (e.symm ℓ')
    have he := congrArg e hc
    rw [e.apply_symm_apply, e.map_smul] at he
    exact ⟨c, he⟩
  have hne : ψ.complex ≠ 1 := by
    intro he
    apply ψ.nontrivial
    ext x
    exact congrArg (fun f : AddChar F.Carrier ℂ => f x) he
  have hr := Langlands.inducedWhittakerType.{uF, max uF uV} p inferInstance F
  have hind := (hr n B (fun i => σ i) τ ψ.complex ψ.continuous_complex hne
    ψ.norm_complex hadm hfinite).mpr
  have hblocks : ∀ i, ∃ ℓ : Module.Dual ℂ (σ i), ℓ ≠ 0 ∧
      ℓ ∈ functionals (upperUnipotent (B.size i) F.Carrier)
        (entrywiseCharacter ψ.complex (B.size i)) (τ i) ∧
      ∀ ℓ', ℓ' ∈ functionals (upperUnipotent (B.size i) F.Carrier)
        (entrywiseCharacter ψ.complex (B.size i)) (τ i) → ∃ c : ℂ, ℓ' = c • ℓ := by
    intro i
    obtain ⟨ℓ, hn, hs⟩ := hspan i
    refine ⟨ℓ.val, hn, ℓ.property, ?_⟩
    intro ℓ' hℓ'
    obtain ⟨c, hc⟩ := hs ⟨ℓ', hℓ'⟩
    exact ⟨c, congrArg Subtype.val hc⟩
  simp_rw [mem_functionals_entrywiseCharacter_iff] at hblocks
  obtain ⟨ℓ, hn, he, _⟩ := hind hblocks
  have hraw : HasFunctional (N := upperUnipotent (n + 1) F.Carrier)
      (θ := entrywiseCharacter ψ.complex (n + 1))
      (Induction.smoothInduced (B.parabolic F.Carrier)
        ((FiniteTensor.external τ).comp (B.leviProjection F.Carrier))) :=
    ⟨⟨ℓ, (mem_functionals_entrywiseCharacter_iff _ _ _ _).mpr he⟩, hn⟩
  rw [entrywiseCharacter_eq_standardCharacter] at hraw
  exact (hasFunctional_iff_of_equiv (T.normalizedProductHalfAbsorptionEquiv B ρ)).mpr hraw
end Langlands.Whittaker
