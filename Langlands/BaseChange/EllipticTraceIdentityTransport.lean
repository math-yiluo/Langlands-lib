import Langlands.BaseChange.TwistedEllipticNonvanishingTransport
import Langlands.BaseChange.SigmaLiftTransport
import Langlands.Representation.Smooth.Admissibility.EquivalenceProof
import Langlands.BaseChange.ConcordanceRingEquiv

/-!
# Transport of an elliptic twisted trace identity along an isomorphism of algebras

Let `F` be a topological field, `R₁` and `R₂` topological `F`-algebras with automorphisms `σ₁`,
`σ₂`, and `ε : R₁ ≃ₐ[F] R₂` a homeomorphic isomorphism with `ε ∘ σ₁ = σ₂ ∘ ε`. A trace identity
`tr (τ₂(φ) ∘ A₂) = c · tr π(f)` on the test pairs over `R₂` (σ₂-elliptic `φ`, regular elliptic
`f` with determinants in the norm image, concordant) gives the same identity, with the same `c`,
for a representation `τ₁` of `GL_n(R₁)` equivalent to `τ₂ ∘ GL_n(ε)`.
-/

noncomputable section

set_option autoImplicit false

open MeasureTheory Langlands.JacquetLanglands Langlands.HarmonicAnalysis

namespace Langlands.BaseChange

universe u v₁ v₂ uV uW₁ uW₂

variable {F : Type u} [Field F] [TopologicalSpace F] [IsTopologicalRing F]
  {R₁ : Type v₁} [CommRing R₁] [Algebra F R₁] [TopologicalSpace R₁] [IsTopologicalRing R₁]
  {R₂ : Type v₂} [CommRing R₂] [Algebra F R₂] [TopologicalSpace R₂] [IsTopologicalRing R₂]
  {σ₁ : R₁ ≃ₐ[F] R₁} {σ₂ : R₂ ≃ₐ[F] R₂} {n l : ℕ}

/-- A σ₂-intertwiner of `τ₂` is a σ₁-intertwiner of the pullback `τ₂ ∘ GL_n(ε)`. -/
def SigmaIntertwiner.pullbackRingEquiv {W : Type uW₂} [AddCommGroup W] [Module ℂ W]
    {τ : Representation ℂ (GeneralLinear n R₂) W} (ε : R₁ ≃+* R₂) (hε : Continuous ε)
    (hε' : Continuous ε.symm) (hσ : ∀ x, ε (σ₁ x) = σ₂ (ε x)) (A : SigmaIntertwiner σ₂ n τ) :
    SigmaIntertwiner σ₁ n (τ.comp (generalLinearRingEquiv (n := n) ε hε hε').toMonoidHom) where
  toLinearEquiv := A.toLinearEquiv
  isIntertwining' g := by
    have h := A.isIntertwining' (generalLinearRingEquiv (n := n) ε hε hε' g)
    have hθ : generalLinearRingEquiv ε hε hε' (entrywiseAut σ₁ n g) =
        entrywiseAut σ₂ n (generalLinearRingEquiv ε hε hε' g) := by
      ext i j
      simp only [generalLinearRingEquiv_apply_apply, entrywiseAut_apply_apply, hσ]
    change A.toLinearMap ∘ₗ τ (generalLinearRingEquiv ε hε hε' g) =
      τ (generalLinearRingEquiv ε hε hε' (entrywiseAut σ₁ n g)) ∘ₗ A.toLinearMap
    rw [hθ]
    exact h

omit [TopologicalSpace F] [IsTopologicalRing F] [TopologicalSpace R₁] [IsTopologicalRing R₁]
  [TopologicalSpace R₂] [IsTopologicalRing R₂] in
/-- The norm images of `R₁ˣ` and `R₂ˣ` in `Fˣ` agree. -/
theorem normUnitsRange_algEquiv (ε : R₁ ≃ₐ[F] R₂) :
    (Units.map (Algebra.norm F : R₁ →* F)).range =
      (Units.map (Algebra.norm F : R₂ →* F)).range := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    refine ⟨Units.map ε.toRingEquiv.toMonoidHom y, ?_⟩
    ext
    change Algebra.norm F (ε (y : R₁)) = Algebra.norm F (y : R₁)
    exact Algebra.norm_eq_of_algEquiv ε (y : R₁)
  · rintro ⟨y, rfl⟩
    refine ⟨Units.map ε.symm.toRingEquiv.toMonoidHom y, ?_⟩
    ext
    change Algebra.norm F (ε.symm (y : R₂)) = Algebra.norm F (y : R₂)
    exact Algebra.norm_eq_of_algEquiv ε.symm (y : R₂)

/-- An admissible representation has an elliptic twisted trace identity against `π` if some
intertwiner and nonzero scalar give the identity on concordant elliptic norm test pairs for
all Haar measures. -/
def HasEllipticTraceIdentity {R : Type*} [CommRing R] [Algebra F R] [TopologicalSpace R]
    [IsTopologicalRing R] [T2Space (GeneralLinear n F)] [LocallyCompactSpace (GeneralLinear n F)]
    [TotallyDisconnectedSpace (GeneralLinear n F)] [T2Space (GeneralLinear n R)]
    [LocallyCompactSpace (GeneralLinear n R)] [TotallyDisconnectedSpace (GeneralLinear n R)]
    {V : Type uV} [AddCommGroup V] [Module ℂ V] {W : Type*} [AddCommGroup W] [Module ℂ W]
    (σ : R ≃ₐ[F] R) (l : ℕ) (π : Representation ℂ (GeneralLinear n F) V) (hπ : IsAdmissible π)
    (τ : Representation ℂ (GeneralLinear n R) W) : Prop :=
  ∃ (hτ : IsAdmissible τ) (A : SigmaIntertwiner σ n τ) (c : ℂ), c ≠ 0 ∧
    letI : MeasurableSpace (GeneralLinear n F) := borel _
    haveI : BorelSpace (GeneralLinear n F) := ⟨rfl⟩
    letI : MeasurableSpace (GeneralLinear n R) := borel _
    haveI : BorelSpace (GeneralLinear n R) := ⟨rfl⟩
    ∀ (μF : Measure (GeneralLinear n F)) [μF.IsHaarMeasure]
      (μR : Measure (GeneralLinear n R)) [μR.IsHaarMeasure]
      (φ : SchwartzBruhat (GeneralLinear n R)) (f : SchwartzBruhat (GeneralLinear n F)),
      IsSigmaEllipticSupported σ l (φ : GeneralLinear n R → ℂ) →
      IsEllipticSupported (f : GeneralLinear n F → ℂ) →
      (∀ g : GeneralLinear n F, f g ≠ 0 →
        GeneralLinear.determinant g ∈ (Units.map (Algebra.norm F : R →* F)).range) →
      AreConcordant σ l μF μR φ f →
      twistedDistribution μR τ hτ A.toLinearMap φ = c * Character.distribution μF π hπ f

/-- **Transport of an elliptic twisted trace identity.** Let `ε : R₁ ≃ₐ[F] R₂` be a homeomorphic
isomorphism of topological `F`-algebras with `ε ∘ σ₁ = σ₂ ∘ ε`, and let `τ₁` be a representation
of `GL_n(R₁)` equivalent to `τ₂ ∘ GL_n(ε)`. If `τ₂` is admissible and has a σ₂-intertwiner `A₂`
and a constant `c ≠ 0` with `tr (τ₂(φ) ∘ A₂) = c · tr π(f)` for all Haar measures and all test
pairs over `R₂` (σ₂-elliptic `φ`, regular elliptic `f` with determinants in the norm image,
concordant), then the same holds for `τ₁`, a σ₁-intertwiner and the same `c`, over `R₁`. -/
theorem ellipticTraceIdentity_transport
    (ε : R₁ ≃ₐ[F] R₂) (hε : Continuous ε) (hε' : Continuous ε.symm)
    (hσ : ∀ x, ε (σ₁ x) = σ₂ (ε x))
    (hF₁ : Continuous (algebraMap F R₁)) (hF₂ : Continuous (algebraMap F R₂))
    [T2Space (GeneralLinear n F)] [LocallyCompactSpace (GeneralLinear n F)]
    [TotallyDisconnectedSpace (GeneralLinear n F)]
    [T2Space (GeneralLinear n R₁)] [LocallyCompactSpace (GeneralLinear n R₁)]
    [TotallyDisconnectedSpace (GeneralLinear n R₁)]
    [T2Space (GeneralLinear n R₂)] [LocallyCompactSpace (GeneralLinear n R₂)]
    [TotallyDisconnectedSpace (GeneralLinear n R₂)]
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GeneralLinear n F) V) (hπ : IsAdmissible π)
    {W₁ : Type uW₁} [AddCommGroup W₁] [Module ℂ W₁] {W₂ : Type uW₂} [AddCommGroup W₂]
    [Module ℂ W₂]
    (τ₁ : Representation ℂ (GeneralLinear n R₁) W₁)
    (τ₂ : Representation ℂ (GeneralLinear n R₂) W₂)
    (B : τ₁.Equiv (τ₂.comp (generalLinearRingEquiv (n := n) ε.toRingEquiv hε hε').toMonoidHom))
    (h₂ : HasEllipticTraceIdentity σ₂ l π hπ τ₂) :
    HasEllipticTraceIdentity σ₁ l π hπ τ₁ := by
  obtain ⟨hτ₂, A₂, c, hc, hid⟩ := h₂
  let κ := generalLinearRingEquiv (n := n) ε.toRingEquiv hε hε'
  have hτ₂κ : IsAdmissible (τ₂.comp κ.toMonoidHom) :=
    isAdmissible_comp_continuousMulEquiv τ₂ κ hτ₂
  have hτ₁ : IsAdmissible τ₁ := (Langlands.isAdmissible_iff_of_equiv B).mpr hτ₂κ
  let A₂' := SigmaIntertwiner.pullbackRingEquiv ε.toRingEquiv hε hε' hσ A₂
  refine ⟨hτ₁, A₂'.transport B.symm, c, hc, ?_⟩
  intro μF _ μE _ φ f hφ hf hdet hconc
  let : MeasurableSpace (GeneralLinear n F) := borel _
  have : BorelSpace (GeneralLinear n F) := ⟨rfl⟩
  let : MeasurableSpace (GeneralLinear n R₁) := borel _
  have : BorelSpace (GeneralLinear n R₁) := ⟨rfl⟩
  let : MeasurableSpace (GeneralLinear n R₂) := borel _
  have : BorelSpace (GeneralLinear n R₂) := ⟨rfl⟩
  have := κ.isHaarMeasure_map μE
  let φ₂ := Hecke.TestFunction.pullback κ.symm.toHomeomorph φ
  have hι : ∀ a : F, ε.toRingEquiv (algebraMap F R₁ a) = algebraMap F R₂ a :=
    fun a => ε.commutes a
  have hell : IsSigmaEllipticSupported σ₂ l (φ₂ : GeneralLinear n R₂ → ℂ) := by
    intro y hy
    have hy' : φ (κ.symm y) ≠ 0 := hy
    have h := (isSigmaElliptic_generalLinearRingEquiv_iff (l := l) ε.toRingEquiv hε hε' hι hσ
      (κ.symm y)).2 (hφ _ hy')
    rwa [ContinuousMulEquiv.apply_symm_apply] at h
  have hdet' : ∀ g : GeneralLinear n F, f g ≠ 0 →
      GeneralLinear.determinant g ∈ (Units.map (Algebra.norm F : R₂ →* F)).range := by
    intro g hg
    rw [← normUnitsRange_algEquiv ε]
    exact hdet g hg
  have hconc' : AreConcordant σ₂ l μF (μE.map κ) φ₂ f := by
    have hι' : ∀ a : F, ε.symm.toRingEquiv (algebraMap F R₂ a) =
        algebraMap F R₁ ((RingEquiv.refl F) a) := fun a => ε.symm.commutes a
    have hσ' : ∀ a : R₂, ε.symm.toRingEquiv (σ₂ a) = σ₁ (ε.symm.toRingEquiv a) := by
      intro a
      apply ε.injective
      change ε (ε.symm (σ₂ a)) = ε (σ₁ (ε.symm a))
      rw [hσ, AlgEquiv.apply_symm_apply, AlgEquiv.apply_symm_apply]
    have hmain := (concordanceRingEquiv (n := n) (l := l) σ₂ σ₁ (RingEquiv.refl F)
      ε.symm.toRingEquiv continuous_id continuous_id hε' hε hι' hσ' hF₂ hF₁ μF (μE.map κ)
      (φ : GeneralLinear n R₁ → ℂ) (f : GeneralLinear n F → ℂ)).2
    have hκF : (generalLinearRingEquiv (n := n) (RingEquiv.refl F) continuous_id
        continuous_id : GeneralLinear n F → GeneralLinear n F) = id := by
      funext g
      ext i j
      rfl
    have hκE : (generalLinearRingEquiv (n := n) ε.symm.toRingEquiv hε' hε :
        GeneralLinear n R₂ → GeneralLinear n R₁) = κ.symm := by
      funext g
      ext i j
      rfl
    have hμE : Measure.map (generalLinearRingEquiv (n := n) ε.symm.toRingEquiv hε' hε)
        (μE.map κ) = μE := by
      have hm1 : Measurable (κ.symm : GeneralLinear n R₂ → GeneralLinear n R₁) :=
        κ.symm.continuous.measurable
      have hm2 : Measurable (κ : GeneralLinear n R₁ → GeneralLinear n R₂) :=
        κ.continuous.measurable
      rw [hκE, Measure.map_map hm1 hm2]
      have : (κ.symm ∘ κ : GeneralLinear n R₁ → GeneralLinear n R₁) = id := by
        funext g
        exact κ.symm_apply_apply g
      rw [this, Measure.map_id]
    have h := hmain (by rw [hκF, Measure.map_id, hμE]; exact hconc)
    rw [hκF, hκE] at h
    exact h
  have key := hid μF (μE.map κ) φ₂ f hell hf hdet' hconc'
  have h1 : twistedDistribution μE τ₁ hτ₁ (A₂'.transport B.symm).toLinearMap φ =
      twistedDistribution μE (τ₂.comp κ.toMonoidHom) hτ₂κ A₂'.toLinearMap φ := by
    rw [← twistedDistribution_eq_of_equivalent μE hτ₁ hτ₂κ B]
    congr 2
    rw [SigmaIntertwiner.transport_toLinearMap]
    exact LinearEquiv.conj_conj_symm _ _
  rw [h1, twistedDistribution_comp_equiv κ μE τ₂ hτ₂ hτ₂κ A₂'.toLinearMap φ]
  exact key

/-- Variant of `ellipticTraceIdentity_transport` for representations pulled back from other
groups: if `τ₁ = ρ₁ ∘ ψ₁`, `τ₂ = ρ₂ ∘ ψ₂`, `ρ₁ ≅ ρ₂ ∘ c` and `c ∘ ψ₁ = ψ₂ ∘ GL_n(ε)`, the
identity for `τ₂` gives the identity for `τ₁` with the same constant. -/
theorem ellipticTraceIdentity_transport_comp
    (ε : R₁ ≃ₐ[F] R₂) (hε : Continuous ε) (hε' : Continuous ε.symm)
    (hσ : ∀ x, ε (σ₁ x) = σ₂ (ε x))
    (hF₁ : Continuous (algebraMap F R₁)) (hF₂ : Continuous (algebraMap F R₂))
    [T2Space (GeneralLinear n F)] [LocallyCompactSpace (GeneralLinear n F)]
    [TotallyDisconnectedSpace (GeneralLinear n F)]
    [T2Space (GeneralLinear n R₁)] [LocallyCompactSpace (GeneralLinear n R₁)]
    [TotallyDisconnectedSpace (GeneralLinear n R₁)]
    [T2Space (GeneralLinear n R₂)] [LocallyCompactSpace (GeneralLinear n R₂)]
    [TotallyDisconnectedSpace (GeneralLinear n R₂)]
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GeneralLinear n F) V) (hπ : IsAdmissible π)
    {G₁ G₂ : Type*} [Monoid G₁] [Monoid G₂]
    {W₁ : Type uW₁} [AddCommGroup W₁] [Module ℂ W₁] {W₂ : Type uW₂} [AddCommGroup W₂]
    [Module ℂ W₂]
    {ρ₁ : Representation ℂ G₁ W₁} {ρ₂ : Representation ℂ G₂ W₂} {c : G₁ →* G₂}
    (B₀ : ρ₁.Equiv (ρ₂.comp c))
    (ψ₁ : GeneralLinear n R₁ →* G₁) (ψ₂ : GeneralLinear n R₂ →* G₂)
    (hident : ∀ g, c (ψ₁ g) = ψ₂ (generalLinearRingEquiv (n := n) ε.toRingEquiv hε hε' g))
    (h₂ : HasEllipticTraceIdentity σ₂ l π hπ (ρ₂.comp ψ₂)) :
    HasEllipticTraceIdentity σ₁ l π hπ (ρ₁.comp ψ₁) := by
  let κ := generalLinearRingEquiv (n := n) ε.toRingEquiv hε hε'
  let B : Representation.Equiv (ρ₁.comp ψ₁) ((ρ₂.comp ψ₂).comp κ.toMonoidHom) :=
    Representation.Equiv.mk B₀.toLinearEquiv (fun g => by
      have h1 := B₀.toIntertwiningMap.isIntertwining' (ψ₁ g)
      change B₀.toLinearEquiv.toLinearMap ∘ₗ ρ₁ (ψ₁ g) =
        ρ₂ (c (ψ₁ g)) ∘ₗ B₀.toLinearEquiv.toLinearMap at h1
      change B₀.toLinearEquiv.toLinearMap ∘ₗ ρ₁ (ψ₁ g) =
        ρ₂ (ψ₂ (κ g)) ∘ₗ B₀.toLinearEquiv.toLinearMap
      rw [← hident g]
      exact h1)
  exact ellipticTraceIdentity_transport ε hε hε' hσ hF₁ hF₂ π hπ (ρ₁.comp ψ₁) (ρ₂.comp ψ₂) B h₂

end Langlands.BaseChange
