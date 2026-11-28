import Langlands.BaseChange.TwistedSupercuspidalEllipticNonvanishingStatement
import Langlands.BaseChange.ConcordanceRingEquiv
import Langlands.BaseChange.TwistedLocalGroupTransport
import Langlands.Representation.CuspidalSupport.GroupTransport

/-!
# Nonvanishing of twisted traces on the σ-elliptic set, transported along ring isomorphisms

`TwistedSupercuspidalEllipticNonvanishingStatement` concerns a cyclic algebra `E'` over a
nonarchimedean local field `F` that is a field. This module carries its conclusion along a
continuous isomorphism `b : E ≃+* E'` of `F`-algebras intertwining automorphisms `σ` of `E` and
`σ'` of `E'`, to the representation `τ' ∘ GL_n(b)` of `GL_n(E)`, where `E` need only be a
commutative ring. The case of interest is `E = F_v ⊗_F E₀` for a cyclic extension of number
fields `E₀/F₀` and a place `v` of `F₀` with a single place `w` of `E₀` above it, where `b` is
the canonical isomorphism onto the completion `E₀,w`.
-/

noncomputable section

set_option autoImplicit false

open MeasureTheory Langlands.JacquetLanglands Langlands.HarmonicAnalysis

namespace Langlands.BaseChange

universe u v v' uW

section RingEquiv

variable {F : Type u} [Field F] [TopologicalSpace F]
  {E : Type v} [CommRing E] [Algebra F E] [TopologicalSpace E]
  {E' : Type v'} [CommRing E'] [Algebra F E'] [TopologicalSpace E']
  {n l : ℕ} {σ : E ≃ₐ[F] E} {σ' : E' ≃ₐ[F] E'}
  (b : E ≃+* E') (hb : Continuous b) (hb' : Continuous b.symm)
  (hι : ∀ a : F, b (algebraMap F E a) = algebraMap F E' a)
  (hσ : ∀ x : E, b (σ x) = σ' (b x))

include hι hσ in
/-- σ-ellipticity is preserved and reflected by a compatible ring isomorphism. -/
theorem isSigmaElliptic_generalLinearRingEquiv_iff (δ : GeneralLinear n E) :
    IsSigmaElliptic σ' l (generalLinearRingEquiv b hb hb' δ) ↔ IsSigmaElliptic σ l δ := by
  have hι' : ∀ a : F, b (algebraMap F E a) = algebraMap F E' ((RingEquiv.refl F) a) := hι
  have hrefl : ∀ γ : GeneralLinear n F,
      generalLinearRingEquiv (RingEquiv.refl F) continuous_id continuous_id γ = γ := by
    intro γ
    ext i j
    rfl
  constructor
  · rintro ⟨γ, hassoc, hell⟩
    refine ⟨γ, ?_, hell⟩
    rw [← generalLinearRingEquiv_isNormAssociated_iff (RingEquiv.refl F) b continuous_id
      continuous_id hb hb' hι' hσ, hrefl]
    exact hassoc
  · rintro ⟨γ, hassoc, hell⟩
    refine ⟨γ, ?_, hell⟩
    have := (generalLinearRingEquiv_isNormAssociated_iff (RingEquiv.refl F) b continuous_id
      continuous_id hb hb' hι' hσ (l := l) δ γ).2 hassoc
    rwa [hrefl] at this

/-- A σ-intertwiner of the pullback `τ' ∘ GL_n(b)` is a σ'-intertwiner of `τ'`. -/
def SigmaIntertwiner.ofGeneralLinearRingEquiv {W : Type uW} [AddCommGroup W] [Module ℂ W]
    {τ' : Representation ℂ (GeneralLinear n E') W}
    (A : SigmaIntertwiner σ n (τ'.comp (generalLinearRingEquiv b hb hb').toMonoidHom)) :
    SigmaIntertwiner σ' n τ' where
  toLinearEquiv := A.toLinearEquiv
  isIntertwining' g' := by
    obtain ⟨g, rfl⟩ := (generalLinearRingEquiv (n := n) b hb hb').surjective g'
    have h := A.isIntertwining' g
    have hθ : generalLinearRingEquiv b hb hb' (entrywiseAut σ n g) =
        entrywiseAut σ' n (generalLinearRingEquiv b hb hb' g) := by
      ext i j
      simp only [generalLinearRingEquiv_apply_apply, entrywiseAut_apply_apply, hσ]
    change A.toLinearMap ∘ₗ τ' (generalLinearRingEquiv b hb hb' g) =
      τ' (generalLinearRingEquiv b hb hb' (entrywiseAut σ n g)) ∘ₗ A.toLinearMap at h
    rw [hθ] at h
    exact h

omit [TopologicalSpace F] in
@[simp] theorem SigmaIntertwiner.ofGeneralLinearRingEquiv_toLinearMap {W : Type uW}
    [AddCommGroup W] [Module ℂ W] {τ' : Representation ℂ (GeneralLinear n E') W}
    (A : SigmaIntertwiner σ n (τ'.comp (generalLinearRingEquiv b hb hb').toMonoidHom)) :
    (SigmaIntertwiner.ofGeneralLinearRingEquiv b hb hb' hσ A).toLinearMap = A.toLinearMap :=
  rfl

end RingEquiv

section Nonvanishing

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] [CharZero F]
  {E : Type v} [CommRing E] [Algebra F E] [TopologicalSpace E] [IsTopologicalRing E]
  {E' : Type v'} [Field E'] [Algebra F E'] [TopologicalSpace E'] [IsTopologicalRing E']
  [IsModuleTopology F E']
  {n l : ℕ} {σ : E ≃ₐ[F] E} {σ' : E' ≃ₐ[F] E'}

/-- **Transport of `TwistedSupercuspidalEllipticNonvanishingStatement` along a ring
isomorphism.** Let `b : E ≃+* E'` be a homeomorphic isomorphism of `F`-algebras with
`b ∘ σ = σ' ∘ b`, where `E'` is a field that is a cyclic `F`-algebra for `σ'` of degree `l`.
Let `τ'` be an irreducible supercuspidal representation of `GL_n(E')`, `0 < n`, and let
`ψ : GL_n(E) → GL_n(E')` be the entrywise map of `b`. Then for the pullback `τ = τ' ∘ ψ`, every
σ-intertwiner `A` of `τ` and every Haar measure `μ` on `GL_n(E)`, some Schwartz–Bruhat function
supported in the σ-elliptic set has `tr (τ(φ) ∘ A) ≠ 0`. -/
theorem exists_sigmaEllipticSupported_twistedDistribution_ne_zero_of_ringEquiv
    (hNV : TwistedSupercuspidalEllipticNonvanishingStatement.{u, v', uW})
    (hE' : IsCyclicAlgebra σ' l) (hn : 0 < n)
    (b : E ≃+* E') (hb : Continuous b) (hb' : Continuous b.symm)
    (hι : ∀ a : F, b (algebraMap F E a) = algebraMap F E' a)
    (hσ : ∀ x : E, b (σ x) = σ' (b x))
    (ψ : GeneralLinear n E →* GeneralLinear n E')
    (hψ : ψ = (generalLinearRingEquiv (n := n) b hb hb').toMonoidHom)
    [T2Space (GeneralLinear n E)] [LocallyCompactSpace (GeneralLinear n E)]
    [TotallyDisconnectedSpace (GeneralLinear n E)]
    [MeasurableSpace (GeneralLinear n E)] [BorelSpace (GeneralLinear n E)]
    {W : Type uW} [AddCommGroup W] [Module ℂ W]
    (τ' : Representation ℂ (GeneralLinear n E') W) (hsc : GeneralLinear.IsSupercuspidal τ')
    (hirr : τ'.IsIrreducible) (hτ : IsAdmissible (τ'.comp ψ))
    (A : SigmaIntertwiner σ n (τ'.comp ψ))
    (μ : Measure (GeneralLinear n E)) [μ.IsHaarMeasure] :
    ∃ φ : SchwartzBruhat (GeneralLinear n E), IsSigmaEllipticSupported σ l (φ : _ → ℂ) ∧
      twistedDistribution μ (τ'.comp ψ) hτ A.toLinearMap φ ≠ 0 := by
  subst hψ
  have : Module.Finite F E' := hE'.1
  have := generalLinear_t2Space_of_finite F E' n
  have := generalLinear_locallyCompactSpace_of_finite F E' n
  have := generalLinear_totallyDisconnectedSpace_of_finite F E' n
  let : MeasurableSpace (GeneralLinear n E') := borel _
  have : BorelSpace (GeneralLinear n E') := ⟨rfl⟩
  let κ := generalLinearRingEquiv (n := n) b hb hb'
  let A' := SigmaIntertwiner.ofGeneralLinearRingEquiv b hb hb' hσ A
  have := κ.isHaarMeasure_map μ
  obtain ⟨φ', hφ', hne⟩ := hNV F E' σ' l n hE' hn τ' hsc hirr A' (μ.map κ)
  refine ⟨Hecke.TestFunction.pullback κ.toHomeomorph φ', ?_, ?_⟩
  · intro δ hδ
    have hδ' : φ' (κ δ) ≠ 0 := hδ
    exact (isSigmaElliptic_generalLinearRingEquiv_iff b hb hb' hι hσ δ).1 (hφ' _ hδ')
  · rw [twistedDistribution_comp_equiv κ μ τ' hsc.1 hτ A.toLinearMap]
    have hpull : Hecke.TestFunction.pullback κ.symm.toHomeomorph
        (Hecke.TestFunction.pullback κ.toHomeomorph φ') = φ' := by
      ext x
      change φ' (κ (κ.symm x)) = φ' x
      rw [ContinuousMulEquiv.apply_symm_apply]
    rw [hpull]
    exact hne

end Nonvanishing

end Langlands.BaseChange
