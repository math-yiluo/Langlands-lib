import Langlands.Global.Factors.CuspidalPairPoleContinuation
import Langlands.Global.Factors.CuspidalPairPoleFiniteEuler
import Langlands.Global.RankinSelberg.EqualEulerFactorizationProof
import Langlands.Global.RankinSelberg.EqualUnfoldingProof
import Langlands.Global.RankinSelberg.SelfPairPositiveData
import Langlands.Global.RankinSelberg.SelfPairResidue

/-! # Equal-rank continuation from normalized partial integrals -/

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1000000

universe u uQ

open NumberField Set
open scoped CategoryTheory.MonObj

namespace Langlands.Global.CuspidalPairPoles

open RankinSelbergGlobal RankinSelbergGlobal.EqualAnalytic
open Automorphic (CuspidalOperatorRealization CuspidalSpectralPresentation
  OperatorRealization conjCharacter)
open CuspidalPairFunctionalEquation (HasIrreducibleAdmissibleComponents)

local instance equalAssemblySchemeAffine (F : Type u) [Field F] (n : ℕ) :
    AlgebraicGeometry.IsAffine (Scheme F n).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme _ _
local instance equalAssemblySchemeSmooth (F : Type u) [Field F] (n : ℕ) :
    AlgebraicGeometry.Smooth (Scheme F n).X.hom :=
  GroupScheme.GeneralLinear.smoothStatement _ _

variable {F : Type u} [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
  {r : ℕ}

/-- An equal-rank global test standard outside the specified finite set. -/
structure EqualPoleTest (T T' : CuspidalOperatorRealization F r) (S : Finset (FinitePlace F)) where
  left : T.Space
  right : T'.Space
  schwartz : RowVector F (r + 1) → ℂ
  sphericalLeft : IsSphericalOutside F T S left
  sphericalRight : IsSphericalOutside F T' S right
  schwartz_mem : schwartz ∈ schwartzBruhat F (r + 1)
  standardSchwartz : IsStandardOutside F (r + 1) S schwartz

variable {T T' : CuspidalOperatorRealization F r}
  {P : CuspidalSpectralPresentation.{u, uQ} T} {P' : CuspidalSpectralPresentation.{u, uQ} T'}
  {h : HasIrreducibleAdmissibleComponents P} {h' : HasIrreducibleAdmissibleComponents P'}
  {c : FinitePairLChoice P P' h h'} {S : Finset (FinitePlace F)}
  {ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles F)} {Linf : ℂ → ℂ}

/-- Entire normalized functions for the equal-rank partial integrals of all tests
standard outside `S`, with a nonzero value among them at every spectral point. -/
structure EqualNormalizedTests (c : FinitePairLChoice P P' h h')
    (S : Finset (FinitePlace F)) (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles F))
    (Linf : ℂ → ℂ) where
  normalized : EqualPoleTest T T' S → ℂ → ℂ
  analytic : ∀ i, AnalyticOnNhd ℂ (normalized i) univ
  nonvanishing : ∀ s, ∃ i, normalized i s ≠ 0
  partial_eq : ∀ i, ∃ σ : ℝ, ∀ s : ℂ, σ < s.re →
    partialEqualWhittakerIntegral F S
      (cuspWhittaker F T ψ.complex i.left) (cuspWhittaker F T' ψ.complex⁻¹ i.right) i.schwartz s =
        normalized i s * Linf s * ∏ v ∈ S, c.finiteL v s

/-- The central character product is trivial and one pair of vectors spherical outside
`S` has nonzero determinant-slab period. -/
def HasEqualTestPeriod (T T' : CuspidalOperatorRealization F r) (S : Finset (FinitePlace F))
    (ω ω' : IdeleClassGroup (𝓞 F) F →ₜ* ℂˣ) : Prop :=
  (∀ z, ideleChar F (ω * ω') z = 1) ∧
    ∃ (x : T.Space) (y : T'.Space), IsSphericalOutside F T S x ∧ IsSphericalOutside F T' S y ∧
      residueConstant F r (fun g => cuspFunction F T x g * cuspFunction F T' y g) 0 ≠ 0

theorem HasEqualTestPeriod.isContragredientOf
    {ω ω' : IdeleClassGroup (𝓞 F) F →ₜ* ℂˣ}
    (hp : HasEqualTestPeriod T T' S ω ω')
    (hω : T.realization.HasCentralCharacter ω) (hω' : T'.realization.HasCentralCharacter ω') :
    T.realization.IsContragredientOf T'.realization := by
  obtain ⟨htriv, x, y, _, _, hres⟩ := hp
  exact isContragredientOf_of_residueConstant_ne_zero F T T' hω hω' htriv x y hres

/-- With the conjugate realization in the first slot, a nonzero spherical vector
gives the required nonzero period. -/
theorem hasEqualTestPeriod_conjugate (hT : IsTrivialOnSplitCentre T)
    {ω : IdeleClassGroup (𝓞 F) F →ₜ* ℂˣ} (hω : T.realization.HasCentralCharacter ω)
    (hP : P.exceptional ⊆ S) :
    HasEqualTestPeriod T.conjugate T S (conjCharacter F ω) ω := by
  obtain ⟨χ, hχu, hχ⟩ := cuspidalSplitCentreUnitaryCentralCharacter F r T hT
  have heq : χ = ω := (T.realization.existsUnique_hasCentralCharacter T.irreducible).unique hχ hω
  subst χ
  obtain ⟨x, hx, hxS⟩ := SelfPair.exists_sphericalOutside_ne_zero P hP
  refine ⟨fun z => ?_, T.conjugateEquiv x, x, SelfPair.isSphericalOutside_conjugate hxS, hxS, ?_⟩
  · rw [mul_comm (conjCharacter F ω) ω, SelfPair.mul_conjCharacter_eq_one ω hχu]
    rfl
  · intro hzero
    have hpos := SelfPair.residueConstant_conjugate_pos T hω x hx
    rw [hzero, Complex.zero_re] at hpos
    exact (lt_irrefl 0) hpos

namespace EqualNormalizedTests

variable (D : EqualNormalizedTests c S ψ Linf)
  {ω ω' : IdeleClassGroup (𝓞 F) F →ₜ* ℂˣ}

private theorem equalIntegral_eq_on_right (hψ : ∀ x : F, ψ (algebraMap F (Adeles F) x) = 1)
    (hP : P.exceptional ⊆ S) (hP' : P'.exceptional ⊆ S)
    (hS : FunctionalEquationComparison.FiniteAdditiveSupport ψ S)
    (hω : T.realization.HasCentralCharacter ω) (hω' : T'.realization.HasCentralCharacter ω') :
    ∀ i, ∃ σ : ℝ, ∀ s : ℂ, σ < s.re →
      equalIntegral F (ω * ω') (cuspFunction F T i.left) (cuspFunction F T' i.right) i.schwartz s =
        D.normalized i s * (Linf s * ∏' v, c.finiteL v s) := by
  have hstd := isStandardAdditiveCharacter_of_unitary ψ hψ
  obtain ⟨a, _, ha⟩ := equalUnfoldingStatement_proof F r T T' ω ω' hω hω'
  obtain ⟨b, hb⟩ := equalEulerFactorization F ψ hψ r T T' P P' S hP hP' hS
  obtain ⟨d, hd⟩ := c.exists_finiteL_convergence hP hP'
  intro i
  obtain ⟨e, he⟩ := D.partial_eq i
  refine ⟨max (max a b) (max d e), fun s hs => ?_⟩
  have hab := (le_max_left (max a b) (max d e)).trans_lt hs
  have hde := (le_max_right (max a b) (max d e)).trans_lt hs
  have hU := ((ha ψ.complex hstd i.left i.right i.schwartz i.schwartz_mem).1 s
    ((le_max_left a b).trans_lt hab)).2.2
  obtain ⟨_, _, q, hq, hE⟩ := hb i.left i.right i.schwartz i.sphericalLeft i.sphericalRight
    i.schwartz_mem i.standardSchwartz s ((le_max_right a b).trans_lt hab)
  have hL := (hd s ((le_max_left d e).trans_lt hde)).2.tprod_eq
  have hpart : RankinSelbergGlobal.partialEulerProduct P P' hP hP' s = q := hq.tprod_eq
  rw [hU, hE, ← hpart, he s ((le_max_right d e).trans_lt hde), hL]
  ring

/-- The normalized covering family gives the continuation and initially detects
the poles through the determinant-slab periods of the tests. -/
theorem exists_completion (hψ : ∀ x : F, ψ (algebraMap F (Adeles F) x) = 1)
    (hP : P.exceptional ⊆ S) (hP' : P'.exceptional ⊆ S)
    (hS : FunctionalEquationComparison.FiniteAdditiveSupport ψ S)
    (hT : IsTrivialOnSplitCentre T) (hT' : IsTrivialOnSplitCentre T')
    (hω : T.realization.HasCentralCharacter ω) (hω' : T'.realization.HasCentralCharacter ω')
    (hL : ∃ σ : ℝ, ContinuousOn (fun s => Linf s * ∏' v, c.finiteL v s) {s | σ < s.re}) :
    ∃ Λ : ℂ → ℂ, c.IsCompletedLFunction Linf Λ ∧
      HasSimplePoleProfile Λ (HasEqualTestPeriod T T' S ω ω') ∧
      ∀ i, ∃ I : ℂ → ℂ, IsBoundedInVerticalStrips I ∧
        ∀ s ∉ ({0, 1} : Set ℂ), I s = D.normalized i s * Λ s := by
  have hstd := isStandardAdditiveCharacter_of_unitary ψ hψ
  choose σ I hI hIb hIr using fun i : EqualPoleTest T T' S =>
    equalIntegral_splitCentre_continuation T T' hT hT' hω hω' ψ.complex hstd
      i.left i.right i.schwartz i.schwartz_mem
  have hMatch (i : EqualPoleTest T T' S) :
      ∃ a : ℝ, ∀ s : ℂ, a < s.re → I i s = D.normalized i s * (Linf s * ∏' v, c.finiteL v s) := by
    obtain ⟨b, hb⟩ := D.equalIntegral_eq_on_right hψ hP hP' hS hω hω' i
    refine ⟨max (σ i) b, fun s hs => ?_⟩
    exact ((hI i s ((le_max_left _ _).trans_lt hs)).2).trans (hb s ((le_max_right _ _).trans_lt hs))
  have hPole (p : ℂ) (hp : p ∈ ({0, 1} : Set ℂ)) :
      (∃ i, meromorphicOrderAt (I i) p < 0) ↔ HasEqualTestPeriod T T' S ω ω' := by
    constructor
    · rintro ⟨i, hi⟩
      obtain ⟨ht, hres, _⟩ := ((hIr i).2 p hp).2.2.mp hi
      exact ⟨ht, i.left, i.right, i.sphericalLeft, i.sphericalRight, hres⟩
    · rintro ⟨ht, x, y, hx, hy, hres⟩
      obtain ⟨Φ, hΦ, hstdΦ, hΦ₀, hΦh₀⟩ :=
        SelfPair.exists_schwartzBruhat_origin_ne_zero (r + 1) S ψ.complex
      let i : EqualPoleTest T T' S := ⟨x, y, Φ, hx, hy, hΦ, hstdΦ⟩
      refine ⟨i, ((hIr i).2 p hp).2.2.mpr ⟨ht, hres, ?_⟩⟩
      by_cases heq : p = 0
      · simpa only [heq, ite_true, i] using hΦ₀
      · simpa only [heq, ite_false, i] using hΦh₀
  obtain ⟨Λ, ⟨a, ha⟩, hΛ, hpoles⟩ := exists_continuation_of_normalized_tests
    I D.normalized (fun s => Linf s * ∏' v, c.finiteL v s) _
    (fun i => (hIr i).1) (fun i p hp => ⟨((hIr i).2 p hp).1, ((hIr i).2 p hp).2.1⟩)
    D.analytic D.nonvanishing hL hMatch hPole
  obtain ⟨b, hb⟩ := c.exists_finiteL_convergence hP hP'
  refine ⟨Λ, ⟨max a b, fun s hs => ?_⟩, hpoles, fun i => ⟨I i, hIb i, hΛ i⟩⟩
  obtain ⟨hsum, hprod⟩ := hb s ((le_max_right _ _).trans_lt hs)
  exact ⟨hsum, _, hprod.multipliable.hasProd, ha s ((le_max_left _ _).trans_lt hs)⟩

end EqualNormalizedTests

end Langlands.Global.CuspidalPairPoles
