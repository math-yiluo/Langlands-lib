import Langlands.Automorphic.Unramified.CyclicOrbitInductionComparisonStatement
import Langlands.Automorphic.Unramified.WeakInductionPairEulerValues
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Subgroup

/-! # Cofinite pair Euler comparison for two weak inductions -/

noncomputable section

set_option autoImplicit false

universe uF uE uV uW

namespace Langlands.Automorphic.Unramified

open Langlands.Global Langlands.Global.AdelicFunctoriality
open Langlands.Global.CuspidalPairFunctionalEquation
open CuspidalOperatorRealization Filter Polynomial

variable {F : Type uF} {E : Type uE} [Field F] [NumberField F] [Field E] [NumberField E]
  [Algebra F E] [IsGalois F E]

/-- The enumeration of the Galois group by the powers of a generator. -/
def galoisGeneratorEquiv (σ : E ≃ₐ[F] E) (hgen : ∀ τ : E ≃ₐ[F] E, τ ∈ Subgroup.zpowers σ) :
    Fin (Module.finrank F E) ≃ (E ≃ₐ[F] E) := by
  have horder : orderOf σ = Module.finrank F E :=
    (orderOf_eq_card_of_forall_mem_zpowers hgen).trans (IsGalois.card_aut_eq_finrank F E)
  exact ((finCongr horder.symm).trans (finEquivZPowers (isOfFinOrder_of_finite σ))).trans
    (Equiv.ofBijective Subtype.val ⟨Subtype.val_injective, fun τ => ⟨⟨τ, hgen τ⟩, rfl⟩⟩)

@[simp] theorem galoisGeneratorEquiv_apply (σ : E ≃ₐ[F] E)
    (hgen : ∀ τ : E ≃ₐ[F] E, τ ∈ Subgroup.zpowers σ) (i : Fin (Module.finrank F E)) :
    galoisGeneratorEquiv σ hgen i = σ ^ (i : ℕ) := by
  rfl

variable [CompactSpace (AdeleQuotient E)]

/-- A sequence of genuine cuspidal conjugates indexed by the exponents of a
cyclic generator represents the full isobaric Galois orbit with multiplicity. -/
theorem galoisOrbit_eq_of_conjugates (σ : E ≃ₐ[F] E)
    (hgen : ∀ τ : E ≃ₐ[F] E, τ ∈ Subgroup.zpowers σ) {m : ℕ}
    (T : CuspidalOperatorRealization E m)
    (U : Fin (Module.finrank F E) → CuspidalOperatorRealization E m)
    (hU : ∀ i : Fin (Module.finrank F E), T.isoClass.IsGaloisConjugate (σ ^ (i : ℕ)) (U i).isoClass) :
    (Finset.univ.val.map fun i => PositiveRankCuspidalClass.ofFixedRank (U i).isoClass) =
      IsobaricData.galoisOrbit F (PositiveRankCuspidalClass.ofFixedRank T.isoClass) := by
  classical
  let e := galoisGeneratorEquiv σ hgen
  let c := PositiveRankCuspidalClass.ofFixedRank T.isoClass
  change (Finset.univ.val.map fun i => PositiveRankCuspidalClass.ofFixedRank (U i).isoClass) =
    Finset.univ.val.map (fun τ : E ≃ₐ[F] E => c.galoisConj τ)
  calc _ = Finset.univ.val.map ((fun τ => c.galoisConj τ) ∘ e) := by
        apply Multiset.map_congr rfl
        intro i _
        simp only [Function.comp_apply, e, galoisGeneratorEquiv_apply, c,
          PositiveRankCuspidalClass.galoisConj_ofFixedRank]
        exact congrArg PositiveRankCuspidalClass.ofFixedRank
          ((IsoClass.isGaloisConjugate_iff _ _ _).mp (hU i))
    _ = _ := by rw [← Multiset.map_map, Multiset.map_univ_val_equiv]

/-- If weak induction gives weak base change to the full orbit, the pair Euler
factor of two weak inductions is the product of the upper factors of the first
source paired with each arithmetic conjugate of the second source. -/
def WeakInductionOrbitPairEulerValuesStatement : Prop :=
  WeakInductionOrbitBaseChangeStatement.{uF, uE, uV, uW} →
  ∀ (F : Type uF) (E : Type uE) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] [IsGalois F E] [CompactSpace (AdeleQuotient F)]
    [CompactSpace (AdeleQuotient E)]
    (σ : E ≃ₐ[F] E) (_hgen : ∀ τ : E ≃ₐ[F] E, τ ∈ Subgroup.zpowers σ)
    {r r' m m' : ℕ}
    (S : CuspidalOperatorRealization F r) (S' : CuspidalOperatorRealization F r')
    (T : CuspidalOperatorRealization E m) (T' : CuspidalOperatorRealization E m')
    (U : Fin (Module.finrank F E) → CuspidalOperatorRealization E m')
    (P : CuspidalSpectralPresentation.{uF, uV} S)
    (P' : CuspidalSpectralPresentation.{uF, uV} S')
    (Q : CuspidalSpectralPresentation.{uE, uW} T)
    (Q' : ∀ i, CuspidalSpectralPresentation.{uE, uW} (U i)),
    (∀ i : Fin (Module.finrank F E), T'.isoClass.IsGaloisConjugate (σ ^ (i : ℕ)) (U i).isoClass) →
    IsoClass.IsWeakInductionOf.{uF, uE, uV, uW} S.isoClass T.isoClass →
    IsoClass.IsWeakInductionOf.{uF, uE, uV, uW} S'.isoClass T'.isoClass →
    ∀ᶠ v : FinitePlace F in cofinite,
      ∃ (hv : v ∉ P.exceptional) (hv' : v ∉ P'.exceptional)
        (hw : ∀ w : FinitePlacesAbove E v, w.1 ∉ Q.exceptional)
        (hw' : ∀ (i : Fin (Module.finrank F E)) (w : FinitePlacesAbove E v),
          w.1 ∉ (Q' i).exceptional),
      ∀ z : ℂ,
        ((pairEulerPolynomial (P.spectralSystem.eigenvalues v hv)
          (P'.spectralSystem.eigenvalues v hv')).eval
            (RankinSelberg.spectralPoint (residueCardinality v) z))⁻¹ =
        ∏ w : FinitePlacesAbove E v, ∏ i : Fin (Module.finrank F E),
          ((pairEulerPolynomial (Q.spectralSystem.eigenvalues w.1 (hw w))
            ((Q' i).spectralSystem.eigenvalues w.1 (hw' i w))).eval
              (RankinSelberg.spectralPoint (residueCardinality w.1) z))⁻¹

theorem weakInductionOrbitPairEulerValues : WeakInductionOrbitPairEulerValuesStatement.{uF, uE, uV, uW} := by
  classical
  intro hOrbit F E _ _ _ _ _ _ _ _ σ hgen r r' m m' S S' T T' U P P' Q Q' hU h h'
  have hBC := hOrbit F E S'.isoClass T'.isoClass h'
  rw [← galoisOrbit_eq_of_conjugates σ hgen T' U hU] at hBC
  exact weakInductionPairEulerValues F E r r' m _ (fun _ => m') S S' T U P P' Q Q' h hBC

end Langlands.Automorphic.Unramified
