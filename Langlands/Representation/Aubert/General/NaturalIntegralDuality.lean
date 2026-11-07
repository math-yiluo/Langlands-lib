import Langlands.Representation.Aubert.General.RationalInductionDualityReduction

/-!
# Natural integral duality of normalized induction on all smooth objects

For an actual semidirect decomposition `P = M ⋉ U`, write `i` for normalized induction
`normalizedInductionFunctor h hU` and `D` for the smooth contragredient. Renard 2026,
III.2.7 (printed p.78, PDF p.84), identifies `Ind_P^G(W~)` with the smooth dual of
`ind_P^G(W ⊗ δ_{P\G})` through the integral over `P\G` of the coefficient pairing; when
`P\G` is compact and `i` is normalized by `δ_P^{1/2}`, this is a natural isomorphism
`(i A)~ ≅ i(A~)`.

`IsIntegralDuality` asks for one such integral-characterized equivalence for every smooth
`A`, with no admissibility hypothesis, the integral taken over a subgroup `K` against a
measure `μ`. `IsNaturalIntegralDuality` says that a natural isomorphism
`C : i.op ⋙ D ≅ D ⋙ i` is characterized by the same integral. The theorem
`exists_isNaturalIntegralDuality` packages the first into the second.
-/

noncomputable section

open CategoryTheory MeasureTheory

namespace Langlands.Aubert.General

universe uG uV

variable {G : Type uG} [Group G] [TopologicalSpace G] [LocallyCompactSpace G]
  [NonarchimedeanGroup G]
variable {P M U : Subgroup G} (h : IsSemidirectDecomposition P M U) (hU : IsClosed (U : Set G))

/-- For every smooth `A` (not only admissible ones) there is an equivalence of the smooth
dual of `i(A)` with `i(A~)` characterized by the integral over `K`, against `μ`, of the
coefficient pairing. -/
def IsIntegralDuality (K : Subgroup G) [MeasurableSpace K] (μ : Measure K) : Prop :=
  ∀ A : SmoothRep.{0, uG, uV} ℂ M,
    ∃ E : Representation.Equiv
        ((normalizedInductionFunctor h hU).obj A).contragredient.representation
        ((normalizedInductionFunctor h hU).obj A.contragredient).representation,
      ∀ (ℓ : ((normalizedInductionFunctor h hU).obj A).contragredient)
        (f : (normalizedInductionFunctor h hU).obj A),
        smoothDualPairing ((normalizedInductionFunctor h hU).obj A).representation ℓ f =
          ∫ k : K, smoothDualPairing A.representation
            (Induction.eval P (inducingRepresentation h hU A.contragredient) (E ℓ) k)
            (Induction.eval P (inducingRepresentation h hU A) f k) ∂μ

/-- The natural isomorphism `C : i.op ⋙ D ≅ D ⋙ i`, with components `(i A)~ ≅ i(A~)`, is
characterized by the integral over `K`, against `μ`, of the coefficient pairing:
`⟨ℓ, f⟩ = ∫_K ⟨(C ℓ)(k), f(k)⟩ dμ(k)` for `ℓ ∈ (i A)~` and `f ∈ i A`. -/
def IsNaturalIntegralDuality (K : Subgroup G) [MeasurableSpace K] (μ : Measure K)
    (C : (normalizedInductionFunctor.{uG, uV} h hU).op ⋙
        SmoothRep.contragredientFunctor.{0, uG, max uG uV} ≅
      SmoothRep.contragredientFunctor.{0, uG, uV} ⋙ normalizedInductionFunctor.{uG, uV} h hU) :
    Prop :=
  ∀ (A : SmoothRep.{0, uG, uV} ℂ M)
    (ℓ : ((normalizedInductionFunctor h hU).obj A).contragredient)
    (f : (normalizedInductionFunctor h hU).obj A),
    smoothDualPairing ((normalizedInductionFunctor h hU).obj A).representation ℓ f =
      ∫ k : K, smoothDualPairing A.representation
        (Induction.eval P (inducingRepresentation h hU A.contragredient)
          (SmoothRep.hom (C.hom.app (Opposite.op A)) ℓ) k)
        (Induction.eval P (inducingRepresentation h hU A) f k) ∂μ

/-- Integral-characterized equivalences on all smooth objects assemble into a natural
isomorphism `i.op ⋙ D ≅ D ⋙ i` characterized by the same integral. Naturality follows
from the integral formula and nondegeneracy of the duality pairing. -/
theorem exists_isNaturalIntegralDuality (K : Subgroup G) [MeasurableSpace K] (μ : Measure K)
    (hdual : IsIntegralDuality.{uG, uV} h hU K μ) :
    ∃ C, IsNaturalIntegralDuality.{uG, uV} h hU K μ C := by
  choose E hE using hdual
  refine ⟨NatIso.ofComponents (fun X => SmoothRep.mkIso
    (A := ((normalizedInductionFunctor h hU).obj X.unop).contragredient)
    (B := (normalizedInductionFunctor h hU).obj X.unop.contragredient) (E X.unop)) ?_,
    fun A ℓ f => hE A ℓ f⟩
  intro X Y f
  apply ObjectProperty.hom_ext
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro (ℓ : ((normalizedInductionFunctor h hU).obj X.unop).contragredient)
  have hEY := hE Y.unop
  have hEX := hE X.unop
  change E Y.unop (contragredientMap
      (SmoothRep.hom ((normalizedInductionFunctor h hU).map f.unop)) ℓ) =
    SmoothRep.hom ((normalizedInductionFunctor h hU).map (SmoothRep.contragredientHom f.unop))
      (E X.unop ℓ)
  rw [← (E Y.unop).apply_symm_apply
    (SmoothRep.hom ((normalizedInductionFunctor h hU).map (SmoothRep.contragredientHom f.unop))
      (E X.unop ℓ))]
  congr 1
  apply Subtype.ext
  apply LinearMap.ext
  intro x
  change smoothDualPairing ((normalizedInductionFunctor h hU).obj X.unop).representation ℓ
      (SmoothRep.hom ((normalizedInductionFunctor h hU).map f.unop) x) =
    smoothDualPairing ((normalizedInductionFunctor h hU).obj Y.unop).representation
      ((E Y.unop).symm (SmoothRep.hom
        ((normalizedInductionFunctor h hU).map (SmoothRep.contragredientHom f.unop))
        (E X.unop ℓ))) x
  rw [hEY, (E Y.unop).apply_symm_apply, hEX]
  rfl

/-- Integral-characterized equivalences in the form of `Induction.exists_integralDualEquiv`,
one for every smooth `A`, give `IsIntegralDuality`. -/
theorem isIntegralDuality_of_twistEquiv (K : Subgroup G) [MeasurableSpace K] (μ : Measure K)
    (hE : ∀ A : SmoothRep.{0, uG, uV} ℂ M,
      ∃ E : Representation.Equiv
          (smoothContragredient (Induction.smoothInduced P (inducingRepresentation h hU A)))
          (Induction.smoothInduced P
            (Langlands.twist (HaarModulus.closedHalfCharacter U hU P h.le_normalizer)
              ((smoothContragredient A.representation).comp h.projection))),
        ∀ (ℓ : SmoothDual (Induction.smoothInduced P (inducingRepresentation h hU A)))
          (f : Induction.SmoothFunctions P (inducingRepresentation h hU A)),
          smoothDualPairing _ ℓ f =
            ∫ k : K, smoothDualPairing A.representation
              (Induction.eval P _ (E ℓ) k) (Induction.eval P _ f k) ∂μ) :
    IsIntegralDuality.{uG, uV} h hU K μ := by
  intro A
  obtain ⟨E, hE⟩ := hE A
  exact exists_functorEquiv_of_twistEquiv h hU K μ A E hE

end Langlands.Aubert.General
