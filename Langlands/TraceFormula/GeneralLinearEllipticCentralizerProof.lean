import Langlands.TraceFormula.GeneralLinearEllipticCentralizerStatement
import Langlands.TraceFormula.AdelicRegularCentralizerCompact
import Langlands.TraceFormula.AdelicRegularConjugacy
import Langlands.TraceFormula.GeneralLinearTwistedEllipticCentralizerReduction
import Mathlib.Algebra.Polynomial.Eval.Irreducible

/-! # The elliptic centralizer quotient and orbit function for `GL_n` -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField MeasureTheory Topology
open scoped CategoryTheory.MonObj
open Langlands.Global Langlands.Global.AdelicGroupPoints Langlands.GroupScheme
open Langlands.JacquetLanglands Langlands.QuotientIntegration

namespace Langlands.TraceFormula

private theorem compactCentralizerQuotient_of_equiv {G G' : Type*} [Group G] [Group G']
    [TopologicalSpace G] [TopologicalSpace G']
    (e : G ≃ₜ* G') (Γ : Subgroup G) (Γ' : Subgroup G')
    (hΓ : ∀ x, e x ∈ Γ' ↔ x ∈ Γ) (r : G)
    (h : IsCompactTwistedCentralizerQuotient Γ' (ContinuousMulEquiv.refl _) (e r)) :
    IsCompactTwistedCentralizerQuotient Γ (ContinuousMulEquiv.refl _) r := by
  let C := twistedCentralizer (MonoidHom.id G) r
  let C' := twistedCentralizer (MonoidHom.id G') (e r)
  let eC : C ≃ₜ* C' := subgroupContinuousMulEquiv e C C' (fun x => by
    change (e x)⁻¹ * e r * e x = e r ↔ x⁻¹ * r * x = r
    rw [← map_inv, ← map_mul, ← map_mul, e.injective.eq_iff])
  let eQ : LeftQuotient (Γ.subgroupOf C) ≃ₜ LeftQuotient (Γ'.subgroupOf C') :=
    Homeomorph.Quotient.congr eC.toHomeomorph (by
      intro x y
      rw [QuotientGroup.rightRel_apply, QuotientGroup.rightRel_apply]
      change y.val * x.val⁻¹ ∈ Γ ↔ e y.val * (e x.val)⁻¹ ∈ Γ'
      rw [← map_inv, ← map_mul]
      exact (hΓ _).symm)
  let : CompactSpace (LeftQuotient (Γ'.subgroupOf C')) := h
  exact eQ.symm.compactSpace

private theorem isClosed_conjugacyOrbit_of_equiv {G G' : Type*} [Group G] [Group G']
    [TopologicalSpace G] [TopologicalSpace G'] (e : G ≃ₜ* G') (r : G)
    (h : IsClosed (Set.range (fun z : G' => z⁻¹ * e r * z))) :
    IsClosed (Set.range (fun z : G => z⁻¹ * r * z)) := by
  have he : Set.range (fun z : G => z⁻¹ * r * z) =
      e ⁻¹' (Set.range (fun z : G' => z⁻¹ * e r * z)) := by
    refine Set.ext fun x => ?_
    change (∃ z : G, z⁻¹ * r * z = x) ↔ ∃ z : G', z⁻¹ * e r * z = e x
    constructor
    · rintro ⟨z, rfl⟩
      exact ⟨e z, by rw [map_mul, map_mul, map_inv]⟩
    · rintro ⟨z, hz⟩
      obtain ⟨y, rfl⟩ := e.surjective z
      exact ⟨y, e.injective (by simpa only [map_mul, map_inv] using hz)⟩
  rw [he]
  exact h.preimage e.continuous

private local instance (F : Type u) [Field F] (n : ℕ) :
    IsAffine (GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of F)).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme (Fin n) (CommRingCat.of F)

private local instance (F : Type u) [Field F] (n : ℕ) :
    Smooth (GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of F)).X.hom :=
  GroupScheme.GeneralLinear.smoothStatement (Fin n) (CommRingCat.of F)

set_option hygiene false in
local notation "GLₙ" => GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of F)

set_option maxRecDepth 2000 in
set_option maxHeartbeats 2000000 in
/-- The rational quotient of the norm-one centralizer has finite volume, and the orbit
function of a continuous compactly supported test function is integrable. -/
theorem generalLinearEllipticCentralizer : GeneralLinearEllipticCentralizerStatement.{u} := by
  intro F _ _ n v r hlocal
  let G := normOneSubgroup F GLₙ
  let Γ := rationalNormOneSubgroup F GLₙ
  let e := GeneralLinearGroupPoints.normOneAdelicHomeomorph F n
  let e₀ := GeneralLinearGroupPoints.rationalEquiv F n
  have he (q : RationalGroupPoints F GLₙ) :
      e (rationalNormOne F GLₙ q) = adelicDeterminantNormOnePoint F n (e₀ q) :=
    Subtype.ext (GeneralLinearGroupPoints.adelicHomeomorph_rational F n q)
  have hΓ (x : G) : e x ∈ adelicDeterminantNormOneRational F n ↔ x ∈ Γ := by
    constructor
    · intro hx
      change (e x).val ∈ (AdelicGL.rational F n).range at hx
      obtain ⟨g, hg⟩ := hx
      obtain ⟨q, hq⟩ := e₀.surjective g
      refine ⟨q, e.injective ?_⟩
      rw [he, hq]
      exact Subtype.ext hg
    · rintro ⟨q, rfl⟩
      exact ⟨e₀ q, (congrArg Subtype.val (he q)).symm⟩
  obtain ⟨q, hq⟩ := r.property
  let g := e₀ q
  have hr : e r.val = adelicDeterminantNormOnePoint F n g := by rw [← hq, he]
  change IsRegularElliptic (FiniteAdelicGL.localProjection F n v
    (AdelicGL.finite F n (e r.val).val)) at hlocal
  rw [hr] at hlocal
  let f := algebraMap F (FiniteCompletion F v)
  change (g.val.map f).charpoly.Separable ∧ Irreducible (g.val.map f).charpoly at hlocal
  rw [Matrix.charpoly_map] at hlocal
  have hsep : g.val.charpoly.Separable := (Polynomial.separable_map f).mp hlocal.1
  have hirr : Irreducible g.val.charpoly :=
    Polynomial.Monic.irreducible_of_irreducible_map f _ g.val.charpoly_monic hlocal.2
  have hn : n ≠ 0 := by simpa using hirr.natDegree_pos.ne'
  let θ := ContinuousMulEquiv.refl G
  have hc : IsCompactTwistedCentralizerQuotient Γ θ r.val := by
    apply compactCentralizerQuotient_of_equiv e Γ (adelicDeterminantNormOneRational F n) hΓ
    rw [hr]
    exact adelicRegularCentralizerCompactQuotient F n g hirr hsep
  have ho : IsClosed (TwistedOrbit θ r.val) := by
    change IsClosed (Set.range (fun z : G => z⁻¹ * r.val * z))
    apply isClosed_conjugacyOrbit_of_equiv e
    exact isClosed_normOneRationalConjugacyOrbit F n hn g hsep (e r.val) (congrArg Subtype.val hr)
  let : SecondCountableTopology G := AdelicGroupPoints.normOneSecondCountableTopology F GLₙ
  let : LocallyCompactSpace G := AdelicGroupPoints.normOneLocallyCompactSpace F GLₙ
  let : SigmaCompactSpace G := sigmaCompactSpace_of_locallyCompact_secondCountable
  obtain ⟨hvol, hInt⟩ := twistedCentralizerAnalyticConditions_of_compact_closed Γ θ r.val hc ho
  intro mC bC mΓC bΓC μC hright hfinite hopen νC νΓC hνC hνΓC
  exact ⟨@hvol mΓC bΓC μC hright hfinite hopen νΓC hνΓC,
    @hInt mC bC μC hright hfinite hopen νC hνC⟩

end Langlands.TraceFormula
