import Langlands.TraceFormula.GeneralLinearSimpleTraceFormulaStatement
import Langlands.TraceFormula.AbstractSimpleTwistedProof
import Langlands.TraceFormula.PositiveQuotientTraceComparisonProof
import Langlands.TraceFormula.GroupSchemeFullL2TraceClassProof
import Langlands.TraceFormula.GeneralLinearEllipticClassFinitenessProof
import Langlands.TraceFormula.GeneralLinearEllipticCentralizerProof
import Langlands.TraceFormula.GeneralLinearTensorSimpleTraceFormulaReduction
import Langlands.TraceFormula.PositiveAverageOrbitSupport
import Langlands.TraceFormula.QuotientRightRegular
import Langlands.TraceFormula.TwistedSupportCompact

/-!
# Proof of the simple trace formula for `GL_n` over a number field

`generalLinearSimpleTraceFormula` proves `GeneralLinearSimpleTraceFormulaStatement`. The trace
class property is `groupSchemeFullL2TraceClass`; the passage to the norm-one quotient is
`positiveQuotientTraceComparison` with the right regular representation `quotientRightRegular`;
the finite family of rational classes comes from `positiveAverageOrbitSupport` and
`generalLinearEllipticClassFiniteness`; the volumes and orbit functions are controlled by
`generalLinearEllipticCentralizer`; the support hypothesis of the abstract formula is
`exists_isCompact_twistedSupport`, fed by the compact centralizer quotients and closed orbits of
regular elliptic elements; and the identity is `abstractSimpleTwistedTraceFormula` with the
trivial twist.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField MeasureTheory Filter
open scoped CategoryTheory.MonObj CompactlySupported
open Langlands.Global Langlands.Global.AdelicGroupPoints
open Langlands.Global.PositiveRealTorus Langlands.GroupScheme
open Langlands.Automorphic.GroupSchemeFunctions
open Langlands.QuotientIntegration Langlands.JacquetLanglands
open Langlands.Analysis.OperatorIdeals

namespace Langlands.TraceFormula

attribute [local instance] generalLinearSimpleTraceIsAffine generalLinearSimpleTraceSmooth

set_option hygiene false in
local notation "GLₙ" => GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of F)

/-- Regular ellipticity is invariant under conjugation. -/
theorem isRegularElliptic_conj_iff {K : Type*} [Field K] {n : ℕ}
    (x g : GeneralLinear n K) :
    IsRegularElliptic (x⁻¹ * g * x) ↔ IsRegularElliptic g := by
  have h : (x⁻¹ * g * x).val.charpoly = g.val.charpoly := by
    simpa only [Units.val_mul, Matrix.coe_units_inv] using Matrix.charpoly_units_conj' x g.val
  unfold IsRegularElliptic IsRegularSemisimple
  rw [h]

/-- The component at a finite place `v` of a point of `GL_n(𝔸_F)`, read through the matrix
model, depends only on the group-scheme point at `v`. -/
theorem localProjection_finite_adelicHomeomorph_congr (F : Type u) [Field F] [NumberField F]
    (n : ℕ) (v : Langlands.Global.FinitePlace F) {y z : AdelicGroupPoints F GLₙ}
    (h : atPlace F GLₙ (.inr v) y = atPlace F GLₙ (.inr v) z) :
    FiniteAdelicGL.localProjection F n v
        (AdelicGL.finite F n (GeneralLinearGroupPoints.adelicHomeomorph F n y)) =
      FiniteAdelicGL.localProjection F n v
        (AdelicGL.finite F n (GeneralLinearGroupPoints.adelicHomeomorph F n z)) := by
  have key (w : AdelicGroupPoints F GLₙ) (a b : Fin n) :
      (FiniteAdelicGL.localProjection F n v
        (AdelicGL.finite F n (GeneralLinearGroupPoints.adelicHomeomorph F n w)) :
          Matrix (Fin n) (Fin n) (FiniteCompletion F v)) a b =
        (GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of F)).affinePointEvaluation
          (placeCompletion F (.inr v)) (atPlace F GLₙ (.inr v) w)
          (GroupScheme.GeneralLinear.entrySection (Fin n) (CommRingCat.of F) a b) := by
    rw [atPlace_evaluation, adeleProjection_inr, FiniteAdelicGL.localProjection_apply,
      AdelicGL.finite_apply]
    change ((GroupScheme.GeneralLinear.affinePointsEquiv (Fin n) (CommRingCat.of F)
      (CommAlgCat.of F (AdeleRing (𝓞 F) F)) w) a b).2 v = _
    rw [GroupScheme.GeneralLinear.affinePointsEquiv_entry_evaluation]
  apply Units.ext
  ext a b
  rw [key, key, h]

/-- Regular ellipticity at a finite place is invariant under conjugation in `GL_n(𝔸_F)¹`. -/
theorem isRegularElliptic_localProjection_normOne_conj_iff (F : Type u) [Field F]
    [NumberField F] (n : ℕ) (v : Langlands.Global.FinitePlace F) (x g : normOneSubgroup F GLₙ) :
    IsRegularElliptic (FiniteAdelicGL.localProjection F n v
        (AdelicGL.finite F n (GeneralLinearGroupPoints.adelicHomeomorph F n
          ((x⁻¹ * g * x : normOneSubgroup F GLₙ) : AdelicGroupPoints F GLₙ)))) ↔
      IsRegularElliptic (FiniteAdelicGL.localProjection F n v
        (AdelicGL.finite F n (GeneralLinearGroupPoints.adelicHomeomorph F n
          (g : AdelicGroupPoints F GLₙ)))) := by
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv]
  exact isRegularElliptic_conj_iff _ _

private theorem compactSubgroupOfQuotient_of_equiv {G G' : Type*} [Group G] [Group G']
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

private theorem isClosed_conjugationOrbit_of_equiv {G G' : Type*} [Group G] [Group G']
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

/-- A rational norm-one point of `GL_n` that is regular elliptic at a finite place has a closed
conjugacy orbit in `GL_n(𝔸_F)¹`, and the rational points of its centralizer have compact quotient
in the centralizer. -/
theorem generalLinearNormOne_compact_closed (F : Type u) [Field F] [NumberField F] (n : ℕ)
    (v : Langlands.Global.FinitePlace F) (r : rationalNormOneSubgroup F GLₙ)
    (hlocal : IsRegularElliptic (FiniteAdelicGL.localProjection F n v
      (AdelicGL.finite F n (GeneralLinearGroupPoints.adelicHomeomorph F n
        ((r : normOneSubgroup F GLₙ) : AdelicGroupPoints F GLₙ))))) :
    IsCompactTwistedCentralizerQuotient (rationalNormOneSubgroup F GLₙ)
        (ContinuousMulEquiv.refl (normOneSubgroup F GLₙ)) (r : normOneSubgroup F GLₙ) ∧
      IsClosed (TwistedOrbit (ContinuousMulEquiv.refl (normOneSubgroup F GLₙ))
        (r : normOneSubgroup F GLₙ)) := by
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
  refine ⟨?_, ?_⟩
  · apply compactSubgroupOfQuotient_of_equiv e Γ (adelicDeterminantNormOneRational F n) hΓ
    rw [hr]
    exact adelicRegularCentralizerCompactQuotient F n g hirr hsep
  · change IsClosed (Set.range (fun z : G => z⁻¹ * r.val * z))
    apply isClosed_conjugationOrbit_of_equiv e
    exact isClosed_normOneRationalConjugacyOrbit F n hn g hsep (e r.val) (congrArg Subtype.val hr)

set_option maxHeartbeats 1000000 in
/-- The simple trace formula for `GL_n` over a number field. -/
theorem generalLinearSimpleTraceFormula : GeneralLinearSimpleTraceFormulaStatement.{u} := by
  classical
  intro F _ _ n hPD hG T i hi _ I _ e hc _ μG f₁ f₂ hHS₁ hHS₂ hrad f v hell fOne
  let G₁ := normOneSubgroup F GLₙ
  let Γ := rationalNormOneSubgroup F GLₙ
  let ν := normOneRationalQuotientHaarMeasure F GLₙ
  let : SigmaCompactSpace G₁ := sigmaCompactSpace_of_locallyCompact_secondCountable
  have hνc : IsCompatible Γ (Measure.haar : Measure G₁) Measure.count ν :=
    normOneRationalQuotientHaarMeasure_isCompatible F GLₙ
  -- the convolution as a compactly supported continuous function
  have hfc : Continuous f := Langlands.Analysis.continuous_convolution_compactlySupported μG f₁ f₂
  have hfs : HasCompactSupport f :=
    Langlands.Analysis.hasCompactSupport_convolution_compactlySupported μG f₁ f₂
  let fc : C_c(AdelicGroupPoints F GLₙ, ℂ) := ⟨⟨f, hfc⟩, hfs⟩
  -- trace class on the positive quotient
  obtain ⟨h, htc⟩ := groupSchemeFullL2TraceClass F GLₙ hPD hG T i hi I e hc f₁ f₂ hHS₁ hHS₂ hrad
  -- the right regular representation on the norm-one quotient
  let π := quotientRightRegular Γ ν hνc.right_invariant
  have hπnorm := norm_quotientRightRegular_apply Γ ν hνc.right_invariant
  have hπmeas := aestronglyMeasurable_quotientRightRegular_apply Γ ν hνc.right_invariant
    (Measure.haar : Measure G₁)
  have hπae := quotientRightRegular_coeFn Γ ν hνc.right_invariant
  -- passage to the norm-one quotient
  obtain ⟨hOc, hOs, hcmp⟩ := positiveQuotientTraceComparison F GLₙ T i hi I e hc fc
  let fOneC : C_c(G₁, ℂ) := ⟨⟨fOne, hOc⟩, hOs⟩
  have hOne : Integrable fOne (Measure.haar : Measure G₁) :=
    fOneC.continuous.integrable_of_hasCompactSupport fOneC.hasCompactSupport
  obtain ⟨hcmp₁, hcmp₂⟩ := hcmp h hOne π hπnorm hπmeas hπae
  -- the twist is trivial
  let θ := ContinuousMulEquiv.refl G₁
  have hθΓ : ∀ x : G₁, θ x ∈ Γ ↔ x ∈ Γ := fun _ => Iff.rfl
  have hθid : ((quotientAutomorphism Γ θ hθΓ).symm : LeftQuotient Γ → LeftQuotient Γ) = id := by
    funext q
    induction q using Quotient.inductionOn with
    | h x => rfl
  have hθν : MeasurePreserving (quotientAutomorphism Γ θ hθΓ).symm ν ν := by
    rw [hθid]
    exact MeasurePreserving.id ν
  have htwist : twistOperator Γ θ hθΓ ν hθν = ContinuousLinearMap.id ℂ (Lp ℂ 2 ν) := by
    refine ContinuousLinearMap.ext fun φ => Lp.ext ((twistOperator_coeFn Γ θ hθΓ ν hθν φ).trans
      (Eventually.of_forall fun q => ?_))
    rw [hθid]
    rfl
  -- the support of `fOne`
  obtain ⟨Ω₁, hΩ₁, hΩ₁pt, hΩ₁f⟩ := positiveAverageOrbitSupport F GLₙ T i hi I e (tsupport f) hfs
  have hval : ∀ z : G₁, fOne z ≠ 0 → z ∈ Ω₁ := fun z hz =>
    ((hΩ₁f (normalizedPositiveHaarMeasure F GLₙ T i hi I e hc) f (subset_tsupport f)).1 z hz).1
  have hΩ₁ell : ∀ z ∈ Ω₁, IsRegularElliptic (FiniteAdelicGL.localProjection F n v
      (AdelicGL.finite F n (GeneralLinearGroupPoints.adelicHomeomorph F n
        (z : AdelicGroupPoints F GLₙ)))) := by
    intro z hz
    obtain ⟨y, hy, hyz⟩ := hΩ₁pt z hz
    rw [← localProjection_finite_adelicHomeomorph_congr F n v (hyz v)]
    exact hell y hy
  -- finiteness of the rational classes meeting the support
  obtain ⟨R, hR⟩ := generalLinearEllipticClassFiniteness F n v
    (GeneralLinearGroupPoints.adelicHomeomorph F n ''
      ((Subtype.val : G₁ → AdelicGroupPoints F GLₙ) '' Ω₁))
    ((hΩ₁.image continuous_subtype_val).image
      (GeneralLinearGroupPoints.adelicHomeomorph F n).continuous)
    (by
      rintro _ ⟨_, ⟨z, hz, rfl⟩, rfl⟩
      exact hΩ₁ell z hz)
  let e₀ := GeneralLinearGroupPoints.rationalEquiv F n
  let ψ : RationalGL F n →* Γ := (rationalNormOne F GLₙ).rangeRestrict.comp e₀.symm.toMonoidHom
  have hψ (g₀ : RationalGL F n) : GeneralLinearGroupPoints.adelicHomeomorph F n
      (((ψ g₀ : Γ) : G₁) : AdelicGroupPoints F GLₙ) = AdelicGL.rational F n g₀ := by
    change GeneralLinearGroupPoints.adelicHomeomorph F n
      (AdelicGroupPoints.rational F GLₙ (e₀.symm g₀)) = _
    rw [GeneralLinearGroupPoints.adelicHomeomorph_rational, MulEquiv.apply_symm_apply]
  have hψs : Function.Surjective ψ :=
    (MonoidHom.rangeRestrict_surjective _).comp e₀.symm.surjective
  let S : Set Γ := {q | ∃ x : G₁, fOne (x⁻¹ * (q : G₁) * x) ≠ 0}
  have hSfin : (ConjClasses.mk '' S).Finite := by
    refine (R.finite_toSet.image (fun r => ConjClasses.mk (ψ r))).subset ?_
    rintro _ ⟨q, ⟨x, hx⟩, rfl⟩
    obtain ⟨g₀, rfl⟩ := hψs q
    have hmem := hval _ hx
    obtain ⟨-, r, hr, y, hy⟩ := hR g₀ ⟨GeneralLinearGroupPoints.adelicHomeomorph F n
      (x : AdelicGroupPoints F GLₙ), by
        refine ⟨_, ⟨_, hmem, rfl⟩, ?_⟩
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv, hψ]⟩
    refine ⟨r, hr, ?_⟩
    change ConjClasses.mk (ψ r) = ConjClasses.mk (ψ g₀)
    rw [ConjClasses.mk_eq_mk_iff_isConj, isConj_iff]
    refine ⟨ψ y, ?_⟩
    rw [← hy]
    simp only [map_mul, map_inv]
    group
  -- representatives of the finitely many classes
  let P := hSfin.toFinset
  let m := P.card
  let enum : Fin m ≃ P := P.equivFin.symm
  choose rep hrepS hrepc using fun c : P => hSfin.mem_toFinset.1 c.2
  let r : Fin m → Γ := fun j => rep (enum j)
  have hrS (j : Fin m) : r j ∈ S := hrepS (enum j)
  have hrc (j : Fin m) : ConjClasses.mk (r j) = (enum j : ConjClasses Γ) := hrepc (enum j)
  have hpair : ∀ j k, IsTwistedConjugate Γ (MonoidHom.id G₁) (r j : G₁) (r k : G₁) → j = k := by
    rintro j k ⟨g, hg, hjk⟩
    apply enum.injective
    apply Subtype.ext
    rw [← hrc, ← hrc, ConjClasses.mk_eq_mk_iff_isConj, isConj_iff]
    refine ⟨(⟨g, hg⟩ : Γ)⁻¹, Subtype.ext ?_⟩
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, inv_inv]
    exact hjk
  have hrell : ∀ j, IsRegularElliptic (FiniteAdelicGL.localProjection F n v
      (AdelicGL.finite F n (GeneralLinearGroupPoints.adelicHomeomorph F n
        ((r j : G₁) : AdelicGroupPoints F GLₙ)))) := by
    intro j
    obtain ⟨x, hx⟩ := hrS j
    exact (isRegularElliptic_localProjection_normOne_conj_iff F n v x (r j : G₁)).1
      (hΩ₁ell _ (hval _ hx))
  have hcover : ∀ q ∈ Γ, (∃ x : G₁, fOne (x⁻¹ * q * x) ≠ 0) →
      ∃ j, IsTwistedConjugate Γ (MonoidHom.id G₁) (r j : G₁) q := by
    intro q hq hx
    let qq : Γ := ⟨q, hq⟩
    have hmem : ConjClasses.mk qq ∈ P := hSfin.mem_toFinset.2 ⟨qq, hx, rfl⟩
    obtain ⟨j, hj⟩ := enum.surjective ⟨_, hmem⟩
    refine ⟨j, ?_⟩
    have hjq : ConjClasses.mk (r j) = ConjClasses.mk qq := by rw [hrc, hj]
    obtain ⟨c, hcq⟩ := isConj_iff.1 (ConjClasses.mk_eq_mk_iff_isConj.1 hjq)
    refine ⟨((c⁻¹ : Γ) : G₁), (c⁻¹).2, ?_⟩
    have hcq' := congrArg (fun z : Γ => (z : G₁)) hcq
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at hcq'
    simp only [Subgroup.coe_inv, inv_inv]
    exact hcq'
  -- the geometric conditions on the representatives
  have hgeom (j : Fin m) := generalLinearNormOne_compact_closed F n v (r j) (hrell j)
  have hsupp := exists_isCompact_twistedSupport Γ θ (fun j => (r j : G₁))
    (fun j => (hgeom j).1) (fun j => (hgeom j).2) fOne hOs (fun q hq hx => hcover q hq hx)
  -- trace class on the norm-one quotient
  have htcOne : IsTraceClass ((Langlands.Analysis.integratedIsometricAction Measure.haar π hπnorm
      hπmeas fOneC (fOneC.continuous.integrable_of_hasCompactSupport
        fOneC.hasCompactSupport)).comp (twistOperator Γ θ hθΓ ν hθν)) := by
    rw [htwist, ContinuousLinearMap.comp_id]
    exact hcmp₁.1 htc
  refine ⟨h, htc, m, r, hpair, hrell, hcover, ?_⟩
  intro mC bC mΓC bΓC μC hright hfinite hopen νC νΓC hνC hνΓC
  have hcent (j : Fin m) := @generalLinearEllipticCentralizer F _ _ n v (r j) (hrell j)
    (mC j) (bC j) (mΓC j) (bΓC j) (μC j) (hright j) (hfinite j) (hopen j) (νC j) (νΓC j)
    (hνC j) (hνΓC j)
  have hvol : ∀ j, νΓC j Set.univ ≠ ⊤ := fun j => (hcent j).1
  have hint : ∀ j, Integrable (twistedOrbitFunction (MonoidHom.id G₁) (r j : G₁) fOne) (νC j) :=
    fun j => (hcent j).2 fOne fOneC.continuous fOneC.hasCompactSupport
  refine ⟨hvol, hint, ?_⟩
  have key := @abstractSimpleTwistedTraceFormula.{u} G₁ _ _ _ _ _ _ _ _ Measure.haar _ _ Γ _ _ _
    ν hνc θ hθΓ (MeasurePreserving.id _) hθν π hπnorm hπmeas hπae fOneC htcOne hsupp m r hpair
    hcover mC bC mΓC bΓC μC hright hfinite hopen νC νΓC hνC hνΓC hvol hint
  rw [htwist, ContinuousLinearMap.comp_id] at key
  exact (hcmp₂ htc).trans key

end Langlands.TraceFormula
