import Langlands.TraceFormula.GroupSchemeTwistCuspidalInvarianceStatement
import Langlands.Global.AdelicSubgroupQuotientTransport

/-! # Twisting preserves the full almost-everywhere cuspidal subspace -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField MeasureTheory
open scoped CategoryTheory.MonObj
open Langlands.Global Langlands.Global.AdelicGroupPoints
open Langlands.Global.PositiveRealTorus Langlands.GroupScheme
open Langlands.Automorphic.GroupSchemeFunctions Langlands.QuotientIntegration

namespace Langlands.TraceFormula

section ParabolicTransport

variable {F : Type u} [Field F] {G : GroupScheme (Spec (CommRingCat.of F))}

/-- Image of a proper rational parabolic and its canonical radical under the inverse. -/
private theorem exists_parabolic_radical_image (hPD : ParabolicDynamicStatement.{u})
    (hG : IsConnectedReductive G) (α : G ≅ G) (P : ProperRationalParabolic G) :
    ∃ P' : ProperRationalParabolic G,
      properRationalParabolicRadicals hPD hG P =
        (properRationalParabolicRadicals hPD hG P').comap α.inv := by
  obtain ⟨P₀, U₀, p, r, hp, hP, hr, hU⟩ := rationalParabolicRadical_spec hPD hG P.val
  have hproper : SubgroupFunctor.range (p ≫ α.inv) ≠ ⊤ := by
    intro htop
    have heq : P.val.val.comap α.hom = ⊤ := by
      rw [← hP]
      exact (SubgroupFunctor.range_comp_iso p α.symm).symm.trans htop
    apply P.property
    simpa only [← SubgroupFunctor.comap_comp, Iso.inv_hom_id, SubgroupFunctor.comap_id,
      SubgroupFunctor.comap_top] using
      congrArg (fun W : SubgroupFunctor G => W.comap α.inv) heq
  let P' : ProperRationalParabolic G :=
    ⟨⟨SubgroupFunctor.range (p ≫ α.inv), ⟨P₀, p ≫ α.inv, hp.comp_iso α.symm, rfl⟩⟩, hproper⟩
  have hrad : properRationalParabolicRadicals hPD hG P' =
      (properRationalParabolicRadicals hPD hG P).comap α.hom := by
    change rationalParabolicRadical hPD hG P'.val = (rationalParabolicRadical hPD hG P.val).comap _
    rw [rationalParabolicRadical_eq hPD hG P'.val (hp.comp_iso α.symm) rfl hr,
      ← Category.assoc, SubgroupFunctor.range_comp_iso (r ≫ p) α.symm, hU]
    rfl
  exact ⟨P', by rw [hrad, ← SubgroupFunctor.comap_comp, Iso.inv_hom_id, SubgroupFunctor.comap_id]⟩

end ParabolicTransport

open AdelicSubgroupPoints in
/-- A comparison on representatives gives convergence and integral transport on the quotients. -/
private theorem period_integrals_transport (F : Type u) [Field F] [NumberField F]
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffine G.X.left]
    [LocallyOfFiniteType G.X.hom]
    {U V : SubgroupFunctor G}
    [IsClosed (adelicPoints F G U : Set (AdelicGroupPoints F G))]
    [IsClosed (adelicPoints F G V : Set (AdelicGroupPoints F G))]
    [CompactSpace (RationalQuotient F G V)]
    (β : G ≅ G) (hU : U = V.comap β.hom)
    {f : RationalQuotient F G U → ℂ} {f' : RationalQuotient F G V → ℂ}
    (hfg : ∀ (n : adelicPoints F G U) (n' : adelicPoints F G V),
      (n' : AdelicGroupPoints F G) = AdelicGroupPoints.map F G G β.hom n →
        f (LeftCosetSpace.mk _ n) = f' (LeftCosetSpace.mk _ n')) :
    (Integrable f (normalizedRationalQuotientHaarMeasure F G U) ↔
      Integrable f' (normalizedRationalQuotientHaarMeasure F G V)) ∧
    (∫ q, f q ∂normalizedRationalQuotientHaarMeasure F G U) =
      ∫ q, f' q ∂normalizedRationalQuotientHaarMeasure F G V := by
  subst U
  have heq : f = f' ∘ rationalQuotientIso F β V := by
    funext q
    induction q using Quotient.inductionOn with
    | _ n =>
      exact hfg n (adelicSubgroupIso F β V n) rfl
  rw [heq]
  exact ⟨integrable_comp_rationalQuotientIso_iff F β V f',
    integral_comp_rationalQuotientIso F β V f'⟩

/-- Inverse adelic pullback preserves the full almost-everywhere cuspidal subspace. -/
theorem groupSchemeTwistCuspidalInvariance : GroupSchemeTwistCuspidalInvarianceStatement.{u} := by
  intro F _ _ G _ _ hPD hG T i hi _ I _ e hc α Θ hα hΘ hΘμ φ hφ
  let Γ := positiveRationalSubgroup F G T i
  let μQ := positiveRationalQuotientHaarMeasure F G T i
  let μG := (Measure.haar : Measure (normOneSubgroup F G))
  let ψ : PositiveRationalQuotient F G T i → ℂ :=
    fun q => φ ((quotientAutomorphism Γ Θ hΘ).symm q)
  apply (mem_aeParabolicCuspidalFunctionSubmodule_congr F G hPD hG T i hi I e hc
    (twistOperator Γ Θ hΘ μQ hΘμ φ) ψ (Lp.stronglyMeasurable _)
    ((Lp.stronglyMeasurable φ).comp_measurable hΘμ.measurable)
    (twistOperator_coeFn Γ Θ hΘ μQ hΘμ φ)).mpr
  have hinv (x : AdelicGroupPoints F G) :
      Θ.symm x = AdelicGroupPoints.map F G G α.inv x := by
    apply Θ.injective
    rw [Θ.apply_symm_apply, hα]
    simp only [AdelicGroupPoints.map_apply, GroupScheme.affinePointsTarget_apply,
      Category.assoc, ← Grp.comp_hom_hom, Iso.inv_hom_id, Grp.id_hom_hom, Category.comp_id]
  have hnorm (x : AdelicGroupPoints F G) :
      Θ.symm x ∈ normOneSubgroup F G ↔ x ∈ normOneSubgroup F G := by
    constructor
    · intro hx
      have hy : Θ (Θ.symm x) ∈ normOneSubgroup F G := by
        rw [hα]
        exact map_normOneSubgroup_le F G G α.hom ⟨Θ.symm x, hx, rfl⟩
      simpa only [Θ.apply_symm_apply] using hy
    · intro hx
      rw [hinv]
      exact map_normOneSubgroup_le F G G α.inv ⟨x, hx, rfl⟩
  let normOneEquiv := subgroupAutomorphism (normOneSubgroup F G) Θ.symm hnorm
  have hnormAE : Measure.QuasiMeasurePreserving normOneEquiv μG μG := by
    have : (Measure.map normOneEquiv μG).IsHaarMeasure := normOneEquiv.isHaarMeasure_map μG
    exact ⟨normOneEquiv.continuous.measurable, Measure.absolutelyContinuous_isHaarMeasure _ _⟩
  intro P
  obtain ⟨P', hP'⟩ := exists_parabolic_radical_image hPD hG α P
  have htransport (g : normOneSubgroup F G) :=
    period_integrals_transport F α.symm hP'
      (f := properParabolicPositivePeriodIntegrand F G hPD hG T i P ψ g)
      (f' := properParabolicPositivePeriodIntegrand F G hPD hG T i P' φ (normOneEquiv g))
      (fun n n' hn' => by
        rw [properParabolicPositivePeriodIntegrand_mk, properParabolicPositivePeriodIntegrand_mk]
        change φ ((quotientAutomorphism Γ Θ hΘ).symm (Quotient.mk _ (n.val * g.val))) = _
        have hn : (n' : AdelicGroupPoints F G) = Θ.symm n := hn'.trans (hinv n).symm
        rw [quotientAutomorphism_symm_mk, map_mul, ← hn]
        rfl)
  obtain ⟨hconv, hvanish⟩ := hφ P'
  refine ⟨?_, ?_⟩
  · filter_upwards [QuasiMeasurePreserving.ae hnormAE hconv] with g hg
    exact (htransport g).1.mpr hg
  · filter_upwards [QuasiMeasurePreserving.ae hnormAE hvanish] with g hg
    exact (htransport g).2.trans hg

end Langlands.TraceFormula
