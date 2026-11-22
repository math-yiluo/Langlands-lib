import Langlands.Geometry.Analytic.AffineAnalytificationFiniteCharts
import Langlands.Geometry.Analytic.AffinoidPointRelation
import Langlands.Geometry.Analytic.FiniteBoundedMaps
import Langlands.Geometry.Analytic.FiniteEtaleAffinoidQuotient
import Langlands.Geometry.Analytic.LocalizedChartCoverLifts
import Langlands.Geometry.Analytic.SmallAffinoidFiniteEtaleReflection
import Langlands.Geometry.Analytic.SpaceAnalytificationAffinoidPointDescent

/-! # Kernel pairs and quotients of affinoid points -/

noncomputable section

universe u

namespace Langlands.Analytic.SpaceAnalytification

open _root_.CategoryTheory _root_.CategoryTheory.Limits Set
open _root_.AlgebraicGeometry
open Langlands.AlgebraicGeometry Langlands.AlgebraicGeometry.AlgebraicSpace
open Langlands.AlgebraicGeometry.PointTopology
open PresentedAffinoidAlgebra SaturatedAtlasPresentation
open AffineAnalytification.FiniteCharts (isFiniteBanach_of_finite)

variable {K : Type u} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]

local notation "M" => localizedAffinoidSpectrum (K := K)

private abbrev spectrumMap {A B : PresentedAffinoidAlgebra K} (f : BoundedAlgHom K A B) :
    M B ⟶ M A := SmallAffinoidSpectrum.localizedMapEquiv.{u, u} A B f

private theorem locallyRefines_univ_of_quasinet {T : Type u} [TopologicalSpace T]
    {σ : Set (Set T)} (hσ : AtlasTopology.IsQuasinet σ) :
    AtlasTopology.LocallyRefines σ {univ} := by
  intro W hW x _
  obtain rfl := mem_singleton_iff.mp hW
  obtain ⟨τ, hτ, hsub, hx, hn⟩ := hσ x
  exact ⟨τ, hτ, hsub, fun S hS => ⟨subset_univ _, hx S hS⟩,
    by simpa only [nhdsWithin_univ] using hn⟩

set_option backward.isDefEq.respectTransparency false in
private theorem isPullback_of_affinoid_tests
    {V X Y Z : LocalizedCategory.{u, u, u} (K := K)}
    {p : V ⟶ X} {q : V ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z} (hw : p ≫ f = q ≫ g)
    (h : ∀ (R : PresentedAffinoidAlgebra K) (a : M R ⟶ X) (b : M R ⟶ Y),
      a ≫ f = b ≫ g → ∃! l : M R ⟶ V, l ≫ p = a ∧ l ≫ q = b) :
    IsPullback p q f g := by
  have hmono (T : LocalizedCategory.{u, u, u} (K := K)) (l m : T ⟶ V)
      (hp : l ≫ p = m ≫ p) (hq : l ≫ q = m ≫ q) : l = m := by
    obtain ⟨S, hS⟩ := localizedObjectEquiv.surjective T
    change localizationFunctor.obj S = T at hS
    subst T
    apply localizedHom_ext_of_chartCover (fun i : S.presentation.atlas.Index => i)
      (locallyRefines_univ_of_quasinet S.presentation.atlas.isNet_chartFamily.1) l m
    intro i
    let j := localizationFunctor.map (S.smallChartSpectrumInclusion i)
    have hcond : (j ≫ l ≫ p) ≫ f = (j ≫ l ≫ q) ≫ g := by
      simp only [Category.assoc, hw]
    obtain ⟨a, ha, huniq⟩ := h _ (j ≫ l ≫ p) (j ≫ l ≫ q) hcond
    exact (huniq _ ⟨Category.assoc _ _ _, Category.assoc _ _ _⟩).trans
      (huniq _ ⟨(Category.assoc _ _ _).trans (congrArg (j ≫ ·) hp.symm),
        (Category.assoc _ _ _).trans (congrArg (j ≫ ·) hq.symm)⟩).symm
  have hLift (d : PullbackCone f g) :
      ∃ l : d.pt ⟶ V, l ≫ p = d.fst ∧ l ≫ q = d.snd := by
    obtain ⟨S, hS⟩ := localizedObjectEquiv.surjective d.pt
    let e : localizationFunctor.obj S ≅ d.pt := eqToIso hS
    obtain ⟨l, hlp, hlq⟩ := exists_lift_of_chartCover
      (fun i : S.presentation.atlas.Index => i)
      (locallyRefines_univ_of_quasinet S.presentation.atlas.isNet_chartFamily.1) p q hmono
      (e.hom ≫ d.fst) (e.hom ≫ d.snd) (fun i => by
        let j := localizationFunctor.map (S.smallChartSpectrumInclusion i) ≫ e.hom
        obtain ⟨l, hl, _⟩ := h _ (j ≫ d.fst) (j ≫ d.snd) (by
          rw [Category.assoc j, Category.assoc j, d.condition])
        exact ⟨l, hl.1.trans (Category.assoc _ _ _), hl.2.trans (Category.assoc _ _ _)⟩)
    refine ⟨e.inv ≫ l, ?_, ?_⟩
    · rw [Category.assoc, hlp, Iso.inv_hom_id_assoc]
    · rw [Category.assoc, hlq, Iso.inv_hom_id_assoc]
  exact IsPullback.of_isLimit (PullbackCone.IsLimit.mk hw
    (fun d => (hLift d).choose) (fun d => (hLift d).choose_spec.1)
    (fun d => (hLift d).choose_spec.2) (fun d m hl hr => hmono d.pt m _
      (hl.trans (hLift d).choose_spec.1.symm) (hr.trans (hLift d).choose_spec.2.symm)))

namespace AffinoidPointRelation

variable {X : AlgebraicSpace (Spec (CommRingCat.of K))} {A B : PresentedAffinoidAlgebra K}
  {f : BoundedAlgHom K A B} {x : RingPoints K X B} (V : AffinoidPointRelation f x)
  {Y : LocalizedCategory.{u, u, u} (K := K)} {p : PointFamily K X Y}
  (hp : IsAnalytification K X Y p) (hs : IsSeparated X) (ht : LocallyOfFiniteTypeOverBase X)

set_option backward.isDefEq.respectTransparency false in
/-- When the base is embedded in the analytic target, the affinoid relation
is the actual kernel pair of the point map into the analytification. -/
theorem localized_isPullback
    {Z : LocalizedCategory.{u, u, u} (K := K)} (F : Y ⟶ Z)
    (b : M A ⟶ Z) [Mono b]
    (hw : affinoidPointHom hp hs ht B x ≫ F = spectrumMap f ≫ b) :
    IsPullback (spectrumMap V.first) (spectrumMap V.second)
      (affinoidPointHom hp hs ht B x) (affinoidPointHom hp hs ht B x) := by
  apply isPullback_of_affinoid_tests
  · change localizationFunctor.map (SmallAffinoidSpectrum.map.{u, u} V.first) ≫
        affinoidPointHom hp hs ht B x =
      localizationFunctor.map (SmallAffinoidSpectrum.map.{u, u} V.second) ≫
        affinoidPointHom hp hs ht B x
    rw [← affinoidPointHom_changeRing hp hs ht V.first,
      ← affinoidPointHom_changeRing hp hs ht V.second, V.condition.2]
  intro R a₁ a₂ he
  obtain ⟨α, rfl⟩ := (SmallAffinoidSpectrum.localizedMapEquiv.{u, u} B R).surjective a₁
  obtain ⟨β, rfl⟩ := (SmallAffinoidSpectrum.localizedMapEquiv.{u, u} B R).surjective a₂
  change spectrumMap α ≫ affinoidPointHom hp hs ht B x =
    spectrumMap β ≫ affinoidPointHom hp hs ht B x at he
  have hpoint : RingPoints.changeRing α.toAlgHom x = RingPoints.changeRing β.toAlgHom x := by
    apply affinoidPointHom_injective hp hs ht R
    rw [affinoidPointHom_changeRing, affinoidPointHom_changeRing]
    exact he
  have hbase : α.comp f = β.comp f := by
    apply (SmallAffinoidSpectrum.localizedMapEquiv.{u, u} A R).injective
    apply (cancel_mono b).mp
    have h := congrArg (· ≫ F) he
    simp only [Category.assoc, hw] at h
    simpa only [SmallAffinoidSpectrum.localizedMapEquiv_comp.{u, u}, Category.assoc] using h
  obtain ⟨δ, h₁, h₂⟩ := (V.factors_iff α.toAlgHom β.toAlgHom).mpr
    ⟨congrArg BoundedAlgHom.toAlgHom hbase, hpoint⟩
  let ψ := BoundedAlgHom.ofFiniteTriangle V.first V.first_finite α δ h₁
  have hψ₁ : ψ.comp V.first = α :=
    BoundedAlgHom.ofFiniteTriangle_comp V.first V.first_finite α δ h₁
  have hψ₂ : ψ.comp V.second = β := BoundedAlgHom.ext fun b => AlgHom.congr_fun h₂ b
  refine ⟨spectrumMap ψ, ⟨?_, ?_⟩, ?_⟩
  · rw [← SmallAffinoidSpectrum.localizedMapEquiv_comp.{u, u} V.first ψ, hψ₁]
  · rw [← SmallAffinoidSpectrum.localizedMapEquiv_comp.{u, u} V.second ψ, hψ₂]
  intro l hl
  obtain ⟨γ, rfl⟩ := (SmallAffinoidSpectrum.localizedMapEquiv.{u, u} V.algebra R).surjective l
  apply congrArg (SmallAffinoidSpectrum.localizedMapEquiv.{u, u} V.algebra R)
  have hγ₁ : γ.comp V.first = ψ.comp V.first := by
    apply (SmallAffinoidSpectrum.localizedMapEquiv.{u, u} B R).injective
    rw [hψ₁, SmallAffinoidSpectrum.localizedMapEquiv_comp.{u, u}]
    exact hl.1
  have hγ₂ : γ.comp V.second = ψ.comp V.second := by
    apply (SmallAffinoidSpectrum.localizedMapEquiv.{u, u} B R).injective
    rw [hψ₂, SmallAffinoidSpectrum.localizedMapEquiv_comp.{u, u}]
    exact hl.2
  have hγ := FiniteLocallyFreeQuotient.QuotFLF.hom_ext V.generates
    (congrArg (fun r : BoundedAlgHom K B R => r.toAlgHom.toRingHom) hγ₁)
    (congrArg (fun r : BoundedAlgHom K B R => r.toAlgHom.toRingHom) hγ₂)
  exact BoundedAlgHom.ext (RingHom.congr_fun hγ)

/-- Over an algebraically finite étale map `A → B`, a finite relation with
analytically étale projections has an affinoid quotient with algebraically
finite étale base and cover maps. -/
def finiteEtaleQuotient (hf : f.AlgebraicallyFiniteEtale)
    (h₁ : etale (spectrumMap V.first)) (h₂ : etale (spectrumMap V.second)) :
    FiniteEtaleAffinoidQuotient f V.first V.second :=
  finiteEtaleAffinoidQuotient f V.first V.second hf
    (SmallAffinoidSpectrum.algebraicallyFiniteEtale_of_map_etale.{u, u} _
      (isFiniteBanach_of_finite _ V.first_finite) h₁)
    (SmallAffinoidSpectrum.algebraicallyFiniteEtale_of_map_etale.{u, u} _
      (isFiniteBanach_of_finite _ V.second_finite) h₂)
    V.condition.1 V.generates V.ringEquivalence

/-- The original point descends to the coefficient algebra of the quotient. -/
theorem exists_descendedPoint (Q : FiniteEtaleAffinoidQuotient f V.first V.second) :
    ∃ y : RingPoints K X Q.algebra, RingPoints.changeRing Q.coverMap.toAlgHom y = x := by
  let g := Q.coverMap
  have hff := SmallAffinoidSpectrum.faithfullyFlat_of_flat_of_spectrum_surjective g
    ((g.algebraicallyFiniteEtale_iff).mp Q.coverMap_finiteEtale).2.1
    Q.coverMap_spectrum_surjective
  have hspec := (flat_and_surjective_SpecMap_iff (CommRingCat.ofHom g.toAlgHom.toRingHom)).2 hff
  let : Flat (ringTestMap K g.toAlgHom).left := hspec.1
  let : Surjective (ringTestMap K g.toAlgHom).left := hspec.2
  let : LocallyOfFinitePresentation (ringTestMap K g.toAlgHom).left :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFinitePresentation)).2
      ((g.algebraicallyFiniteEtale_iff).mp Q.coverMap_finiteEtale).2.2.2
  let U := Over.forget (Spec (CommRingCat.of K))
  have hsp : IsPullback (U.map (ringTestMap K V.first.toAlgHom))
      (U.map (ringTestMap K V.second.toAlgHom))
      (U.map (ringTestMap K g.toAlgHom)) (U.map (ringTestMap K g.toAlgHom)) :=
    isPullback_SpecMap_of_isPushout _ _ _ _ Q.relation_isPushout
  exact ProductPointsDescent.exists_pullback_eq X (ringTestMap K g.toAlgHom)
    (hsp.of_map_of_faithful U) x V.condition.2

end AffinoidPointRelation

end Langlands.Analytic.SpaceAnalytification
