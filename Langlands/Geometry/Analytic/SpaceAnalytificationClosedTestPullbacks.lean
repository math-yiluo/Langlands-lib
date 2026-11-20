import Langlands.Geometry.Analytic.GeneralizedAffinoid.Noetherian
import Langlands.Geometry.Analytic.LocalizedChartCoverLifts
import Langlands.Geometry.Analytic.SmallAffinoidLocalizedMaps
import Langlands.Geometry.Analytic.SpaceAnalytificationAffinoidChartCover
import Langlands.Geometry.Analytic.SpaceAnalytificationClosedImmersionPreservation

/-! # Affine and affinoid tests of closed immersions -/

noncomputable section

universe u

namespace Langlands.Analytic.SpaceAnalytification

open _root_.CategoryTheory _root_.CategoryTheory.Limits Set
open _root_.AlgebraicGeometry
open Langlands.AlgebraicGeometry Langlands.AlgebraicGeometry.AlgebraicSpace
open Langlands.AlgebraicGeometry.PointTopology
open AffineAnalytification PresentedAffinoidAlgebra SaturatedAtlasPresentation

variable {K : Type u} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {X' X : AlgebraicSpace (Spec (CommRingCat.of K))} {f : X' ⟶ X}
  {Y' Y : LocalizedCategory.{u, u, u} (K := K)}
  {p' : PointFamily K X' Y'} {p : PointFamily K X Y} {F : Y' ⟶ Y}
  (hp' : IsAnalytification K X' Y' p') (hp : IsAnalytification K X Y p)
  (hs' : IsSeparated X') (ht' : LocallyOfFiniteTypeOverBase X')
  (hs : IsSeparated X) (ht : LocallyOfFiniteTypeOverBase X)
  (hF : ∀ (A : Type u) [CommRing A] [Algebra K A]
    (P : FinitePolynomialPresentation K A) (x : RingPoints K X' A),
    p' A P x ≫ F = p A P (RingPoints.map f x))

set_option backward.isDefEq.respectTransparency false in
private theorem isPullback_of_affinoid_lifts
    {V W : LocalizedCategory.{u, u, u} (K := K)} {r : V ⟶ Y'} {s : V ⟶ W}
    [Mono s] {a : W ⟶ Y} (hw : r ≫ F = s ≫ a)
    (hloc : ∀ (R : PresentedAffinoidAlgebra K) (x : RingPoints K X' R)
      (v : localizedAffinoidSpectrum R ⟶ W),
      affinoidPointHom hp' hs' ht' R x ≫ F = v ≫ a →
      ∃ l : localizedAffinoidSpectrum R ⟶ V,
        l ≫ r = affinoidPointHom hp' hs' ht' R x ∧ l ≫ s = v) :
    IsPullback r s F a := by
  have hLift (c : PullbackCone F a) :
      ∃ l : c.pt ⟶ V, l ≫ r = c.fst ∧ l ≫ s = c.snd := by
    obtain ⟨S, hS⟩ := localizedObjectEquiv.surjective c.pt
    let e₀ : localizationFunctor.obj S ≅ c.pt := eqToIso hS
    let b := e₀.hom ≫ c.fst
    let d := e₀.hom ≫ c.snd
    obtain ⟨A, e, I, hI, h⟩ := exists_affinoidPointHom_pair_chartCover
      hp' hp' hs' ht' hs' ht' S b b
    obtain ⟨l, hlr, hls⟩ := exists_lift_of_chartCover (fun i : I => i.val) hI r s
      (fun _ _ _ _ h => (cancel_mono s).mp h) (e.hom ≫ b) (e.hom ≫ d) (fun i => by
        obtain ⟨x, _, hx, _⟩ := h i
        obtain ⟨l, hlr, hls⟩ := hloc _ x
          (localizationFunctor.map (A.smallChartSpectrumInclusion i.val) ≫ e.hom ≫ d) (by
            rw [hx]
            simp only [b, d, Category.assoc, c.condition])
        exact ⟨l, hlr.trans hx, hls⟩)
    refine ⟨e₀.inv ≫ e.inv ≫ l, ?_, ?_⟩
    · rw [Category.assoc, Category.assoc, hlr, Iso.inv_hom_id_assoc]
      exact e₀.inv_hom_id_assoc c.fst
    · rw [Category.assoc, Category.assoc, hls, Iso.inv_hom_id_assoc]
      exact e₀.inv_hom_id_assoc c.snd
  exact IsPullback.of_isLimit (PullbackCone.IsLimit.mk hw
    (fun c => (hLift c).choose) (fun c => (hLift c).choose_spec.1)
    (fun c => (hLift c).choose_spec.2)
    (fun c m _ hm => (cancel_mono s).mp (hm.trans (hLift c).choose_spec.2.symm)))

section Affine

variable {A B C : Type u} [CommRing A] [Algebra K A] [CommRing B] [Algebra K B]
  [CommRing C] [Algebra K C] {x : RingPoints K X A} {z : RingPoints K X' B}
  {g : A →ₐ[K] B}
  (hAlg : IsPullback (pointHom K z) ((schemeYoneda _).map (ringTestMap K g))
    (hom f) (pointHom K x))

include hAlg in
omit [IsUltrametricDist K] [CompleteSpace K] in
private theorem map_eq_changeRing : RingPoints.map f z = RingPoints.changeRing g x := by
  apply uliftYonedaEquiv.{u + 1}.symm.injective
  exact (pointHom_map K f z).trans (hAlg.w.trans (pointHom_changeRing g x).symm)

include hAlg in
omit [IsUltrametricDist K] [CompleteSpace K] in
set_option backward.isDefEq.respectTransparency false in
private theorem exists_ringPoint_factor (b : RingPoints K X' C) (φ : A →ₐ[K] C)
    (hb : RingPoints.map f b = RingPoints.changeRing φ x) :
    ∃ h : B →ₐ[K] C, h.comp g = φ ∧ RingPoints.changeRing h z = b := by
  have he : pointHom K b ≫ hom f = (schemeYoneda _).map (ringTestMap K φ) ≫ pointHom K x := by
    rw [← pointHom_map, hb, pointHom_changeRing]
  let l := hAlg.lift (pointHom K b) ((schemeYoneda _).map (ringTestMap K φ)) he
  obtain ⟨m, hm⟩ := (schemeYoneda _).map_surjective l
  let h := affineRingPointEquiv K B C m
  have hh : (schemeYoneda _).map (ringTestMap K h) = l :=
    (congrArg ((schemeYoneda _).map) (ringTestMap_affineRingPointEquiv K m)).trans hm
  refine ⟨h, ?_, ?_⟩
  · apply (affineRingPointEquiv K A C).symm.injective
    change ringTestMap K (h.comp g) = ringTestMap K φ
    apply (schemeYoneda _).map_injective
    rw [ringTestMap_comp, Functor.map_comp, hh]
    exact hAlg.lift_snd _ _ _
  · apply uliftYonedaEquiv.{u + 1}.symm.injective
    change pointHom K (RingPoints.changeRing h z) = pointHom K b
    rw [pointHom_changeRing, hh]
    exact hAlg.lift_fst _ _ _

include hp' hp hs' ht' hs ht hF hAlg in
set_option backward.isDefEq.respectTransparency false in
/-- An affine test of an algebraic pullback remains a pullback when its
analytified projection is monic. Lifts are constructed on affinoid charts. -/
theorem isPullback_of_affine_test (P : FinitePolynomialPresentation K A)
    (Q : FinitePolynomialPresentation K B)
    [Mono (AffineAnalytification.localizedHom K P Q g)] :
    IsPullback (p' B Q z) (AffineAnalytification.localizedHom K P Q g) F (p A P x) := by
  apply isPullback_of_affinoid_lifts hp' hs' ht'
  · rw [hF, map_eq_changeRing hAlg, hp.naturality]
  · intro R b v hv
    obtain ⟨φ, rfl⟩ := (localizedAffinoidHomEquiv K P R).surjective v
    have he : RingPoints.map f b = RingPoints.changeRing φ x := by
      apply affinoidPointHom_injective hp hs ht
      rw [← affinoidPointHom_comp hp' hs' ht' hp hs ht f F hF, affinoidPointHom_test]
      exact hv
    obtain ⟨δ, hδ, hz⟩ := exists_ringPoint_factor hAlg b φ he
    refine ⟨localizedAffinoidHom K Q R δ, ?_, ?_⟩
    · rw [← affinoidPointHom_test hp' hs' ht', hz]
    · rw [localizedAffinoidHom_comp K P R Q g δ, hδ]
      rfl

end Affine

set_option backward.isDefEq.respectTransparency false in
private theorem mono_localizedMapEquiv_of_surjective
    {R T : PresentedAffinoidAlgebra K} (q : BoundedAlgHom K R T) (hq : Function.Surjective q) :
    Mono (SmallAffinoidSpectrum.localizedMapEquiv.{u, u} R T q) := by
  constructor
  intro S l m h
  obtain ⟨A, hA⟩ := localizedObjectEquiv.surjective S
  change localizationFunctor.obj A = S at hA
  subst S
  refine localizedHom_ext_of_chartCover (fun i : A.presentation.atlas.Index => i) ?_ l m ?_
  · intro W hW x _
    obtain rfl := mem_singleton_iff.mp hW
    obtain ⟨σ, hσ, hm, hz, hn⟩ := A.presentation.atlas.isNet_chartFamily.1 x
    exact ⟨σ, hσ, hm, fun V hV => ⟨subset_univ _, hz V hV⟩,
      by simpa only [nhdsWithin_univ] using hn⟩
  · intro i
    let C := A.presentation.atlas.algebra i
    let j := localizationFunctor.map (A.smallChartSpectrumInclusion i)
    obtain ⟨α, hα⟩ := (SmallAffinoidSpectrum.localizedMapEquiv T C).surjective (j ≫ l)
    obtain ⟨β, hβ⟩ := (SmallAffinoidSpectrum.localizedMapEquiv T C).surjective (j ≫ m)
    have he : α.comp q = β.comp q := by
      apply (SmallAffinoidSpectrum.localizedMapEquiv R C).injective
      rw [SmallAffinoidSpectrum.localizedMapEquiv_comp.{u, u},
        SmallAffinoidSpectrum.localizedMapEquiv_comp.{u, u},
        hα, hβ, Category.assoc, Category.assoc, h]
    have hαβ : α = β := by
      apply BoundedAlgHom.ext
      intro b
      obtain ⟨a, rfl⟩ := hq b
      exact congrArg (fun k : BoundedAlgHom K R C => k a) he
    exact hα.symm.trans ((congrArg (SmallAffinoidSpectrum.localizedMapEquiv T C) hαβ).trans hβ)

include hp' hs' ht' hF in
set_option backward.isDefEq.respectTransparency false in
/-- On a realized affinoid point, the pullback of an algebraic closed
immersion is the spectrum of the actual closed quotient algebra. -/
theorem exists_affinoid_quotient_pullback
    (hf : AlgebraicSpace.IsClosedImmersion (hom f))
    (R : PresentedAffinoidAlgebra K) (x : RingPoints K X R) :
    ∃ (I : Ideal R) (hI : IsClosed (I : Set R))
      (r : localizedAffinoidSpectrum (@ClosedQuotient.algebra K _ _ R I hI) ⟶ Y'),
      IsPullback r (SmallAffinoidSpectrum.localizedMapEquiv R _
        (@ClosedQuotient.map K _ _ R I hI)) F (affinoidPointHom hp hs ht R x) := by
  obtain ⟨I, z, hAlg⟩ := exists_affine_quotient_pullback_of_isClosedImmersion hf x
  let hI := PresentedAffinoidAlgebra.isClosed_ideal R I
  let T := ClosedQuotient.algebra R I
  let q := ClosedQuotient.map R I
  let g := Ideal.Quotient.mkₐ K I
  let e : (R ⧸ I) →ₐ[K] T := Ideal.Quotient.liftₐ I q.toAlgHom
    (fun a ha => (ClosedQuotient.map_eq_zero_iff R I a).mpr ha)
  have he : e.comp g = q.toAlgHom := rfl
  let zT := RingPoints.changeRing e z
  let r := affinoidPointHom hp' hs' ht' T zT
  let s := SmallAffinoidSpectrum.localizedMapEquiv.{u, u} R T q
  let : Mono s := mono_localizedMapEquiv_of_surjective q (ClosedQuotient.map_surjective R I)
  refine ⟨I, hI, r, isPullback_of_affinoid_lifts hp' hs' ht' ?_ ?_⟩
  · change affinoidPointHom hp' hs' ht' T zT ≫ F =
      localizationFunctor.map (SmallAffinoidSpectrum.map.{u, u} q) ≫
        affinoidPointHom hp hs ht R x
    rw [affinoidPointHom_comp hp' hs' ht' hp hs ht f F hF, ← affinoidPointHom_changeRing,
      ← RingPoints.changeRing_map, map_eq_changeRing hAlg,
      ← SpaceFilteredRingPoints.changeRing_comp, he]
  · intro C b v hv
    obtain ⟨φ, rfl⟩ := (SmallAffinoidSpectrum.localizedMapEquiv R C).surjective v
    have hproj : RingPoints.map f b = RingPoints.changeRing φ.toAlgHom x := by
      apply affinoidPointHom_injective hp hs ht
      rw [← affinoidPointHom_comp hp' hs' ht' hp hs ht f F hF, affinoidPointHom_changeRing]
      exact hv
    obtain ⟨δ, hδ, hz⟩ := exists_ringPoint_factor hAlg b φ.toAlgHom hproj
    have hφ (a : R) (ha : a ∈ I) : φ a = 0 := by
      rw [← hδ, AlgHom.comp_apply]
      change δ (Ideal.Quotient.mk I a) = 0
      rw [(Ideal.Quotient.eq_zero_iff_mem).mpr ha, map_zero]
    let ψ := ClosedQuotient.lift R I φ hφ
    have hψ : ψ.comp q = φ := ClosedQuotient.lift_comp_map R I φ hφ
    have hψe : ψ.toAlgHom.comp e = δ := by
      apply AlgHom.ext
      intro t
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mkₐ_surjective K I t
      have ha := congrArg (fun k : R →ₐ[K] T => k a) he
      have hd := congrArg (fun k : R →ₐ[K] C => k a) hδ
      change ψ (e (g a)) = δ (g a)
      change e (g a) = q a at ha
      change δ (g a) = φ a at hd
      rw [ha, hd]
      exact congrArg (fun k : BoundedAlgHom K R C => k a) hψ
    refine ⟨SmallAffinoidSpectrum.localizedMapEquiv T C ψ, ?_, ?_⟩
    · change localizationFunctor.map (SmallAffinoidSpectrum.map.{u, u} ψ) ≫
        affinoidPointHom hp' hs' ht' T (RingPoints.changeRing e z) =
        affinoidPointHom hp' hs' ht' C b
      rw [← affinoidPointHom_changeRing, ← SpaceFilteredRingPoints.changeRing_comp, hψe, hz]
    · change SmallAffinoidSpectrum.localizedMapEquiv T C ψ ≫
          SmallAffinoidSpectrum.localizedMapEquiv R T q = _
      rw [← SmallAffinoidSpectrum.localizedMapEquiv_comp.{u, u} q ψ, hψ]

/-- A pullback against an affinoid test, with its actual quotient ideal,
quotient algebra and map to the source of the original morphism. -/
structure AffinoidQuotientPullback (R : PresentedAffinoidAlgebra K)
    {U V : LocalizedCategory.{u, u, u} (K := K)} (g : U ⟶ V)
    (a : localizedAffinoidSpectrum R ⟶ V) where
  ideal : Ideal R
  isClosed : IsClosed (ideal : Set R)
  lift : localizedAffinoidSpectrum (@ClosedQuotient.algebra K _ _ R ideal isClosed) ⟶ U
  isPullback : IsPullback lift
    (SmallAffinoidSpectrum.localizedMapEquiv R _ (@ClosedQuotient.map K _ _ R ideal isClosed)) g a

/-- Realize the pullback of a compatible analytification of a closed
immersion against the analytic map of an affinoid-algebra point. -/
def affinoidQuotientPullbackOfIsClosedImmersion
    (hf : AlgebraicSpace.IsClosedImmersion (hom f))
    (R : PresentedAffinoidAlgebra K) (x : RingPoints K X R) :
    AffinoidQuotientPullback R F (affinoidPointHom hp hs ht R x) := by
  let h := exists_affinoid_quotient_pullback hp' hp hs' ht' hs ht hF hf R x
  let I := h.choose
  let hc := h.choose_spec.choose
  let r := h.choose_spec.choose_spec.choose
  exact ⟨I, hc, r, h.choose_spec.choose_spec.choose_spec⟩

end Langlands.Analytic.SpaceAnalytification
