import Langlands.Geometry.Analytic.GeneralizedAffinoid.FiniteAffinoidAlgebraDescent.FiniteBanachBounds
import Langlands.Geometry.Analytic.SmallAffinoidPullbacks
import Mathlib.Algebra.Category.Ring.Basic

/-! # Analytic pullbacks from finite Banach ring pushouts -/

noncomputable section

universe u v

namespace Langlands.Analytic.SmallAffinoidSpectrum

open CategoryTheory PresentedAffinoidAlgebra SaturatedAtlasPresentation

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A B C P : PresentedAffinoidAlgebra K}
  {f : BoundedAlgHom K A B} {g : BoundedAlgHom K A C}
  {s : BoundedAlgHom K B P} {t : BoundedAlgHom K C P}

private abbrev ringMap {R S : PresentedAffinoidAlgebra K} (b : BoundedAlgHom K R S) :
    CommRingCat.of R ⟶ CommRingCat.of S :=
  CommRingCat.ofHom b.toAlgHom.toRingHom

omit [CompleteSpace K] in
private theorem ringMap_injective {R S : PresentedAffinoidAlgebra K} :
    Function.Injective (ringMap (K := K) (R := R) (S := S)) := by
  intro b c h
  exact BoundedAlgHom.ext (RingHom.congr_fun (congrArg CommRingCat.Hom.hom h))

omit [CompleteSpace K] in
/-- The ring pushout lift is bounded when one map into the pushout is finite Banach. -/
def ringPushoutLift
    (h : IsPushout (CommRingCat.ofHom f.toAlgHom.toRingHom)
      (CommRingCat.ofHom g.toAlgHom.toRingHom)
      (CommRingCat.ofHom s.toAlgHom.toRingHom) (CommRingCat.ofHom t.toAlgHom.toRingHom))
    (hs : s.IsFiniteBanach) {E : PresentedAffinoidAlgebra K}
    (a : BoundedAlgHom K B E) (b : BoundedAlgHom K C E) (hab : a.comp f = b.comp g) :
    BoundedAlgHom K P E := by
  have hw : ringMap f ≫ ringMap a = ringMap g ≫ ringMap b := congrArg ringMap hab
  let d := h.desc (ringMap a) (ringMap b) hw
  have ha : d.hom.comp s.toAlgHom.toRingHom = a.toAlgHom.toRingHom :=
    congrArg CommRingCat.Hom.hom (h.inl_desc (ringMap a) (ringMap b) hw)
  let dAlg : P →ₐ[K] E :=
    { d.hom with
      commutes' := fun k => by
        rw [← s.toAlgHom.commutes]
        exact (RingHom.congr_fun ha (algebraMap K B k)).trans (a.toAlgHom.commutes k) }
  exact BoundedAlgHom.ofFiniteBanachTriangle s hs a dAlg
    (AlgHom.ext (RingHom.congr_fun ha))

omit [CompleteSpace K] in
private theorem existsUnique_lift_of_ring_isPushout
    (h : IsPushout (ringMap f) (ringMap g) (ringMap s) (ringMap t))
    (hs : s.IsFiniteBanach) {E : PresentedAffinoidAlgebra K}
    (a : BoundedAlgHom K B E) (b : BoundedAlgHom K C E) (hab : a.comp f = b.comp g) :
    ∃! d : BoundedAlgHom K P E, d.comp s = a ∧ d.comp t = b := by
  let d := ringPushoutLift h hs a b hab
  have hw : ringMap f ≫ ringMap a = ringMap g ≫ ringMap b := congrArg ringMap hab
  have hd₁ : d.comp s = a := ringMap_injective (h.inl_desc (ringMap a) (ringMap b) hw)
  have hd₂ : d.comp t = b := ringMap_injective (h.inr_desc (ringMap a) (ringMap b) hw)
  refine ⟨d, ⟨hd₁, hd₂⟩, fun e he => ringMap_injective (h.hom_ext ?_ ?_)⟩
  · exact congrArg ringMap (he.1.trans hd₁.symm)
  · exact congrArg ringMap (he.2.trans hd₂.symm)

private theorem topChartPushout_of_ring_isPushout
    (h : IsPushout (ringMap f) (ringMap g) (ringMap s) (ringMap t))
    (hs : s.IsFiniteBanach)
    [Small.{v} (BanachSpectrum A)] [Small.{v} (BanachSpectrum B)]
    [Small.{v} (BanachSpectrum C)] [Small.{v} (BanachSpectrum P)] :
    TopChartPushout (map s) (map t) (map f) (map g)
      (topIndex P) (topIndex B) (topIndex C) (topIndex A)
      (top_contains B) (top_contains C) (top_contains A) := by
  have transport {A' B' C' P' : PresentedAffinoidAlgebra K}
      (hA : A' = A) (hB : B' = B) (hC : C' = C) (hP : P' = P)
      (f' : BoundedAlgHom K A' B') (g' : BoundedAlgHom K A' C')
      (s' : BoundedAlgHom K B' P') (t' : BoundedAlgHom K C' P')
      (hf : HEq f' f) (hg : HEq g' g) (hsl : HEq s' s) (ht : HEq t' t) :
      ∀ (E : PresentedAffinoidAlgebra K) (a : BoundedAlgHom K B' E)
        (b : BoundedAlgHom K C' E), a.comp f' = b.comp g' →
        ∃! d : BoundedAlgHom K P' E, d.comp s' = a ∧ d.comp t' = b := by
    subst A' B' C' P'
    cases eq_of_heq hf
    cases eq_of_heq hg
    cases eq_of_heq hsl
    cases eq_of_heq ht
    exact fun _ a b hab => existsUnique_lift_of_ring_isPushout h hs a b hab
  exact transport (top_algebra A) (top_algebra B) (top_algebra C) (top_algebra P)
    _ _ _ _ (map_pullbackAtTop_heq f) (map_pullbackAtTop_heq g)
    (map_pullbackAtTop_heq s) (map_pullbackAtTop_heq t)

/-- A ring pushout of presented affinoid algebras whose first leg into the
pushout is finite Banach gives a pullback in the localized analytic category. -/
theorem localized_isPullback_of_ring_isPushout
    (h : IsPushout (CommRingCat.ofHom f.toAlgHom.toRingHom)
      (CommRingCat.ofHom g.toAlgHom.toRingHom)
      (CommRingCat.ofHom s.toAlgHom.toRingHom) (CommRingCat.ofHom t.toAlgHom.toRingHom))
    (hs : s.IsFiniteBanach)
    [Small.{v} (BanachSpectrum A)] [Small.{v} (BanachSpectrum B)]
    [Small.{v} (BanachSpectrum C)] [Small.{v} (BanachSpectrum P)] :
    IsPullback (localizationFunctor.map (map s)) (localizationFunctor.map (map t))
      (localizationFunctor.map (map f)) (localizationFunctor.map (map g)) := by
  have hcomp : s.comp f = t.comp g := ringMap_injective h.w
  have hw : map s ≫ map f = map t ≫ map g := by
    rw [← map_comp, ← map_comp, hcomp]
  have hStrong := (topChartPushout_of_ring_isPushout h hs).isPullback (top_contains P) hw
  apply IsRefinedStrongPullback.isPullback
  refine ⟨hw, ?_, fun _ _ _ => hStrong.hom_ext⟩
  intro T a b hab
  refine ⟨T, 𝟙 T, AffinoidAtlasPresentation.StrongHom.isQuasiIso_id T.presentation,
    hStrong.lift a b hab, ?_, ?_⟩
  · simpa only [Category.id_comp] using hStrong.lift_fst a b hab
  · simpa only [Category.id_comp] using hStrong.lift_snd a b hab

end Langlands.Analytic.SmallAffinoidSpectrum
