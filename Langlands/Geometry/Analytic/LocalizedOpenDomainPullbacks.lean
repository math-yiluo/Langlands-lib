import Langlands.Geometry.Analytic.LocalizedDomainGluing
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-! # Pullbacks by open analytic domains -/

noncomputable section

universe u v w i

namespace Langlands.Analytic.SaturatedAtlasPresentation

open CategoryTheory CategoryTheory.Limits Set

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {W X Y Z S : LocalizedCategory.{u, v, w} (K := K)}
  {p : W ⟶ X} {q : W ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}

/-- A pullback on domains of a given square. The domain in the proposed pullback is exactly
where both projections lie in the prescribed open domains. -/
structure OpenPullbackChart (p : W ⟶ X) (q : W ⟶ Y) (f : X ⟶ Z) (g : Y ⟶ Z) where
  source : (presentationOf W).AnalyticDomain
  left : (presentationOf X).AnalyticDomain
  right : (presentationOf Y).AnalyticDomain
  target : (presentationOf Z).AnalyticDomain
  left_open : IsOpen left.carrier
  right_open : IsOpen right.carrier
  source_carrier : source.carrier =
    localizedSpaceFunctor.map p ⁻¹' left.carrier ∩ localizedSpaceFunctor.map q ⁻¹' right.carrier
  fst : domainObj W source ⟶ domainObj X left
  snd : domainObj W source ⟶ domainObj Y right
  leftMap : domainObj X left ⟶ domainObj Z target
  rightMap : domainObj Y right ⟶ domainObj Z target
  fst_fac : fst ≫ domainι X left = domainι W source ≫ p
  snd_fac : snd ≫ domainι Y right = domainι W source ≫ q
  left_fac : leftMap ≫ domainι Z target = domainι X left ≫ f
  right_fac : rightMap ≫ domainι Z target = domainι Y right ≫ g
  isPullback : IsPullback fst snd leftMap rightMap

namespace OpenPullbackChart

private theorem existsUnique_lift (c : OpenPullbackChart p q f g) (a : S ⟶ X) (b : S ⟶ Y)
    (hab : a ≫ f = b ≫ g)
    (ha : ∀ y, localizedSpaceFunctor.map a y ∈ c.left.carrier)
    (hb : ∀ y, localizedSpaceFunctor.map b y ∈ c.right.carrier) :
    ∃! l : S ⟶ W, l ≫ p = a ∧ l ≫ q = b := by
  let a' := domainLift c.left a ha
  let b' := domainLift c.right b hb
  have ha' : a' ≫ domainι X c.left = a := domainLift_comp _ _ _
  have hb' : b' ≫ domainι Y c.right = b := domainLift_comp _ _ _
  have hcomm : a' ≫ c.leftMap = b' ≫ c.rightMap := by
    apply (cancel_mono (domainι Z c.target)).mp
    rw [Category.assoc, Category.assoc, c.left_fac, c.right_fac, ← Category.assoc,
      ← Category.assoc, ha', hb', hab]
  let l' := c.isPullback.lift a' b' hcomm
  have hlf : l' ≫ c.fst = a' := c.isPullback.lift_fst a' b' hcomm
  have hlr : l' ≫ c.snd = b' := c.isPullback.lift_snd a' b' hcomm
  refine ⟨l' ≫ domainι W c.source, ⟨?_, ?_⟩, ?_⟩
  · rw [Category.assoc, ← c.fst_fac, ← Category.assoc, hlf, ha']
  · rw [Category.assoc, ← c.snd_fac, ← Category.assoc, hlr, hb']
  · intro m hm
    have hmD (y : localizedSpaceFunctor.obj S) :
        localizedSpaceFunctor.map m y ∈ c.source.carrier := by
      rw [c.source_carrier]
      change localizedSpaceFunctor.map p (localizedSpaceFunctor.map m y) ∈ c.left.carrier ∧
        localizedSpaceFunctor.map q (localizedSpaceFunctor.map m y) ∈ c.right.carrier
      rw [← TopCat.comp_app, ← TopCat.comp_app, ← Functor.map_comp, ← Functor.map_comp, hm.1, hm.2]
      exact ⟨ha y, hb y⟩
    let m' := domainLift c.source m hmD
    have hm' : m' ≫ domainι W c.source = m := domainLift_comp _ _ _
    have he : m' = l' := by
      apply c.isPullback.hom_ext
      · apply (cancel_mono (domainι X c.left)).mp
        rw [Category.assoc, c.fst_fac, ← Category.assoc, hm', hm.1, hlf, ha']
      · apply (cancel_mono (domainι Y c.right)).mp
        rw [Category.assoc, c.snd_fac, ← Category.assoc, hm', hm.2, hlr, hb']
    rw [← hm', he]

private def sourceDomain (c : OpenPullbackChart p q f g) (a : S ⟶ X) (b : S ⟶ Y) :
    (presentationOf S).AnalyticDomain :=
  (presentationOf S).openDomain
    (localizedSpaceFunctor.map a ⁻¹' c.left.carrier ∩
      localizedSpaceFunctor.map b ⁻¹' c.right.carrier)
    ((c.left_open.preimage (localizedSpaceFunctor.map a).hom.continuous).inter
      (c.right_open.preimage (localizedSpaceFunctor.map b).hom.continuous))

private theorem isOpen_sourceDomain (c : OpenPullbackChart p q f g) (a : S ⟶ X) (b : S ⟶ Y) :
    IsOpen (c.sourceDomain a b).carrier :=
  (c.left_open.preimage (localizedSpaceFunctor.map a).hom.continuous).inter
    (c.right_open.preimage (localizedSpaceFunctor.map b).hom.continuous)

private theorem existsUnique_restrict_lift (c : OpenPullbackChart p q f g)
    (a : S ⟶ X) (b : S ⟶ Y) (hab : a ≫ f = b ≫ g)
    (D : (presentationOf S).AnalyticDomain) (hD : D ≤ c.sourceDomain a b) :
    ∃! l : domainObj S D ⟶ W, l ≫ p = domainι S D ≫ a ∧ l ≫ q = domainι S D ≫ b := by
  apply c.existsUnique_lift (domainι S D ≫ a) (domainι S D ≫ b)
  · simpa only [Category.assoc] using congrArg (domainι S D ≫ ·) hab
  · intro y
    rw [Functor.map_comp, TopCat.comp_app, domainι_apply]
    exact (hD y.property).1
  · intro y
    rw [Functor.map_comp, TopCat.comp_app, domainι_apply]
    exact (hD y.property).2

end OpenPullbackChart

/-- Open-domain pullbacks glue to a pullback when their outside domains cover every
pair of points with the same image. -/
def openDomainChartPullbackIsLimit (hpq : p ≫ f = q ≫ g) {I : Type i}
    (chart : I → OpenPullbackChart p q f g)
    (cover : ∀ (x : localizedSpaceFunctor.obj X) (y : localizedSpaceFunctor.obj Y),
      localizedSpaceFunctor.map f x = localizedSpaceFunctor.map g y →
      ∃ k, x ∈ (chart k).left.carrier ∧ y ∈ (chart k).right.carrier) :
    IsLimit (PullbackCone.mk p q hpq) := by
  classical
  have hLift (s : PullbackCone f g) : ∃! l : s.pt ⟶ W, l ≫ p = s.fst ∧ l ≫ q = s.snd := by
    let D (k : I) := (chart k).sourceDomain s.fst s.snd
    have hD : AtlasTopology.LocallyRefines (range fun k => (D k).carrier) {univ} := by
      intro U hU z _
      obtain rfl := Set.mem_singleton_iff.mp hU
      have h := congrArg (fun m => localizedSpaceFunctor.map m z) s.condition
      simp only [Functor.map_comp] at h
      obtain ⟨k, hx, hy⟩ := cover _ _ h
      have hz : z ∈ (D k).carrier := ⟨hx, hy⟩
      refine ⟨{(D k).carrier}, finite_singleton _, singleton_subset_iff.mpr ⟨k, rfl⟩, ?_, ?_⟩
      · intro T hT
        obtain rfl := mem_singleton_iff.mp hT
        exact ⟨subset_univ _, hz⟩
      · rw [sUnion_singleton, nhdsWithin_univ]
        exact ((chart k).isOpen_sourceDomain _ _).mem_nhds hz
    have hLocal (k : I) : ∃ l : domainObj s.pt (D k) ⟶ W,
        l ≫ p = domainι s.pt (D k) ≫ s.fst ∧ l ≫ q = domainι s.pt (D k) ≫ s.snd :=
      ((chart k).existsUnique_restrict_lift _ _ s.condition _ le_rfl).exists
    choose l hl hr using hLocal
    have hFac (k : I) {E : (presentationOf s.pt).AnalyticDomain} (hE : E ≤ D k) :
        (localizedDomainMap hE ≫ l k) ≫ p = domainι s.pt E ≫ s.fst ∧
          (localizedDomainMap hE ≫ l k) ≫ q = domainι s.pt E ≫ s.snd := by
      constructor
      · rw [Category.assoc, hl, ← Category.assoc]
        exact congrArg (· ≫ s.fst) (localizedDomainMap_inclusion hE)
      · rw [Category.assoc, hr, ← Category.assoc]
        exact congrArg (· ≫ s.snd) (localizedDomainMap_inclusion hE)
    let d : LocalizedDomainMatchingFamily (presentationOf s.pt) (presentationOf W) D :=
      ⟨l, fun j k => by
        obtain ⟨m, _, hm⟩ := (chart j).existsUnique_restrict_lift _ _ s.condition
          (D j ⊓ D k) inf_le_left
        exact (hm _ (hFac j inf_le_left)).trans (hm _ (hFac k inf_le_right)).symm⟩
    let lift : s.pt ⟶ W := d.glue hD
    have hRestrict (k : I) : domainι s.pt (D k) ≫ lift = l k := d.glue_restrict hD k
    have hLiftFst : lift ≫ p = s.fst := by
      apply localizedHom_ext_of_domainCover D hD
      intro k
      change domainι s.pt (D k) ≫ (lift ≫ p) = _
      rw [← Category.assoc, hRestrict]
      exact hl k
    have hLiftSnd : lift ≫ q = s.snd := by
      apply localizedHom_ext_of_domainCover D hD
      intro k
      change domainι s.pt (D k) ≫ (lift ≫ q) = _
      rw [← Category.assoc, hRestrict]
      exact hr k
    refine ⟨lift, ⟨hLiftFst, hLiftSnd⟩, ?_⟩
    intro m hm
    apply localizedHom_ext_of_domainCover D hD
    intro k
    obtain ⟨n, _, hn⟩ := (chart k).existsUnique_restrict_lift _ _ s.condition (D k) le_rfl
    change domainι s.pt (D k) ≫ m = domainι s.pt (D k) ≫ lift
    apply (hn (domainι s.pt (D k) ≫ m) ?_).trans
      (hn (domainι s.pt (D k) ≫ lift) ?_).symm
    · exact ⟨by rw [Category.assoc, hm.1], by rw [Category.assoc, hm.2]⟩
    · exact ⟨by rw [Category.assoc, hLiftFst], by rw [Category.assoc, hLiftSnd]⟩
  exact PullbackCone.IsLimit.mk hpq
    (fun s => (hLift s).exists.choose)
    (fun s => (hLift s).exists.choose_spec.1)
    (fun s => (hLift s).exists.choose_spec.2)
    (fun s m hm₁ hm₂ => by
      obtain ⟨l, _, hl⟩ := hLift s
      exact (hl m ⟨hm₁, hm₂⟩).trans (hl _ (hLift s).exists.choose_spec).symm)

/-- The square formed by such a covering family of open-domain pullbacks is Cartesian. -/
theorem isPullback_of_openDomainCharts (hpq : p ≫ f = q ≫ g) {I : Type i}
    (chart : I → OpenPullbackChart p q f g)
    (cover : ∀ (x : localizedSpaceFunctor.obj X) (y : localizedSpaceFunctor.obj Y),
      localizedSpaceFunctor.map f x = localizedSpaceFunctor.map g y →
      ∃ k, x ∈ (chart k).left.carrier ∧ y ∈ (chart k).right.carrier) :
    IsPullback p q f g :=
  IsPullback.of_isLimit (openDomainChartPullbackIsLimit hpq chart cover)

end Langlands.Analytic.SaturatedAtlasPresentation
