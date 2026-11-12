import Langlands.Geometry.Analytic.SaturatedStrongLocalization
import Langlands.Geometry.Analytic.FullRecognitionPairLocalCondition
import Langlands.Geometry.Analytic.FullRecognitionIsomorphismCriterion
import Langlands.Geometry.Analytic.AffinoidProductChartSystem

/-! # Field-valued points of analytic spaces -/

noncomputable section

universe u v w uL

namespace Langlands.Analytic

open Set CategoryTheory PresentedAffinoidAlgebra

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

namespace IndexedAffinoidAtlas

variable {X : Type v} [TopologicalSpace X] (a : IndexedAffinoidAtlas.{u, v, w} K X)

/-- Every point lies in some chart, since the chart ranges form a quasinet. -/
theorem exists_mem_range_chart (x : X) : ∃ i, x ∈ range (a.chart i) := by
  obtain ⟨σ, -, hστ, hxσ, hσN⟩ := a.isNet_chartFamily.1 x
  obtain ⟨V, hVσ, -⟩ := Set.mem_sUnion.1 (mem_of_mem_nhds hσN)
  obtain ⟨i, rfl⟩ := hστ hVσ
  exact ⟨i, hxσ _ hVσ⟩

end IndexedAffinoidAtlas

namespace AffinoidAtlasPresentation

variable (L : Type uL) [NormedField L] [NormedAlgebra K L]

/-- An `L`-valued point of an analytic space: a point `x` together with, for every chart
containing `x`, a `K`-algebra map from the chart algebra to `L` whose absolute value is the
multiplicative seminorm of `x` in that chart, compatible with all restriction maps. -/
structure FieldPoint (A : AffinoidAtlasPresentation.{u, v, w} K) where
  /-- The underlying point. -/
  point : A.space
  /-- The evaluation map at every chart containing the point. -/
  eval : ∀ i : A.atlas.Index, point ∈ range (A.atlas.chart i) → (A.atlas.algebra i →ₐ[K] L)
  /-- The absolute value of each evaluation is the seminorm of the point in that chart. -/
  isChartPoint : ∀ i (h : point ∈ range (A.atlas.chart i)),
    ∃ p : BanachSpectrum (A.atlas.algebra i), A.atlas.chart i p = point ∧ ∀ a, ‖eval i h a‖ = p a
  /-- Evaluations are compatible with the restriction maps of the atlas. -/
  eval_restriction : ∀ i j (hij : range (A.atlas.chart i) ⊆ range (A.atlas.chart j))
    (hi : point ∈ range (A.atlas.chart i)),
    (eval i hi).comp (A.atlas.restriction i j hij).toAlgHom = eval j (hij hi)

namespace FieldPoint

variable {L} {A B C : AffinoidAtlasPresentation.{u, v, w} K}

theorem ext' {p q : FieldPoint L A} (h : p.point = q.point)
    (he : ∀ i hp hq, p.eval i hp = q.eval i hq) : p = q := by
  rcases p with ⟨x, e, c, r⟩
  rcases q with ⟨y, e', c', r'⟩
  dsimp only at h he
  subst h
  have : e = e' := funext fun i => funext fun hi => he i hi hi
  subst this
  rfl

/-- Evaluation at a larger chart, followed by any map into its algebra, is evaluation at a
smaller chart containing the point, followed by the restriction and the map. -/
theorem eval_comp_eq (p : FieldPoint L A) {i m : A.atlas.Index}
    (hmi : range (A.atlas.chart m) ⊆ range (A.atlas.chart i)) (hm : p.point ∈ range (A.atlas.chart m))
    {R : PresentedAffinoidAlgebra K} (φ : BoundedAlgHom K R (A.atlas.algebra i)) :
    (p.eval i (hmi hm)).comp φ.toAlgHom =
      (p.eval m hm).comp ((A.atlas.restriction m i hmi).comp φ).toAlgHom := by
  rw [← p.eval_restriction m i hmi hm]
  rfl

end FieldPoint

namespace StrongHom

variable {A B C : AffinoidAtlasPresentation.{u, v, w} K}

/-- If the source contains all local domains, a point whose image lies in a target chart lies
in a source chart mapped into that target chart. -/
theorem exists_admissible_mem (f : StrongHom A B) (hA : A.atlas.HasAllLocalDomains)
    (x : A.space) (j : B.atlas.Index) (hj : f.baseMap x ∈ range (B.atlas.chart j)) :
    ∃ i, x ∈ range (A.atlas.chart i) ∧
      f.baseMap '' range (A.atlas.chart i) ⊆ range (B.atlas.chart j) := by
  obtain ⟨i₀, hi₀⟩ := A.atlas.exists_mem_range_chart x
  obtain ⟨k, hk⟩ := f.target_exists i₀
  obtain ⟨m, hm, hxm⟩ :=
    IndexedAffinoidAtlas.exists_chart_inter hj (hk ⟨x, hi₀, rfl⟩)
  obtain ⟨c, hc⟩ := f.exists_chart_inter_preimage hA i₀ k m hk (hm.trans inter_subset_right)
  refine ⟨c, by rw [hc]; exact ⟨hi₀, hxm⟩, ?_⟩
  rintro _ ⟨y, hy, rfl⟩
  rw [hc] at hy
  exact (hm hy.2).1

end StrongHom

namespace FieldPoint

variable {L} {A B C : AffinoidAtlasPresentation.{u, v, w} K}

/-- Through two admissible source charts containing the point, the composite of evaluation
with the pullback of a strong map is the same. -/
theorem eval_comp_pullback_eq (p : FieldPoint L A) (f : StrongHom A B) (j : B.atlas.Index)
    {i i' : A.atlas.Index} (hi : p.point ∈ range (A.atlas.chart i))
    (hi' : p.point ∈ range (A.atlas.chart i'))
    (h : f.baseMap '' range (A.atlas.chart i) ⊆ range (B.atlas.chart j))
    (h' : f.baseMap '' range (A.atlas.chart i') ⊆ range (B.atlas.chart j)) :
    (p.eval i hi).comp (f.pullback i j h).toAlgHom =
      (p.eval i' hi').comp (f.pullback i' j h').toAlgHom := by
  obtain ⟨m, hm, hxm⟩ := IndexedAffinoidAtlas.exists_chart_inter hi hi'
  have hmi : range (A.atlas.chart m) ⊆ range (A.atlas.chart i) := hm.trans inter_subset_left
  have hmi' : range (A.atlas.chart m) ⊆ range (A.atlas.chart i') := hm.trans inter_subset_right
  have hmj : f.baseMap '' range (A.atlas.chart m) ⊆ range (B.atlas.chart j) :=
    (Set.image_mono hmi).trans h
  have key : ∀ {n : A.atlas.Index} (hmn : range (A.atlas.chart m) ⊆ range (A.atlas.chart n))
      (hn : f.baseMap '' range (A.atlas.chart n) ⊆ range (B.atlas.chart j)),
      (A.atlas.restriction m n hmn).comp (f.pullback n j hn) = f.pullback m j hmj := by
    intro n hmn hn
    rw [f.restriction_comm m n j j hmn subset_rfl hmj hn, B.atlas.restriction_id,
      BoundedAlgHom.comp_id]
  calc (p.eval i hi).comp (f.pullback i j h).toAlgHom
      = (p.eval m hxm).comp ((A.atlas.restriction m i hmi).comp (f.pullback i j h)).toAlgHom :=
        p.eval_comp_eq hmi hxm _
    _ = (p.eval m hxm).comp (f.pullback m j hmj).toAlgHom := by rw [key hmi h]
    _ = (p.eval m hxm).comp ((A.atlas.restriction m i' hmi').comp
          (f.pullback i' j h')).toAlgHom := by rw [key hmi' h']
    _ = (p.eval i' hi').comp (f.pullback i' j h').toAlgHom := (p.eval_comp_eq hmi' hxm _).symm

/-- The image of a field-valued point at a target chart: evaluation at a chosen admissible
source chart, composed with the pullback. -/
def pushEval (p : FieldPoint L A) (f : StrongHom A B) (hA : A.atlas.HasAllLocalDomains)
    (j : B.atlas.Index) (hj : f.baseMap p.point ∈ range (B.atlas.chart j)) :
    B.atlas.algebra j →ₐ[K] L :=
  (p.eval _ (f.exists_admissible_mem hA p.point j hj).choose_spec.1).comp
    (f.pullback _ j (f.exists_admissible_mem hA p.point j hj).choose_spec.2).toAlgHom

theorem pushEval_eq (p : FieldPoint L A) (f : StrongHom A B) (hA : A.atlas.HasAllLocalDomains)
    (j : B.atlas.Index) (hj : f.baseMap p.point ∈ range (B.atlas.chart j))
    (i : A.atlas.Index) (hi : p.point ∈ range (A.atlas.chart i))
    (hij : f.baseMap '' range (A.atlas.chart i) ⊆ range (B.atlas.chart j)) :
    p.pushEval f hA j hj = (p.eval i hi).comp (f.pullback i j hij).toAlgHom :=
  p.eval_comp_pullback_eq f j _ hi _ hij

/-- The image of a field-valued point under a strong map out of an atlas containing all local
domains. -/
def map (p : FieldPoint L A) (f : StrongHom A B) (hA : A.atlas.HasAllLocalDomains) :
    FieldPoint L B where
  point := f.baseMap p.point
  eval j hj := p.pushEval f hA j hj
  isChartPoint j hj := by
    obtain ⟨i, hi, hij⟩ := f.exists_admissible_mem hA p.point j hj
    obtain ⟨q, hq, hn⟩ := p.isChartPoint i hi
    refine ⟨BanachSpectrum.comap (f.pullback i j hij).toBoundedRingHom q, ?_, fun b => ?_⟩
    · rw [f.chart_comm, hq]
    · rw [p.pushEval_eq f hA j hj i hi hij]
      exact hn _
  eval_restriction j j' hjj' hj := by
    obtain ⟨i, hi, hij⟩ := f.exists_admissible_mem hA p.point j hj
    have hij' : f.baseMap '' range (A.atlas.chart i) ⊆ range (B.atlas.chart j') :=
      hij.trans hjj'
    rw [p.pushEval_eq f hA j hj i hi hij, p.pushEval_eq f hA j' (hjj' hj) i hi hij']
    have hc := f.restriction_comm i i j j' subset_rfl hjj' hij hij'
    rw [A.atlas.restriction_id, BoundedAlgHom.id_comp] at hc
    rw [hc]
    rfl

@[simp]
theorem map_point (p : FieldPoint L A) (f : StrongHom A B) (hA : A.atlas.HasAllLocalDomains) :
    (p.map f hA).point = f.baseMap p.point := rfl

theorem map_eval (p : FieldPoint L A) (f : StrongHom A B) (hA : A.atlas.HasAllLocalDomains)
    (j : B.atlas.Index) (hj : f.baseMap p.point ∈ range (B.atlas.chart j))
    (i : A.atlas.Index) (hi : p.point ∈ range (A.atlas.chart i))
    (hij : f.baseMap '' range (A.atlas.chart i) ⊆ range (B.atlas.chart j)) :
    (p.map f hA).eval j hj = (p.eval i hi).comp (f.pullback i j hij).toAlgHom :=
  p.pushEval_eq f hA j hj i hi hij

theorem map_id (p : FieldPoint L A) (hA : A.atlas.HasAllLocalDomains) :
    p.map (StrongHom.id A) hA = p := by
  refine ext' rfl fun j hj hj' => ?_
  rw [p.map_eval (StrongHom.id A) hA j hj j hj' (by rintro _ ⟨y, hy, rfl⟩; exact hy)]
  exact p.eval_restriction j j _ hj'

theorem map_saturatedComp (p : FieldPoint L A) (f : StrongHom A B) (g : StrongHom B C)
    (hA : A.atlas.HasAllLocalDomains) (hB : B.atlas.HasAllLocalDomains) :
    p.map (f.saturatedComp g hA hB) hA = (p.map f hA).map g hB := by
  refine ext' rfl fun l hl hl' => ?_
  obtain ⟨j, hj, hjl⟩ := g.exists_admissible_mem hB (f.baseMap p.point) l hl'
  obtain ⟨i, hi, hij⟩ := f.exists_admissible_mem hA p.point j hj
  have hil : (f.saturatedComp g hA hB).baseMap '' range (A.atlas.chart i) ⊆
      range (C.atlas.chart l) := by
    rintro _ ⟨y, hy, rfl⟩
    exact hjl ⟨f.baseMap y, hij ⟨y, hy, rfl⟩, rfl⟩
  rw [p.map_eval _ hA l hl i hi hil, (p.map f hA).map_eval g hB l hl' j hj hjl,
    p.map_eval f hA j hj i hi hij, f.saturatedComp_pullback g hA hB i j l hij hjl hil]
  rfl

end FieldPoint

namespace StrongHom.IsQuasiIso

variable {A B : AffinoidAtlasPresentation.{u, v, w} K} {s : StrongHom A B} (hs : s.IsQuasiIso)
  (hB : B.atlas.HasAllLocalDomains)

include hs hB in
/-- For a quasi-isomorphism into an atlas containing all local domains, the image of every
source chart is a target chart. -/
theorem exists_chart_eq_image (i : A.atlas.Index) :
    ∃ j, range (B.atlas.chart j) = s.baseMap '' range (A.atlas.chart i) := by
  obtain ⟨k, hk⟩ := s.target_exists i
  obtain ⟨j, hj⟩ := hB.exists_chart ⟨k, hs.localDomain i k hk⟩
  refine ⟨j, hj.trans ?_⟩
  exact image_preimage_eq_of_subset hk

/-- A target chart whose range is the image of the source chart `i`. -/
def imageChart (i : A.atlas.Index) : B.atlas.Index :=
  (hs.exists_chart_eq_image hB i).choose

theorem range_imageChart (i : A.atlas.Index) :
    range (B.atlas.chart (hs.imageChart hB i)) = s.baseMap '' range (A.atlas.chart i) :=
  (hs.exists_chart_eq_image hB i).choose_spec

theorem imageChart_admissible (i : A.atlas.Index) :
    s.baseMap '' range (A.atlas.chart i) ⊆ range (B.atlas.chart (hs.imageChart hB i)) :=
  (hs.range_imageChart hB i).ge

theorem represents_univ (i : A.atlas.Index) :
    Represents K (s.pullback i (hs.imageChart hB i) (hs.imageChart_admissible hB i)) univ := by
  have h := hs.2 i _ (hs.imageChart_admissible hB i)
  have hu : s.chartImageLocus i (hs.imageChart hB i) = univ := by
    rw [chartImageLocus, ← hs.range_imageChart hB i, preimage_range]
  rwa [hu] at h

/-- The inverse of the pullback to the image chart, which is an isomorphism of affinoid
algebras. -/
def chartInverse (i : A.atlas.Index) :
    BoundedAlgHom K (A.atlas.algebra i) (B.atlas.algebra (hs.imageChart hB i)) :=
  (hs.represents_univ hB i).univInverse

theorem chartInverse_comp (i : A.atlas.Index) (b : B.atlas.algebra (hs.imageChart hB i)) :
    hs.chartInverse hB i (s.pullback i _ (hs.imageChart_admissible hB i) b) = b :=
  congrArg (fun q : BoundedAlgHom K _ _ => q b) (hs.represents_univ hB i).univInverse_comp

theorem comp_chartInverse (i : A.atlas.Index) (a : A.atlas.algebra i) :
    s.pullback i _ (hs.imageChart_admissible hB i) (hs.chartInverse hB i a) = a :=
  congrArg (fun q : BoundedAlgHom K _ _ => q a) (hs.represents_univ hB i).comp_univInverse

/-- The inverse composed with the pullback to any target chart containing the image chart is the
target restriction. -/
theorem chartInverse_pullback (i : A.atlas.Index) (j : B.atlas.Index)
    (h : s.baseMap '' range (A.atlas.chart i) ⊆ range (B.atlas.chart j))
    (hj : range (B.atlas.chart (hs.imageChart hB i)) ⊆ range (B.atlas.chart j))
    (b : B.atlas.algebra j) :
    hs.chartInverse hB i (s.pullback i j h b) =
      B.atlas.restriction (hs.imageChart hB i) j hj b := by
  have hc := s.restriction_comm i i (hs.imageChart hB i) j subset_rfl hj
    (hs.imageChart_admissible hB i) h
  rw [A.atlas.restriction_id, BoundedAlgHom.id_comp] at hc
  have hb := congrArg (fun q : BoundedAlgHom K _ _ => q b) hc
  rw [hb]
  exact hs.chartInverse_comp hB i _

end StrongHom.IsQuasiIso

namespace FieldPoint

variable {L} {A B : AffinoidAtlasPresentation.{u, v, w} K}

theorem eval_congr {p q : FieldPoint L A} (e : p = q) (i : A.atlas.Index)
    (hp : p.point ∈ range (A.atlas.chart i)) (hq : q.point ∈ range (A.atlas.chart i)) :
    p.eval i hp = q.eval i hq := by
  subst e
  rfl

variable {s : StrongHom A B} (hs : s.IsQuasiIso) (hB : B.atlas.HasAllLocalDomains)

/-- The preimage of a field-valued point under a quasi-isomorphism into an atlas containing all
local domains: evaluate at the image chart and compose with the inverse of the pullback. -/
def comapQuasiIso (q : FieldPoint L B) : FieldPoint L A where
  point := Function.surjInv hs.1.surjective q.point
  eval i hi := (q.eval (hs.imageChart hB i) (by
      rw [hs.range_imageChart hB i, ← Function.surjInv_eq hs.1.surjective q.point]
      exact mem_image_of_mem _ hi)).comp (hs.chartInverse hB i).toAlgHom
  isChartPoint i hi := by
    obtain ⟨r, hr, hn⟩ := q.isChartPoint (hs.imageChart hB i) (by
      rw [hs.range_imageChart hB i, ← Function.surjInv_eq hs.1.surjective q.point]
      exact mem_image_of_mem _ hi)
    refine ⟨BanachSpectrum.comap (hs.chartInverse hB i).toBoundedRingHom r, ?_, fun a => hn _⟩
    apply hs.1.injective
    rw [Function.surjInv_eq hs.1.surjective q.point, ← s.chart_comm i (hs.imageChart hB i)
      (hs.imageChart_admissible hB i), ← hr]
    congr 1
    ext b
    exact congrArg r (hs.chartInverse_comp hB i b)
  eval_restriction i i' hii' hi := by
    have hmem : ∀ m (hm : Function.surjInv hs.1.surjective q.point ∈ range (A.atlas.chart m)),
        q.point ∈ range (B.atlas.chart (hs.imageChart hB m)) := fun m hm => by
      rw [hs.range_imageChart hB m, ← Function.surjInv_eq hs.1.surjective q.point]
      exact mem_image_of_mem _ hm
    have hjj : range (B.atlas.chart (hs.imageChart hB i)) ⊆
        range (B.atlas.chart (hs.imageChart hB i')) := by
      rw [hs.range_imageChart hB i, hs.range_imageChart hB i']
      exact image_mono hii'
    rw [← q.eval_restriction _ _ hjj (hmem i hi)]
    ext a
    change q.eval _ (hmem i hi) (hs.chartInverse hB i (A.atlas.restriction i i' hii' a)) =
      q.eval _ (hmem i hi) (B.atlas.restriction _ _ hjj (hs.chartInverse hB i' a))
    congr 1
    have hc := s.restriction_comm i i' (hs.imageChart hB i) (hs.imageChart hB i') hii' hjj
      (hs.imageChart_admissible hB i) (hs.imageChart_admissible hB i')
    have hb := congrArg (fun φ : BoundedAlgHom K _ _ =>
      hs.chartInverse hB i (φ (hs.chartInverse hB i' a))) hc
    change hs.chartInverse hB i (A.atlas.restriction i i' hii'
        (s.pullback i' _ (hs.imageChart_admissible hB i') (hs.chartInverse hB i' a))) =
      hs.chartInverse hB i (s.pullback i _ (hs.imageChart_admissible hB i)
        (B.atlas.restriction _ _ hjj (hs.chartInverse hB i' a))) at hb
    rw [hs.comp_chartInverse hB i' a, hs.chartInverse_comp hB i] at hb
    exact hb

theorem map_comapQuasiIso (hA : A.atlas.HasAllLocalDomains) (q : FieldPoint L B) :
    (comapQuasiIso hs hB q).map s hA = q := by
  refine ext' (Function.surjInv_eq hs.1.surjective q.point) fun j hj hj' => ?_
  obtain ⟨i, hi, hij⟩ := s.exists_admissible_mem hA _ j hj
  have hjj : range (B.atlas.chart (hs.imageChart hB i)) ⊆ range (B.atlas.chart j) := by
    rw [hs.range_imageChart hB i]
    exact hij
  rw [map_eval _ s hA j hj i hi hij, ← q.eval_restriction _ _ hjj]
  ext b
  change q.eval _ _ (hs.chartInverse hB i (s.pullback i j hij b)) =
    q.eval _ _ (B.atlas.restriction _ _ hjj b)
  rw [hs.chartInverse_pullback hB i j hij hjj b]

include hs hB in
theorem map_injective (hA : A.atlas.HasAllLocalDomains) :
    Function.Injective fun p : FieldPoint L A => p.map s hA := by
  intro p p' e
  have hpt : p.point = p'.point := hs.1.injective (congrArg FieldPoint.point e)
  refine ext' hpt fun i hp hp' => ?_
  have hm : s.baseMap p.point ∈ range (B.atlas.chart (hs.imageChart hB i)) :=
    hs.imageChart_admissible hB i ⟨p.point, hp, rfl⟩
  have hm' : s.baseMap p'.point ∈ range (B.atlas.chart (hs.imageChart hB i)) :=
    hs.imageChart_admissible hB i ⟨p'.point, hp', rfl⟩
  have he := eval_congr e (hs.imageChart hB i) hm hm'
  rw [map_eval p s hA _ hm i hp (hs.imageChart_admissible hB i),
    map_eval p' s hA _ hm' i hp' (hs.imageChart_admissible hB i)] at he
  ext a
  have ha := congrArg (fun φ => φ (hs.chartInverse hB i a)) he
  simp only [AlgHom.comp_apply] at ha
  change p.eval i hp (s.pullback i _ _ (hs.chartInverse hB i a)) =
    p'.eval i hp' (s.pullback i _ _ (hs.chartInverse hB i a)) at ha
  rwa [hs.comp_chartInverse hB i a] at ha

include hs hB in
theorem map_bijective (hA : A.atlas.HasAllLocalDomains) :
    Function.Bijective fun p : FieldPoint L A => p.map s hA :=
  ⟨map_injective hs hB hA, fun q => ⟨comapQuasiIso hs hB q, map_comapQuasiIso hs hB hA q⟩⟩

end FieldPoint

end AffinoidAtlasPresentation

namespace SaturatedAtlasPresentation

open AffinoidAtlasPresentation

variable (L : Type uL) [NormedField L] [NormedAlgebra K L]

/-- The functor of `L`-valued points on saturated affinoid atlas presentations. -/
def fieldPointFunctor : SaturatedAtlasPresentation.{u, v, w} K ⥤ Type (max u v w uL) where
  obj A := FieldPoint L A.presentation
  map {A _B} f := TypeCat.ofHom fun p : FieldPoint L A.presentation => p.map f A.hasAllLocalDomains
  map_id A := by
    ext p
    exact FieldPoint.map_id p A.hasAllLocalDomains
  map_comp {A B _C} f g := by
    ext p
    exact FieldPoint.map_saturatedComp p f g A.hasAllLocalDomains B.hasAllLocalDomains

theorem fieldPointFunctor_obj (A : SaturatedAtlasPresentation.{u, v, w} K) :
    (fieldPointFunctor L).obj A = FieldPoint L A.presentation := rfl

theorem fieldPointFunctor_map_apply {A B : SaturatedAtlasPresentation.{u, v, w} K} (f : A ⟶ B)
    (p : FieldPoint L A.presentation) :
    (fieldPointFunctor L).map f p = p.map f A.hasAllLocalDomains := rfl

/-- Field-valued points turn quasi-isomorphisms into bijections. -/
theorem fieldPointFunctor_inverts :
    (quasiIsomorphisms (K := K) :
      MorphismProperty (SaturatedAtlasPresentation.{u, v, w} K)).IsInvertedBy
        (fieldPointFunctor L) := by
  intro A B s hs
  exact (isIso_iff_bijective _).2
    (FieldPoint.map_bijective hs B.hasAllLocalDomains A.hasAllLocalDomains)

/-- The functor of `L`-valued points on the localized category of analytic spaces. -/
def localizedFieldPointFunctor : LocalizedCategory.{u, v, w} (K := K) ⥤ Type (max u v w uL) :=
  descend (fieldPointFunctor L) (fieldPointFunctor_inverts L)

@[simp]
theorem localizationFunctor_localizedFieldPointFunctor :
    (localizationFunctor (K := K)) ⋙ localizedFieldPointFunctor L = fieldPointFunctor L :=
  localizationFunctor_descend _ _

/-- The underlying point of a field-valued point. -/
def fieldPointProjection :
    fieldPointFunctor L ⟶
      spaceFunctor.{u, v, w} (K := K) ⋙ forget TopCat ⋙ uliftFunctor.{max u w uL, v} where
  app _ := TypeCat.ofHom fun p => ULift.up p.point
  naturality _ _ _ := rfl

/-- The underlying point of a field-valued point, on the localized category. -/
def localizedFieldPointProjection :
    localizedFieldPointFunctor L ⟶
      localizedSpaceFunctor.{u, v, w} (K := K) ⋙ forget TopCat ⋙ uliftFunctor.{max u w uL, v} :=
  Localization.Construction.natTransExtension
    (eqToHom (localizationFunctor_localizedFieldPointFunctor L) ≫ fieldPointProjection L ≫
      eqToHom (by
        rw [← Functor.assoc]
        exact congrArg (fun F => F ⋙ forget TopCat ⋙ uliftFunctor.{max u w uL, v})
          localizationFunctor_localizedSpaceFunctor.symm))

theorem localizedFieldPointProjection_app (A : SaturatedAtlasPresentation.{u, v, w} K)
    (p : (localizedFieldPointFunctor L).obj (localizationFunctor.obj A)) :
    (localizedFieldPointProjection L).app (localizationFunctor.obj A) p =
      ULift.up (FieldPoint.point (L := L) (A := A.presentation) p) := rfl


end SaturatedAtlasPresentation

end Langlands.Analytic
