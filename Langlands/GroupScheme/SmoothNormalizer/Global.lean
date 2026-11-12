import Langlands.GroupScheme.SmoothNormalizer.Affine
import Langlands.GroupScheme.SubgroupFunctor.NormalizerBaseChange
import Langlands.GroupScheme.SubgroupFunctor.ZariskiLocality
import Langlands.GroupScheme.RepresentabilityTransfer
import Langlands.AlgebraicGeometry.ClosedSubschemeGluing

/-! # Closed normalizers of smooth connected subgroups over an arbitrary base

The affine case is glued along the affine open cover of the base: on the preimage of each affine
open of `S` in `G`, the normalizer is cut out by the closed subscheme produced over that affine
open, and closed subschemes satisfying a common condition glue.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.SmoothNormalizer

open SubgroupFunctor

variable {S : Scheme.{u}} {G H : GroupScheme S}

/-- Membership in a subgroup functor pulls back along every morphism of underlying schemes that is
compatible with the two points. -/
theorem mem_of_comp_left (F : SubgroupFunctor G) {T T' : Over S} {x : T ⟶ G.X}
    {x' : T' ⟶ G.X} (f : T.left ⟶ T'.left) (hf : f ≫ x'.left = x.left)
    (hx' : x' ∈ F.carrier T') : x ∈ F.carrier T := by
  have hw : f ≫ T'.hom = T.hom := by
    rw [← Over.w x', ← Over.w x, ← hf, Category.assoc]
  have hx : Over.homMk f hw ≫ x' = x := Over.OverMorphism.ext hf
  rw [← hx]
  exact F.comp_mem _ hx'

variable (G) in
/-- A morphism of schemes `z : Z ⟶ G.X.left`, regarded as a point of `G` over `Z`. -/
abbrev schemePt {Z : Scheme.{u}} (z : Z ⟶ G.X.left) : Over.mk (z ≫ G.X.hom) ⟶ G.X :=
  Over.homMk z rfl

/-- Membership of a point depends only on its underlying morphism of schemes. -/
theorem mem_iff_schemePt (F : SubgroupFunctor G) {T : Over S} (x : T ⟶ G.X) :
    x ∈ F.carrier T ↔ schemePt G x.left ∈ F.carrier _ :=
  ⟨mem_of_comp_left F (𝟙 _) (Category.id_comp _), mem_of_comp_left F (𝟙 _) (Category.id_comp _)⟩

/-- The normalizer of the range of `i`, as a condition on morphisms of schemes into `G`. -/
def NormalizerPred (i : H ⟶ G) : ∀ ⦃Z : Scheme.{u}⦄, (Z ⟶ G.X.left) → Prop :=
  fun _ z => schemePt G z ∈ (range i).normalizer.carrier _

theorem normalizerPred_comp (i : H ⟶ G) ⦃Z Z' : Scheme.{u}⦄ (a : Z' ⟶ Z)
    ⦃z : Z ⟶ G.X.left⦄ (hz : NormalizerPred i z) : NormalizerPred i (a ≫ z) :=
  mem_of_comp_left (T := Over.mk ((a ≫ z) ≫ G.X.hom)) (T' := Over.mk (z ≫ G.X.hom)) _ a rfl hz

/-- Membership in the normalizer of a monomorphically represented subgroup is local on the test
scheme. -/
theorem mem_normalizer_of_openCover (i : H ⟶ G) [Mono i.hom.hom] {T : Over S}
    (𝒰 : Scheme.OpenCover.{u} T.left) (g : T ⟶ G.X)
    (hg : ∀ k : 𝒰.I₀, coverMap 𝒰 k ≫ g ∈ (range i).normalizer.carrier (coverObj 𝒰 k)) :
    g ∈ (range i).normalizer.carrier T := by
  intro V a x hx
  let 𝒱 : Scheme.OpenCover.{u} V.left := 𝒰.pullback₁ a.left
  have key : ∀ k : 𝒱.I₀, ∃ a' : coverObj 𝒱 k ⟶ coverObj 𝒰 k,
      coverMap 𝒱 k ≫ a = a' ≫ coverMap 𝒰 k := fun k =>
    ⟨Over.homMk (pullback.snd a.left (𝒰.f k)) (by
      change pullback.snd a.left (𝒰.f k) ≫ 𝒰.f k ≫ T.hom =
        pullback.fst a.left (𝒰.f k) ≫ V.hom
      rw [← Over.w a, pullback.condition_assoc]),
      Over.OverMorphism.ext pullback.condition⟩
  constructor
  · refine (mem_range_iff_openCover i 𝒱 _).mpr fun k => ?_
    obtain ⟨a', ha'⟩ := key k
    have h := (hg k (coverObj 𝒱 k) a' (coverMap 𝒱 k ≫ x) ((range i).comp_mem _ hx)).1
    simpa only [MonObj.comp_mul, GrpObj.comp_inv, ← Category.assoc, ha'] using h
  · refine (mem_range_iff_openCover i 𝒱 _).mpr fun k => ?_
    obtain ⟨a', ha'⟩ := key k
    have h := (hg k (coverObj 𝒱 k) a' (coverMap 𝒱 k ≫ x) ((range i).comp_mem _ hx)).2
    simpa only [MonObj.comp_mul, GrpObj.comp_inv, ← Category.assoc, ha'] using h

/-- The normalizer condition is local on the source. -/
theorem normalizerPred_of_local (i : H ⟶ G) [Mono i.hom.hom] ⦃Z : Scheme.{u}⦄
    (z : Z ⟶ G.X.left)
    (h : ∀ p : Z, ∃ U : Z.Opens, p ∈ U ∧ NormalizerPred i (U.ι ≫ z)) : NormalizerPred i z := by
  choose U hU hP using h
  let 𝒰 : Z.OpenCover := Scheme.Cover.mkOfCovers Z (fun p => (U p : Scheme.{u}))
    (fun p => (U p).ι) (fun p => ⟨p, ⟨p, hU p⟩, rfl⟩)
  refine mem_normalizer_of_openCover i (T := Over.mk (z ≫ G.X.hom)) 𝒰 _ fun p => ?_
  exact mem_of_comp_left _ (𝟙 _) (Category.id_comp _) (hP p)

/-- A representative of the normalizer after base change along `b` is a chart of the normalizer
condition over the open `pullback.fst G.X.hom b` of `G`. -/
theorem isChart_baseChange (i : H ⟶ G) {S' : Scheme.{u}} (b : S' ⟶ S) {N : GroupScheme S'}
    (j : N ⟶ (GroupScheme.baseChange b).obj G)
    (hj : (range ((GroupScheme.baseChange b).map i)).normalizer.IsRepresentedBy j) :
    Scheme.ClosedSubschemeGluing.IsChart (NormalizerPred i) (pullback.fst G.X.hom b)
      j.hom.hom.left := by
  intro Z z
  rw [range_baseChangeHom, ← normalizer_baseChange] at hj
  let x' : Over.mk (z ≫ ((GroupScheme.baseChange b).obj G).X.hom) ⟶
      ((GroupScheme.baseChange b).obj G).X := Over.homMk z rfl
  have h₁ : NormalizerPred i (z ≫ pullback.fst G.X.hom b) ↔
      x' ∈ ((range i).normalizer.baseChange b).carrier _ := by
    rw [mem_baseChange]
    exact ⟨mem_of_comp_left _ (𝟙 _) (Category.id_comp _),
      mem_of_comp_left _ (𝟙 _) (Category.id_comp _)⟩
  rw [h₁, ← hj.2, mem_range]
  constructor
  · rintro ⟨y, hy⟩
    exact ⟨y.left, congrArg CommaMorphism.left hy⟩
  · rintro ⟨a, ha⟩
    refine ⟨Over.homMk a ?_, Over.OverMorphism.ext ha⟩
    subst ha
    exact (congrArg (a ≫ ·) (Over.w j.hom.hom)).symm.trans (Category.assoc _ _ _).symm

/-- A closed representative of a condition and a chart of it over an open `v` agree on `v`. -/
theorem exists_iso_pullback_chart {X : Scheme.{u}} {P : ∀ ⦃Z : Scheme.{u}⦄, (Z ⟶ X) → Prop}
    {L₀ : Scheme.{u}} {c₀ : L₀ ⟶ X} [Mono c₀]
    (hfac : ∀ ⦃Z : Scheme.{u}⦄ (z : Z ⟶ X), P z ↔ ∃ a : Z ⟶ L₀, a ≫ c₀ = z)
    {V L : Scheme.{u}} {v : V ⟶ X} {c : L ⟶ V} [Mono c]
    (hc : Scheme.ClosedSubschemeGluing.IsChart P v c) :
    ∃ e : pullback c₀ v ≅ L, e.hom ≫ c = pullback.snd c₀ v := by
  obtain ⟨a, ha⟩ := (hfac (c ≫ v)).mp ((hc c).mpr ⟨𝟙 _, Category.id_comp c⟩)
  obtain ⟨b, hb⟩ := (hc (pullback.snd c₀ v)).mp
    ((hfac _).mpr ⟨pullback.fst c₀ v, pullback.condition⟩)
  refine ⟨{ hom := b, inv := pullback.lift a c ha, hom_inv_id := ?_, inv_hom_id := ?_ }, hb⟩
  · apply pullback.hom_ext
    · rw [← cancel_mono c₀, Category.assoc, Category.assoc, pullback.lift_fst_assoc, ha,
        reassoc_of% hb, Category.id_comp, pullback.condition]
    · rw [Category.assoc, pullback.lift_snd, hb, Category.id_comp]
  · rw [← cancel_mono c, Category.assoc, hb, pullback.lift_snd, Category.id_comp]

/-- **The normalizer over an arbitrary base.** The normalizer of a smooth closed subgroup with
geometrically connected fibres of a smooth affine group scheme is represented by a finitely
presented closed subgroup scheme. -/
theorem exists_normalizer (G H : GroupScheme S) [Smooth G.X.hom] [IsAffineHom G.X.hom]
    (i : H ⟶ G) (hi : IsClosedSubgroup i) (hHs : Smooth H.X.hom)
    (hHc : GeometricallyConnected H.X.hom) :
    ∃ (N : GroupScheme S) (j : N ⟶ G), IsClosedSubgroup j ∧
      LocallyOfFinitePresentation j.hom.hom.left ∧
        (SubgroupFunctor.range i).normalizer.IsRepresentedBy j := by
  have : IsClosedImmersion i.hom.hom.left := hi
  have : Mono i.hom.hom := Over.mono_of_mono_left _
  let 𝒜 := S.affineOpenCover
  -- The affine case over each member of the affine open cover of `S`.
  have hloc : ∀ k : 𝒜.I₀, ∃ (N : GroupScheme (Spec (𝒜.X k)))
      (j : N ⟶ (GroupScheme.baseChange (𝒜.f k)).obj G), IsClosedSubgroup j ∧
        LocallyOfFinitePresentation j.hom.hom.left ∧
        (range ((GroupScheme.baseChange (𝒜.f k)).map i)).normalizer.IsRepresentedBy j := by
    intro k
    have : Smooth H.X.hom := hHs
    have : GeometricallyConnected H.X.hom := hHc
    have : Smooth ((GroupScheme.baseChange (𝒜.f k)).obj G).X.hom :=
      inferInstanceAs (Smooth (pullback.snd G.X.hom (𝒜.f k)))
    have : IsAffineHom ((GroupScheme.baseChange (𝒜.f k)).obj G).X.hom :=
      inferInstanceAs (IsAffineHom (pullback.snd G.X.hom (𝒜.f k)))
    exact exists_normalizer_affine _ _ _ (hi.baseChange (𝒜.f k))
      (inferInstanceAs (Smooth (pullback.snd H.X.hom (𝒜.f k))))
      (inferInstanceAs (GeometricallyConnected (pullback.snd H.X.hom (𝒜.f k))))
  choose N j hjc hjl hjr using hloc
  let c : ∀ k, (N k).X.left ⟶ pullback G.X.hom (𝒜.f k) := fun k => (j k).hom.hom.left
  have : ∀ k, IsClosedImmersion (c k) := hjc
  let 𝒰 : G.X.left.OpenCover := 𝒜.openCover.pullback₁ G.X.hom
  -- Glue the charts to a closed subscheme of `G`.
  obtain ⟨L₀, c₀, hc₀, hfac⟩ := Scheme.ClosedSubschemeGluing.exists_isClosedImmersion
    (normalizerPred_comp i) (fun k => pullback.fst G.X.hom (𝒜.f k))
    c (fun k => isChart_baseChange i (𝒜.f k) (j k) (hjr k))
    (fun x => ⟨𝒰.idx x, 𝒰.covers x⟩) (normalizerPred_of_local i)
  have hlfp : LocallyOfFinitePresentation c₀ := by
    have : IsZariskiLocalAtTarget @LocallyOfFinitePresentation :=
      HasRingHomProperty.instIsZariskiLocalAtTarget _
    have : IsClosedImmersion c₀ := hc₀
    refine IsZariskiLocalAtTarget.of_openCover 𝒰 fun k => ?_
    have : IsClosedImmersion (c k) := hjc k
    have : LocallyOfFinitePresentation (c k) := hjl k
    obtain ⟨e, he⟩ := exists_iso_pullback_chart (c := c k) hfac
      (isChart_baseChange i (𝒜.f k) (j k) (hjr k))
    change LocallyOfFinitePresentation (pullback.snd c₀ (pullback.fst G.X.hom (𝒜.f k)))
    rw [← he]
    infer_instance
  -- Transfer the group structure.
  let i₀ : Over.mk (c₀ ≫ G.X.hom) ⟶ G.X := Over.homMk c₀ rfl
  have : Mono i₀ := Over.mono_of_mono_left _
  have hi₀ : ∀ (T : Over S) (x : T ⟶ G.X),
      x ∈ (range i).normalizer.carrier T ↔ ∃ y : T ⟶ Over.mk (c₀ ≫ G.X.hom), y ≫ i₀ = x := by
    intro T x
    rw [mem_iff_schemePt]
    refine (hfac x.left).trans ⟨fun ⟨a, ha⟩ => ?_, fun ⟨y, hy⟩ => ⟨y.left, ?_⟩⟩
    · refine ⟨Over.homMk a ?_, Over.OverMorphism.ext ha⟩
      change a ≫ c₀ ≫ G.X.hom = T.hom
      rw [← Category.assoc, ha, Over.w x]
    · exact congrArg CommaMorphism.left hy
  have hj₀ : ((range i).normalizer.representingHom i₀ hi₀).hom.hom.left = c₀ := by
    rw [representingHom_hom]
    rfl
  refine ⟨_, (range i).normalizer.representingHom i₀ hi₀, ?_, ?_,
    (range i).normalizer.isRepresentedBy_representingHom i₀ hi₀⟩
  · change IsClosedImmersion _
    rw [hj₀]
    exact hc₀
  · rw [hj₀]
    exact hlfp

end Langlands.GroupScheme.SmoothNormalizer
