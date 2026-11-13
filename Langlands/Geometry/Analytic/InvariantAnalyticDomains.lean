import Langlands.Geometry.Analytic.AnalyticDomainSpaces
import Langlands.Geometry.Analytic.SaturatedDomainCorestriction
import Langlands.Geometry.Analytic.GeneralizedAffinoid.RationalLaurentNeighborhoods
import Langlands.Geometry.Analytic.ContinuousAnalyticAction

/-! # Open and invariant analytic domains and restricted group actions -/

noncomputable section

universe u v w z

namespace Langlands.Analytic

open CategoryTheory Set Filter Topology PresentedAffinoidAlgebra
open scoped Topology

namespace IndexedAffinoidAtlas

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {X : Type v} [TopologicalSpace X] {a : IndexedAffinoidAtlas.{u, v, w} K X}

/-- In an atlas with all local domains, every open subset is an analytic domain: each point has
a chart contained in the open subset whose range is a neighbourhood of the point. -/
theorem HasAllLocalDomains.isOriginalChartDomain_of_isOpen (ha : a.HasAllLocalDomains)
    {U : Set X} (hU : IsOpen U) : a.IsOriginalChartDomain U := by
  classical
  let κ : Set (Set X) := Set.range (fun i => Set.range (a.chart i) ∩ U)
  have hκ : AtlasTopology.LocallyRefines κ {U} := by
    rintro _ ⟨rfl⟩ x hx
    obtain ⟨σ, hf, hs, hm, hn⟩ := a.isNet_chartFamily.1 x
    refine ⟨(fun V => V ∩ U) '' σ, hf.image _, ?_, ?_, ?_⟩
    · rintro _ ⟨V, hV, rfl⟩
      obtain ⟨i, rfl⟩ := hs hV
      exact ⟨i, rfl⟩
    · rintro _ ⟨V, hV, rfl⟩
      exact ⟨Set.inter_subset_right, hm V hV, hx⟩
    · have hδ : ⋃₀ ((fun V => V ∩ U) '' σ) = (⋃₀ σ) ∩ U := by
        ext y
        constructor
        · rintro ⟨_, ⟨V, hV, rfl⟩, hy⟩
          exact ⟨⟨V, hV, hy.1⟩, hy.2⟩
        · rintro ⟨⟨V, hV, hyV⟩, hyU⟩
          exact ⟨_, ⟨V, hV, rfl⟩, hyV, hyU⟩
      rw [hδ]
      exact Filter.inter_mem (mem_nhdsWithin_of_mem_nhds hn) self_mem_nhdsWithin
  apply (AtlasTopology.isQuasinet_restrictedFamily_iff _ _).mpr
  apply hκ.trans
  rintro _ ⟨i, rfl⟩ x hx
  obtain ⟨⟨y, rfl⟩, hyU⟩ := hx
  have hpre : a.chart i ⁻¹' U ∈ 𝓝 y :=
    (hU.preimage (a.isEmbedding_chart i).continuous).mem_nhds hyU
  obtain ⟨d, hd, hdU⟩ := RationalChart.exists_rational_neighborhood (K := K) y _ hpre
  obtain ⟨k, hk⟩ := ha.exists_chart ⟨i, d.toDomain⟩
  change Set.range (a.chart k) = a.chart i '' d.locus at hk
  refine ⟨{Set.range (a.chart k)}, Set.finite_singleton _, ?_, ?_, ?_⟩
  · rintro _ rfl
    exact ⟨k, rfl⟩
  · rintro _ rfl
    rw [hk]
    refine ⟨?_, y, mem_of_mem_nhds hd, rfl⟩
    rintro _ ⟨z, hz, rfl⟩
    exact ⟨⟨z, rfl⟩, hdU hz⟩
  · rw [Set.sUnion_singleton, hk]
    exact nhdsWithin_mono _ Set.inter_subset_left
      ((a.isEmbedding_chart i).isInducing.image_mem_nhdsWithin hd)

end IndexedAffinoidAtlas

namespace SaturatedAtlasPresentation

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

section Domains

variable (S : SaturatedAtlasPresentation.{u, v, w} K)

/-- An open subset of the space of `S`, as an analytic domain. -/
def openDomain (U : Set S.presentation.space) (hU : IsOpen U) : S.AnalyticDomain :=
  ⟨U, S.hasAllLocalDomains.isOriginalChartDomain_of_isOpen hU⟩

@[simp]
theorem openDomain_carrier (U : Set S.presentation.space) (hU : IsOpen U) :
    (S.openDomain U hU).carrier = U :=
  rfl

/-- The localized canonical morphism of a domain is the image of the domain inclusion of the
source-quotient category under its comparison equivalence with the localized category. -/
theorem comparisonFunctor_map_domainInclusion (D : S.AnalyticDomain) :
    SourceCategory.comparisonFunctor.map (SourceCategory.domainInclusion S D) =
      S.localizedDomainInclusion D :=
  sourceHomEquiv.apply_symm_apply (localizationFunctor.map (S.originalDomainInclusion D))

/-- The localized canonical morphism of a domain is a monomorphism. -/
instance localizedDomainInclusion_mono (D : S.AnalyticDomain) :
    Mono (S.localizedDomainInclusion D) where
  right_cancellation {Z} f g h := by
    obtain ⟨A, rfl⟩ := localizedObjectEquiv.surjective Z
    obtain ⟨F, rfl⟩ := (SourceCategory.comparisonFunctor (K := K)).map_surjective
      (X := SourceCategory.ofPresentation A)
      (Y := SourceCategory.ofPresentation (S.originalDomain D)) f
    obtain ⟨G, rfl⟩ := (SourceCategory.comparisonFunctor (K := K)).map_surjective
      (X := SourceCategory.ofPresentation A)
      (Y := SourceCategory.ofPresentation (S.originalDomain D)) g
    have e := S.comparisonFunctor_map_domainInclusion D
    have hF := (SourceCategory.comparisonFunctor.map_comp F (SourceCategory.domainInclusion S D)).trans
      (congrArg (SourceCategory.comparisonFunctor.map F ≫ ·) e)
    have hG := (SourceCategory.comparisonFunctor.map_comp G (SourceCategory.domainInclusion S D)).trans
      (congrArg (SourceCategory.comparisonFunctor.map G ≫ ·) e)
    have hFG : F ≫ SourceCategory.domainInclusion S D = G ≫ SourceCategory.domainInclusion S D :=
      SourceCategory.comparisonFunctor.map_injective (hF.trans (h.trans hG.symm))
    exact congrArg SourceCategory.comparisonFunctor.map
      ((cancel_mono (SourceCategory.domainInclusion S D)).1 hFG)

variable {S}

/-- Every morphism of analytic spaces whose image lies in a domain `D` factors through the
canonical morphism of `D`. -/
theorem exists_localizedDomainLift {X : LocalizedCategory.{u, v, w} (K := K)}
    (D : S.AnalyticDomain) (f : X ⟶ localizationFunctor.obj S)
    (hf : ∀ x, localizedSpaceFunctor.map f x ∈ D.carrier) :
    ∃ g : X ⟶ localizationFunctor.obj (S.domain D), g ≫ S.localizedDomainInclusion D = f := by
  obtain ⟨A, rfl⟩ := localizedObjectEquiv.surjective X
  obtain ⟨F, rfl⟩ := (SourceCategory.comparisonFunctor (K := K)).map_surjective
    (X := SourceCategory.ofPresentation A) (Y := SourceCategory.ofPresentation S) f
  obtain ⟨G, hG⟩ := SourceCategory.exists_domainFactor D F hf
  refine ⟨SourceCategory.comparisonFunctor.map G, ?_⟩
  exact (congrArg (SourceCategory.comparisonFunctor.map G ≫ ·)
    (S.comparisonFunctor_map_domainInclusion D).symm).trans
      ((SourceCategory.comparisonFunctor.map_comp G _).symm.trans
        (congrArg SourceCategory.comparisonFunctor.map hG))

end Domains

section Objects

variable {X Y Z : LocalizedCategory.{u, v, w} (K := K)}

variable (X) in
/-- The analytic space of a domain `D` of an analytic space `X`. -/
abbrev domainObj (D : (presentationOf X).AnalyticDomain) : LocalizedCategory.{u, v, w} (K := K) :=
  localizationFunctor.obj ((presentationOf X).domain D)

variable (X) in
/-- The canonical morphism `ν : D → X` of a domain `D` of `X`. -/
def domainι (D : (presentationOf X).AnalyticDomain) : domainObj X D ⟶ X :=
  (presentationOf X).localizedDomainInclusion D

/-- The canonical morphism of a domain is the inclusion of the subspace. -/
@[simp]
theorem domainι_apply (D : (presentationOf X).AnalyticDomain)
    (x : localizedSpaceFunctor.obj (domainObj X D)) :
    localizedSpaceFunctor.map (domainι X D) x = Subtype.val (p := (· ∈ D.carrier)) x :=
  (presentationOf X).localizedSpaceFunctor_map_localizedDomainInclusion D x

instance domainι_mono (D : (presentationOf X).AnalyticDomain) : Mono (domainι X D) :=
  (presentationOf X).localizedDomainInclusion_mono D

/-- Every morphism to `X` whose image lies in the domain `D` factors through `D`. -/
theorem exists_domainLift (D : (presentationOf X).AnalyticDomain) (f : Y ⟶ X)
    (hf : ∀ y, localizedSpaceFunctor.map f y ∈ D.carrier) :
    ∃ g : Y ⟶ domainObj X D, g ≫ domainι X D = f :=
  exists_localizedDomainLift (S := presentationOf X) D f hf

/-- The factorization through `D` of a morphism whose image lies in `D`. -/
def domainLift (D : (presentationOf X).AnalyticDomain) (f : Y ⟶ X)
    (hf : ∀ y, localizedSpaceFunctor.map f y ∈ D.carrier) : Y ⟶ domainObj X D :=
  Classical.choose (exists_domainLift D f hf)

@[reassoc (attr := simp)]
theorem domainLift_comp (D : (presentationOf X).AnalyticDomain) (f : Y ⟶ X)
    (hf : ∀ y, localizedSpaceFunctor.map f y ∈ D.carrier) :
    domainLift D f hf ≫ domainι X D = f :=
  Classical.choose_spec (exists_domainLift D f hf)

/-- The factorization through `D` is unique. -/
theorem eq_domainLift (D : (presentationOf X).AnalyticDomain) (f : Y ⟶ X)
    (hf : ∀ y, localizedSpaceFunctor.map f y ∈ D.carrier) (g : Y ⟶ domainObj X D)
    (hg : g ≫ domainι X D = f) : g = domainLift D f hf :=
  (cancel_mono (domainι X D)).1 (hg.trans (domainLift_comp D f hf).symm)

/-- The factorization has the same underlying map, with its codomain restricted to `D`. -/
theorem val_domainLift_apply (D : (presentationOf X).AnalyticDomain) (f : Y ⟶ X)
    (hf : ∀ y, localizedSpaceFunctor.map f y ∈ D.carrier) (y : localizedSpaceFunctor.obj Y) :
    Subtype.val (p := (· ∈ D.carrier)) (localizedSpaceFunctor.map (domainLift D f hf) y) =
      localizedSpaceFunctor.map f y := by
  rw [← domainι_apply, ← TopCat.comp_app, ← Functor.map_comp, domainLift_comp]

theorem domainι_comp_apply_mem (D : (presentationOf X).AnalyticDomain)
    (E : (presentationOf Y).AnalyticDomain) (f : X ⟶ Y)
    (hf : ∀ x ∈ D.carrier, localizedSpaceFunctor.map f x ∈ E.carrier)
    (x : localizedSpaceFunctor.obj (domainObj X D)) :
    localizedSpaceFunctor.map (domainι X D ≫ f) x ∈ E.carrier := by
  have hx : localizedSpaceFunctor.map (domainι X D ≫ f) x =
      localizedSpaceFunctor.map f (Subtype.val (p := (· ∈ D.carrier)) x) := by
    rw [Functor.map_comp, TopCat.comp_app, domainι_apply]
  exact (congrArg (· ∈ E.carrier) hx).mpr (hf _ x.property)

/-- The restriction of a morphism `f : X → Y` to domains `D` of `X` and `E` of `Y` with
`f(D) ⊆ E`. -/
def domainRestrict (D : (presentationOf X).AnalyticDomain) (E : (presentationOf Y).AnalyticDomain)
    (f : X ⟶ Y) (hf : ∀ x ∈ D.carrier, localizedSpaceFunctor.map f x ∈ E.carrier) :
    domainObj X D ⟶ domainObj Y E :=
  domainLift E (domainι X D ≫ f) (domainι_comp_apply_mem D E f hf)

@[reassoc (attr := simp)]
theorem domainRestrict_comp (D : (presentationOf X).AnalyticDomain)
    (E : (presentationOf Y).AnalyticDomain) (f : X ⟶ Y)
    (hf : ∀ x ∈ D.carrier, localizedSpaceFunctor.map f x ∈ E.carrier) :
    domainRestrict D E f hf ≫ domainι Y E = domainι X D ≫ f :=
  domainLift_comp _ _ _

theorem domainRestrict_id (D : (presentationOf X).AnalyticDomain) :
    domainRestrict D D (𝟙 X) (fun _ hx => hx) = 𝟙 _ :=
  (eq_domainLift _ _ _ (𝟙 _) (by rw [Category.id_comp, Category.comp_id])).symm

theorem domainRestrict_comp_domainRestrict (D : (presentationOf X).AnalyticDomain)
    (E : (presentationOf Y).AnalyticDomain) (F : (presentationOf Z).AnalyticDomain)
    (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : ∀ x ∈ D.carrier, localizedSpaceFunctor.map f x ∈ E.carrier)
    (hg : ∀ x ∈ E.carrier, localizedSpaceFunctor.map g x ∈ F.carrier)
    (hfg : ∀ x ∈ D.carrier, localizedSpaceFunctor.map (f ≫ g) x ∈ F.carrier) :
    domainRestrict D E f hf ≫ domainRestrict E F g hg = domainRestrict D F (f ≫ g) hfg :=
  eq_domainLift _ _ _ _ (by
    rw [Category.assoc, domainRestrict_comp, domainRestrict_comp_assoc])

end Objects

section Actions

variable {G : Type z} [Monoid G]

/-- A domain `D` of the space of an action of `G` is invariant if every element of `G` maps `D`
into itself. -/
def IsInvariantDomain (X : Action (LocalizedCategory.{u, v, w} (K := K)) G)
    (D : (presentationOf X.V).AnalyticDomain) : Prop :=
  ∀ (g : G), ∀ x ∈ D.carrier, localizedSpaceFunctor.map (X.ρ g) x ∈ D.carrier

variable (X : Action (LocalizedCategory.{u, v, w} (K := K)) G)
  (D : (presentationOf X.V).AnalyticDomain) (hD : IsInvariantDomain X D)

/-- The action of `G` on an invariant domain `D`: each element acts by the restriction of its
action on `X`. -/
def invariantDomainAction : Action (LocalizedCategory.{u, v, w} (K := K)) G where
  V := domainObj X.V D
  ρ :=
    { toFun := fun g => domainRestrict D D (X.ρ g) (hD g)
      map_one' := by
        refine (eq_domainLift _ _ _ _ ?_).symm
        rw [map_one, End.one_def, End.one_def, Category.id_comp, Category.comp_id]
      map_mul' := fun g h => by
        refine (eq_domainLift _ _ _ _ ?_).symm
        rw [End.mul_def, Category.assoc, domainRestrict_comp, ← Category.assoc,
          domainRestrict_comp, map_mul, End.mul_def, Category.assoc] }

@[simp]
theorem invariantDomainAction_V : (invariantDomainAction X D hD).V = domainObj X.V D :=
  rfl

theorem invariantDomainAction_ρ (g : G) :
    (invariantDomainAction X D hD).ρ g = domainRestrict D D (X.ρ g) (hD g) :=
  rfl

/-- The canonical morphism of an invariant domain is equivariant. -/
def invariantDomainInclusion : invariantDomainAction X D hD ⟶ X where
  hom := domainι X.V D
  comm g := domainRestrict_comp D D (X.ρ g) (hD g)

@[simp]
theorem invariantDomainInclusion_hom :
    (invariantDomainInclusion X D hD).hom = domainι X.V D :=
  rfl

/-- An equivariant morphism to `X` whose image lies in the invariant domain `D` factors through
`D`. -/
def invariantDomainLift {Y : Action (LocalizedCategory.{u, v, w} (K := K)) G} (f : Y ⟶ X)
    (hf : ∀ y, localizedSpaceFunctor.map f.hom y ∈ D.carrier) :
    Y ⟶ invariantDomainAction X D hD where
  hom := domainLift D f.hom hf
  comm g := by
    change Y.ρ g ≫ domainLift D f.hom hf = domainLift D f.hom hf ≫ domainRestrict D D (X.ρ g) (hD g)
    apply (cancel_mono (domainι X.V D)).1
    rw [Category.assoc, domainLift_comp, f.comm, Category.assoc, domainRestrict_comp,
      domainLift_comp_assoc]

@[reassoc (attr := simp)]
theorem invariantDomainLift_comp {Y : Action (LocalizedCategory.{u, v, w} (K := K)) G}
    (f : Y ⟶ X) (hf : ∀ y, localizedSpaceFunctor.map f.hom y ∈ D.carrier) :
    invariantDomainLift X D hD f hf ≫ invariantDomainInclusion X D hD = f :=
  Action.Hom.ext (domainLift_comp D f.hom hf)

instance invariantDomainInclusion_mono : Mono (invariantDomainInclusion X D hD) where
  right_cancellation _ _ h := Action.Hom.ext ((cancel_mono (domainι X.V D)).1
    (congrArg Action.Hom.hom h))

end Actions

section GSpaces

variable {G : Type z} [Group G] [TopologicalSpace G]

/-- An invariant domain of a `G`-space whose restricted action is continuous, as a `G`-space.
Its space is Hausdorff as a subspace of a Hausdorff space. -/
def invariantDomainGSpace (X : GSpace.{u, v, w} K G)
    (D : (presentationOf X.obj.V).AnalyticDomain) (hD : IsInvariantDomain X.obj D)
    (hc : IsContinuousAction (invariantDomainAction X.obj D hD).ρAut) : GSpace.{u, v, w} K G :=
  ⟨invariantDomainAction X.obj D hD, by
    have : T2Space (presentationOf X.obj.V).presentation.space := X.property.1
    exact ⟨inferInstanceAs (T2Space D.carrier), hc⟩⟩

/-- The canonical morphism of an invariant domain, as a morphism of `G`-spaces. -/
def invariantDomainGSpaceInclusion (X : GSpace.{u, v, w} K G)
    (D : (presentationOf X.obj.V).AnalyticDomain) (hD : IsInvariantDomain X.obj D)
    (hc : IsContinuousAction (invariantDomainAction X.obj D hD).ρAut) :
    invariantDomainGSpace X D hD hc ⟶ X :=
  ObjectProperty.homMk (invariantDomainInclusion X.obj D hD)

end GSpaces

end SaturatedAtlasPresentation

end Langlands.Analytic
