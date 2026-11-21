import Langlands.Cohomology.AnalyticEtaleGermNeighborhoods
import Langlands.Cohomology.AnalyticGaloisSiteCover
import Langlands.Cohomology.GaloisGermCartanTransport

/-! # Relative analytic Galois covers of étale germs -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace Langlands.Sheaf.Equivariant.Analytic

open _root_.CategoryTheory _root_.CategoryTheory.Limits TopologicalSpace
open Langlands.Analytic Langlands.Analytic.SaturatedAtlasPresentation
open Langlands.Cohomology

universe u v uL z

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable {X : LocalizedCategory.{u, v, v} (K := K)}

instance etaleOpenRestrictionInclusion_mono (T : Opens (localizedSpaceFunctor.obj X))
    (A : EtaleSite X) : Mono ((etaleOpenRestrictionInclusion X T).app A) where
  right_cancellation {B} f g e := by
    apply MorphismProperty.Over.Hom.ext
    apply (cancel_mono (restrictEtaleInclusion X T A)).mp
    exact congrArg (fun a : B ⟶ A => a.left) e

instance etaleOpenRestrictionMap_mono {T U : Opens (localizedSpaceFunctor.obj X)}
    (i : T ⟶ U) (A : EtaleSite X) :
    Mono (((etaleOpenRestrictionFunctor X).map i).app A) := by
  have h := congrArg (fun n => n.app A) (etaleOpenRestrictionInclusion_naturality X i)
  change ((etaleOpenRestrictionFunctor X).map i).app A ≫
    (etaleOpenRestrictionInclusion X U).app A = _ at h
  have : Mono (((etaleOpenRestrictionFunctor X).map i).app A ≫
      (etaleOpenRestrictionInclusion X U).app A) := h.symm ▸ inferInstance
  exact mono_of_mono _ ((etaleOpenRestrictionInclusion X U).app A)

/-- The square of restriction inclusions for an arrow of the site is a pullback. -/
theorem isPullback_etaleOpenRestriction (T : Opens (localizedSpaceFunctor.obj X))
    {A B : EtaleSite X} (f : A ⟶ B) :
    IsPullback (((etaleOpenRestrictionFunctor X).obj T).map f)
      ((etaleOpenRestrictionInclusion X T).app A) ((etaleOpenRestrictionInclusion X T).app B) f := by
  let j := etaleOpenRestrictionInclusion X T
  refine IsPullback.mk' (j.naturality f) (by
    intro Z a b _ h
    exact (cancel_mono (j.app A)).mp h) ?_
  intro Z g k h
  let g₁ := g.left ≫ (restrictEtaleObject X T B).hom
  have he : g₁ ≫ (openEtaleObject X T).hom = k.left ≫ A.hom := by
    have h' : g.left ≫ restrictEtaleInclusion X T B = k.left ≫ f.left :=
      congrArg (fun a : Z ⟶ B => a.left) h
    have hB := (isPullback_restrictEtale X T B).w
    change (g.left ≫ (restrictEtaleObject X T B).hom) ≫ (openEtaleObject X T).hom =
      k.left ≫ A.hom
    rw [Category.assoc, hB, ← Category.assoc, h', Category.assoc, MorphismProperty.Over.w f]
  let q : Z.left ⟶ (((etaleOpenRestrictionFunctor X).obj T).obj A).left :=
    (isPullback_restrictEtale X T A).lift g₁ k.left he
  have hq : q ≫ restrictEtaleInclusion X T A = k.left :=
    (isPullback_restrictEtale X T A).lift_snd _ _ _
  let l : Z ⟶ ((etaleOpenRestrictionFunctor X).obj T).obj A :=
    MorphismProperty.Over.homMk q (by
      rw [← MorphismProperty.Over.w (j.app A)]
      change q ≫ restrictEtaleInclusion X T A ≫ A.hom = Z.hom
      rw [← Category.assoc, hq]
      exact MorphismProperty.Over.w k)
  have hl : l ≫ j.app A = k := MorphismProperty.Over.Hom.ext hq
  refine ⟨l, (cancel_mono (j.app B)).mp ?_, hl⟩
  rw [Category.assoc, j.naturality, ← Category.assoc, hl]
  exact h.symm

private def siteGaloisCoverOfPullback {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C} {Γ : Type z} [Group Γ]
    {A B A' B' : C} (D : GaloisCovering J Γ A B)
    {p : A' ⟶ B'} {a : A' ⟶ A} {b : B' ⟶ B} [Mono a] [Mono b]
    (h : IsPullback p a b D.p) (deck : Γ → (A' ⟶ A'))
    (hdeck : ∀ γ, deck γ ≫ a = a ≫ D.deck γ) :
    GaloisCovering J Γ A' B' where
  p := p
  covering := by
    apply J.superset_covering _ (J.pullback_stable b D.covering)
    rintro Z f ⟨_, q, _, ⟨j⟩, hq⟩
    exact ⟨A', h.lift f q hq.symm, p, ⟨()⟩, h.lift_fst _ _ _⟩
  deck := deck
  deck_one := (cancel_mono a).mp (by simp [hdeck, D.deck_one])
  deck_mul γ δ := (cancel_mono a).mp (by
    simp [Category.assoc, hdeck, reassoc_of% (hdeck δ), D.deck_mul])
  deck_comp γ := (cancel_mono b).mp (by
    simp [Category.assoc, h.w, reassoc_of% (hdeck γ), D.deck_comp])
  locally_transitive f g hfg := by
    have he : (f ≫ a) ≫ D.p = (g ≫ a) ≫ D.p := by
      simpa only [Category.assoc, h.w] using congrArg (· ≫ b) hfg
    apply J.superset_covering _ (D.locally_transitive (f ≫ a) (g ≫ a) he)
    rintro Z k ⟨γ, hk⟩
    refine ⟨γ, (cancel_mono a).mp ?_⟩
    simpa only [Category.assoc, hdeck] using hk
  locally_free f γ hf := D.locally_free (f ≫ a) γ (by
    simpa only [Category.assoc, hdeck] using congrArg (· ≫ a) hf)

variable {y : localizedSpaceFunctor.obj X}

/-- A finite Galois cover over an ambient open restriction of a pointed étale object. -/
structure EtaleGermGaloisCover (V : EtaleGermNeighborhood X y) where
  baseOpen : Opens (localizedSpaceFunctor.obj X)
  mem_baseOpen : y ∈ baseOpen
  source : EtaleGermNeighborhood X y
  Γ : Type
  [instGroup : Group Γ]
  [instFinite : Finite Γ]
  p : source.obj ⟶ (V.restrict baseOpen mem_baseOpen).obj
  geometry : AnalyticGaloisCover Γ p.left
  distinguished : IsDistinguishedEtale source.obj.hom

attribute [instance] EtaleGermGaloisCover.instGroup EtaleGermGaloisCover.instFinite

namespace EtaleGermGaloisCover

variable {V : EtaleGermNeighborhood X y} (E : EtaleGermGaloisCover V)

/-- The cover arrow as a morphism to the unrestricted base object. -/
def toBase : E.source.obj ⟶ V.obj :=
  E.p ≫ (etaleOpenRestrictionInclusion X E.baseOpen).app V.obj

private abbrev siteCover :
    GaloisCovering (etaleTopology X) E.Γ E.source.obj (V.restrict E.baseOpen E.mem_baseOpen).obj :=
  E.geometry.toEtaleSiteCover E.p

private theorem stage_isPullback {T : Opens (localizedSpaceFunctor.obj X)} (hT : T ≤ E.baseOpen) :
    IsPullback (((etaleOpenRestrictionFunctor X).obj T).map E.toBase)
      ((etaleOpenRestrictionInclusion X T).app E.source.obj)
      (((etaleOpenRestrictionFunctor X).map (CategoryTheory.homOfLE hT)).app V.obj) E.p := by
  let i := _root_.CategoryTheory.homOfLE hT
  let j := (etaleOpenRestrictionInclusion X E.baseOpen).app V.obj
  let b := ((etaleOpenRestrictionFunctor X).map i).app V.obj
  have hi : b ≫ j = (etaleOpenRestrictionInclusion X T).app V.obj :=
    congrArg (fun η => η.app V.obj) (etaleOpenRestrictionInclusion_naturality X i)
  let H := isPullback_etaleOpenRestriction T E.toBase
  refine IsPullback.mk' ((cancel_mono j).mp ?_) (by
    intro Z f g _ h
    exact (cancel_mono ((etaleOpenRestrictionInclusion X T).app E.source.obj)).mp h) ?_
  · change (_ ≫ b) ≫ j = (_ ≫ E.p) ≫ j
    simpa only [Category.assoc, hi, toBase] using H.w
  · intro Z a c e
    exact H.exists_lift a c (by
      have he : (a ≫ b) ≫ j = (c ≫ E.p) ≫ j := congrArg (· ≫ j) e
      simpa only [Category.assoc, hi, toBase] using he)

/-- The ordinary site cover at an open stage smaller than the cover's base open. -/
def stageCover {T : Opens (localizedSpaceFunctor.obj X)} (hT : T ≤ E.baseOpen) :
    GaloisCovering (etaleTopology X) E.Γ
      (((etaleOpenRestrictionFunctor X).obj T).obj E.source.obj)
      (((etaleOpenRestrictionFunctor X).obj T).obj V.obj) :=
  siteGaloisCoverOfPullback E.siteCover (E.stage_isPullback hT)
    (fun γ => ((etaleOpenRestrictionFunctor X).obj T).map (E.siteCover.deck γ))
    (fun γ => (etaleOpenRestrictionInclusion X T).naturality (E.siteCover.deck γ))

theorem stageDeck_comp_inclusion {T : Opens (localizedSpaceFunctor.obj X)} (hT : T ≤ E.baseOpen)
    (γ : E.Γ) :
    ((E.stageCover hT).deck γ).left ≫ restrictEtaleInclusion X T E.source.obj =
      restrictEtaleInclusion X T E.source.obj ≫ (E.geometry.deck γ).hom :=
  congrArg (fun a => a.left)
    ((etaleOpenRestrictionInclusion X T).naturality (E.siteCover.deck γ))

abbrev coverIndex : Type (max u (v + 1) uL) :=
  distinguishedNbhdIndex.{u, v, uL} X y E.baseOpen

abbrev indexInclusion : coverIndex.{u, v, uL} E ⥤ nbhdIndex.{u, v, uL} X y :=
  (distinguishedNbhdProperty.{u, v, uL} X y E.baseOpen).ι

/-- The two étale diagrams over the distinguished opens of the cover. -/
abbrev coverDiagram : coverIndex.{u, v, uL} E ⥤ EtaleSite X :=
  E.indexInclusion ⋙ etaleNeighborhoodDiagram.{u, v, uL} X y E.source.obj

abbrev baseDiagram : coverIndex.{u, v, uL} E ⥤ EtaleSite X :=
  E.indexInclusion ⋙ etaleNeighborhoodDiagram.{u, v, uL} X y V.obj

theorem distinguished_stage (i : coverIndex.{u, v, uL} E) :
    IsDistinguishedEtale ((coverDiagram.{u, v, uL} E).obj i).hom := by
  let T := (nbhdOpen.{u, v, uL} X y).obj i.obj
  have h := MorphismProperty.Over.w ((etaleOpenRestrictionInclusion X T).app E.source.obj)
  change IsDistinguishedEtale (((etaleOpenRestrictionFunctor X).obj T).obj E.source.obj).hom
  rw [← h]
  exact E.distinguished.restrictToDistinguishedOpen i.property.2

private def stageMap {A B : EtaleSite X} (f : A ⟶ B) :
    indexInclusion.{u, v, uL} E ⋙ etaleNeighborhoodDiagram.{u, v, uL} X y A ⟶
      E.indexInclusion ⋙ etaleNeighborhoodDiagram.{u, v, uL} X y B where
  app i := ((etaleOpenRestrictionFunctor X).obj ((nbhdOpen X y).obj i.obj)).map f
  naturality _ _ g :=
    (((etaleOpenRestrictionFunctor X).map ((nbhdOpen X y).map g.hom)).naturality f).symm

/-- The finite Galois datum of the distinguished neighbourhood diagrams. -/
def germDatum :
    GaloisGerms.GermGaloisDatum (etaleTopology X) (ULift.{max u (v + 1) uL} E.Γ)
      (coverDiagram.{u, v, uL} E) (baseDiagram.{u, v, uL} E) where
  p := E.stageMap E.toBase
  deck γ := E.stageMap (E.siteCover.deck γ.down)
  deck_one := NatTrans.ext (funext fun i => (E.stageCover i.property.1).deck_one)
  deck_mul γ δ := NatTrans.ext (funext fun i => (E.stageCover i.property.1).deck_mul γ.down δ.down)
  deck_comp γ := NatTrans.ext (funext fun i => (E.stageCover i.property.1).deck_comp γ.down)
  covering i := (E.stageCover i.property.1).covering
  locally_transitive := by
    intro i U f g h
    apply (etaleTopology X).superset_covering _
      ((E.stageCover i.property.1).locally_transitive f g h)
    rintro T a ⟨γ, ha⟩
    exact ⟨ULift.up γ, ha⟩
  locally_free := by
    intro i U f γ h
    rcases (E.stageCover i.property.1).locally_free f γ.down h with hγ | he
    · exact Or.inl (ULift.ext _ _ hγ)
    · exact Or.inr he

variable (R : Type (max u (v + 1) uL)) [CommRing R]

/-- Étale section germs along the base-open neighbourhoods of a pointed object. -/
def etaleSectionGerm (V : EtaleGermNeighborhood X y) :
    Sheaf (etaleTopology X) (ModuleCat.{max u (v + 1) uL} R) ⥤
      ModuleCat.{max u (v + 1) uL} R :=
  GaloisGerms.germ (etaleTopology X) R (etaleNeighborhoodDiagram.{u, v, uL} X y V.obj)

variable {G : Type z} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {ρ : G →* Aut X}
variable [T2Space (localizedSpaceFunctor.obj X)]

/-- A pointed analytic Galois cover gives a Cartan germ cover by cofinal
comparison along the distinguished opens inside its base open. -/
def toGermCover (hρ : IsContinuousAction ρ) :
    GaloisGerms.GermCover (etaleTopology X) R
      (etaleSectionGerm.{u, v, uL} R V) (etaleSectionGerm.{u, v, uL} R E.source) := by
  letI := distinguishedNbhdIndex_isCofiltered.{u, v, uL} hρ E.mem_baseOpen
  letI := distinguishedNbhdInclusion_initial.{u, v, uL} hρ E.mem_baseOpen
  exact
    { Index := coverIndex.{u, v, uL} E
      base := E.baseDiagram
      covering := E.coverDiagram
      Γ := ULift.{max u (v + 1) uL} E.Γ
      datum := E.germDatum
      baseIso := GaloisGerms.germReindexIso (etaleTopology X) R _ E.indexInclusion
      coveringIso := GaloisGerms.germReindexIso (etaleTopology X) R _ E.indexInclusion }

end EtaleGermGaloisCover
end Langlands.Sheaf.Equivariant.Analytic
