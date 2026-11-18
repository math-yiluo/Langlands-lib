import Langlands.Geometry.Analytic.AnalyticImmersion
import Langlands.Geometry.Analytic.EtaleOpenMap.Proof
import Langlands.Geometry.Analytic.SpaceAnalytificationAffinePullback
import Langlands.Geometry.Analytic.SpaceAnalytificationEtaleReflection
import Langlands.AlgebraicGeometry.AlgebraicSpace.SliceOpenGluing
import Langlands.AlgebraicGeometry.AlgebraicSpace.SmoothDimensionRestrictions

/-! # Preservation of open immersions from analytic Hom descent -/

noncomputable section

universe u w

open CategoryTheory CategoryTheory.Limits
open _root_.AlgebraicGeometry
open Langlands.AlgebraicGeometry Langlands.AlgebraicGeometry.AlgebraicSpace

namespace Langlands.Analytic.SaturatedAtlasPresentation

variable {K : Type u} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable {X Y Z : LocalizedCategory.{u, u, u} (K := K)}
  {ι : Type w} {U : ι → LocalizedCategory.{u, u, u} (K := K)}

/-- Compatible analytic maps on a jointly surjective étale family have a
unique amalgamation under the analytic Hom sheaf premise. -/
private theorem existsUnique_of_etaleCover
    (hHom : Presieve.IsSheaf (etaleTopology X)
      ((MorphismProperty.Over.forget _ _ X ⋙ Over.forget X).op ⋙ yoneda.obj Z))
    (g : ∀ i, U i ⟶ X) (hg : ∀ i, etale (g i))
    (hcover : ∀ x : localizedSpaceFunctor.obj X,
      ∃ (i : ι) (z : localizedSpaceFunctor.obj (U i)), localizedSpaceFunctor.map (g i) z = x)
    (a : ∀ i, U i ⟶ Z)
    (hCompat : ∀ (i j : ι) {T : LocalizedCategory.{u, u, u} (K := K)}
      (r : T ⟶ U i) (s : T ⟶ U j), r ≫ g i = s ≫ g j → r ≫ a i = s ≫ a j) :
    ∃! b : X ⟶ Z, ∀ i, g i ≫ b = a i := by
  let B : EtaleSite X := MorphismProperty.Over.mk ⊤ (𝟙 X) (etale_of_isIso _)
  let V (i : ι) : EtaleSite X := MorphismProperty.Over.mk ⊤ (g i) (hg i)
  let π (i : ι) : V i ⟶ B := MorphismProperty.Over.homMk (g i) (Category.comp_id _)
  let P := (MorphismProperty.Over.forget etale ⊤ X ⋙ Over.forget X).op ⋙ yoneda.obj Z
  have hπ : Presieve.ofArrows V π ∈ etalePrecoverage X B :=
    ofArrows_mem_etalePrecoverage_iff.mpr hcover
  have hc : Presieve.Arrows.Compatible P π a := fun i j _ r s h =>
    hCompat i j r.left s.left (congrArg (fun m => m.left) h)
  exact (Presieve.isSheafFor_arrows_iff (π := π) (P := P)).mp
    (hHom.isSheafFor_of_mem_precoverage hπ) a hc

/-- The range of a map is open when its composites with a jointly surjective
source family are étale. -/
theorem isOpen_range_of_etale_composites (f : X ⟶ Y)
    (g : ∀ i, U i ⟶ X)
    (hcover : ∀ x : localizedSpaceFunctor.obj X,
      ∃ (i : ι) (z : localizedSpaceFunctor.obj (U i)), localizedSpaceFunctor.map (g i) z = x)
    (he : ∀ i, etale (g i ≫ f)) :
    IsOpen (Set.range (localizedSpaceFunctor.map f)) := by
  have h : Set.range (localizedSpaceFunctor.map f) =
      ⋃ i, Set.range (localizedSpaceFunctor.map (g i ≫ f)) := by
    ext y
    simp only [Set.mem_range, Set.mem_iUnion, Functor.map_comp, TopCat.comp_app]
    constructor
    · rintro ⟨x, rfl⟩
      obtain ⟨i, z, rfl⟩ := hcover x
      exact ⟨i, z, rfl⟩
    · rintro ⟨i, z, rfl⟩
      exact ⟨localizedSpaceFunctor.map (g i) z, rfl⟩
  rw [h]
  exact isOpen_iUnion fun i => (etaleOpenMap K (g i ≫ f) (he i)).isOpen_range

section OpenImage

variable (hBase : LocalizedEtalePullbackStatement.{u, u} K)
  (hHom : ∀ (S T : LocalizedCategory.{u, u, u} (K := K)),
    Presieve.IsSheaf (etaleTopology S)
      ((MorphismProperty.Over.forget _ _ S ⋙ Over.forget S).op ⋙ yoneda.obj T))
  (f : X ⟶ Y) (g : ∀ i, U i ⟶ X) (hg : ∀ i, etale (g i))
  (hcover : ∀ x : localizedSpaceFunctor.obj X,
    ∃ (i : ι) (z : localizedSpaceFunctor.obj (U i)), localizedSpaceFunctor.map (g i) z = x)
  (he : ∀ i, etale (g i ≫ f))
  (hCompat : ∀ (i j : ι) {T : LocalizedCategory.{u, u, u} (K := K)}
    (r : T ⟶ U i) (s : T ⟶ U j),
    r ≫ g i ≫ f = s ≫ g j ≫ f → r ≫ g i = s ≫ g j)

/-- An étale source cover with étale composites and common overlap
relations gives an analytic isomorphism onto the open image domain. -/
def openImageIsoOfEtaleSourceCover :
    let D := (presentationOf Y).openDomain (Set.range (localizedSpaceFunctor.map f))
      (isOpen_range_of_etale_composites f g hcover he)
    {e : X ≅ domainObj Y D // e.hom ≫ domainι Y D = f} := by
  dsimp only
  let D := (presentationOf Y).openDomain (Set.range (localizedSpaceFunctor.map f))
    (isOpen_range_of_etale_composites f g hcover he)
  let d := domainι Y D
  let a := domainLift D f (fun x => ⟨x, rfl⟩)
  have ha : a ≫ d = f := domainLift_comp D f _
  let q (i : ι) : U i ⟶ domainObj Y D := g i ≫ a
  have hq (i : ι) : q i ≫ d = g i ≫ f := by simp only [q, Category.assoc, ha]
  have hqEtale (i : ι) : etale (q i) :=
    SpaceAnalytification.etale_snd_of_isPullback_of_etalePullbacks K hBase
      (IsPullback.of_horiz_isIso_mono (fst := 𝟙 (U i))
        (g := domainι Y D) ⟨(Category.id_comp _).trans (hq i).symm⟩) (he i)
  have hqCover (z : localizedSpaceFunctor.obj (domainObj Y D)) :
      ∃ (i : ι) (t : localizedSpaceFunctor.obj (U i)), localizedSpaceFunctor.map (q i) t = z := by
    obtain ⟨x, hx⟩ := z.property
    obtain ⟨i, t, ht⟩ := hcover x
    refine ⟨i, t, Subtype.ext ?_⟩
    have hh := congrArg (fun k : U i ⟶ Y => localizedSpaceFunctor.map k t) (hq i)
    simp only [Functor.map_comp, TopCat.comp_app, d, domainι_apply, ht, hx] at hh
    exact hh
  have hGlue := existsUnique_of_etaleCover (hHom (domainObj Y D) X) q hqEtale hqCover g
    (fun i j {_} r s h => hCompat i j r s (by
      simpa only [Category.assoc, hq] using congrArg (fun k => k ≫ d) h))
  obtain ⟨b, hb⟩ := Classical.indefiniteDescription _ hGlue.exists
  have hab : a ≫ b = 𝟙 X :=
    (existsUnique_of_etaleCover (hHom X X) g hg hcover g (fun _ _ {_} _ _ h => h)).unique
      (fun i => (Category.assoc _ _ _).symm.trans (hb i)) (fun i => Category.comp_id _)
  have hba : b ≫ a = 𝟙 (domainObj Y D) :=
    (existsUnique_of_etaleCover (hHom (domainObj Y D) (domainObj Y D)) q hqEtale hqCover q
      (fun _ _ {_} _ _ h => h)).unique
      (fun i => (Category.assoc _ _ _).symm.trans (congrArg (· ≫ a) (hb i)))
      (fun i => Category.comp_id _)
  exact ⟨⟨a, b, hab, hba⟩, ha⟩

end OpenImage

end Langlands.Analytic.SaturatedAtlasPresentation

namespace Langlands.Analytic.SpaceAnalytification

open SaturatedAtlasPresentation

variable (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]

/-- The open-immersion preservation direction uses localized étale
pullbacks and the analytic Hom sheaf property. -/
theorem openImmersion_of_isOpenImmersion_of_homSheaf
    (hBase : LocalizedEtalePullbackStatement.{u, u} K)
    (hHom : ∀ (S T : LocalizedCategory.{u, u, u} (K := K)),
      Presieve.IsSheaf (etaleTopology S)
        ((MorphismProperty.Over.forget _ _ S ⋙ Over.forget S).op ⋙ yoneda.obj T))
    {X' X : AlgebraicSpace (Spec (CommRingCat.of K))} (f : X' ⟶ X)
    (hX' : IsSeparated X')
    {Y' Y : LocalizedCategory.{u, u, u} (K := K)}
    {p' : PointFamily K X' Y'} {p : PointFamily K X Y}
    (hp' : IsAnalytification K X' Y' p') (hp : IsAnalytification K X Y p)
    (F : Y' ⟶ Y)
    (hF : ∀ (A : Type u) [CommRing A] [Algebra K A]
      (P : FinitePolynomialPresentation K A) (x : RingPoints K X' A),
      p' A P x ≫ F = p A P (RingPoints.map f x))
    (hf : AlgebraicSpace.IsOpenImmersion (hom f)) :
    openImmersion F := by
  let g (i : EtaleAffineTest K X') := p' i.algebra i.presentation i.point
  have hg (i : EtaleAffineTest K X') : etale (g i) :=
    hp'.etale_map i.presentation i.point i.etale_point
  have hcover (x : localizedSpaceFunctor.obj Y') :
      ∃ (i : EtaleAffineTest K X') (z : localizedSpaceFunctor.obj _),
        localizedSpaceFunctor.map (g i) z = x := by
    obtain ⟨A, _, _, P, y, hy, hz⟩ := hp'.jointly_surjective x
    exact ⟨⟨CommAlgCat.of K A, P, y, hy⟩, hz⟩
  have he' (i : EtaleAffineTest K X') :
      g i ≫ F = p i.algebra i.presentation (RingPoints.map f i.point) :=
    hF i.algebra i.presentation i.point
  have hf' := PointOpenSubspace.isEtale_of_isOpenImmersion hf
  have he (i : EtaleAffineTest K X') : etale (g i ≫ F) := by
    rw [he' i]
    apply hp.etale_map
    rw [pointHom_map]
    exact i.etale_point.comp hf'
  let : Mono (hom f) := SliceOpenGluing.relative_monomorphisms_le_monomorphisms _
    (MorphismProperty.relative_monotone SliceOpenGluing.openProperty_le_monomorphisms _ hf)
  have hCompat (i j : EtaleAffineTest K X') {T : LocalizedCategory.{u, u, u} (K := K)}
      (r : T ⟶ _) (s : T ⟶ _) (h : r ≫ g i ≫ F = s ≫ g j ≫ F) :
      r ≫ g i = s ≫ g j := by
    obtain ⟨C, _, _, R, a, b, _, hpb⟩ :=
      hasClosedAffinePointPullbacks_of_isSeparated hX'
        i.algebra i.presentation j.algebra j.presentation i.point j.point
    have hpbY : IsPullback
        ((schemeYoneda _).map (PointTopology.ringTestMap K a))
        ((schemeYoneda _).map (PointTopology.ringTestMap K b))
        (pointHom K (RingPoints.map f i.point))
        (pointHom K (RingPoints.map f j.point)) := by
      rw [pointHom_map, pointHom_map]
      refine IsPullback.mk' ?_ (fun {_ _ _} h₁ h₂ => hpb.hom_ext h₁ h₂) ?_
      · rw [← Category.assoc, hpb.w, Category.assoc]
      · intro _ a' b' hab
        have hab' : a' ≫ pointHom K i.point = b' ≫ pointHom K j.point :=
          (cancel_mono (hom f)).mp (by simpa only [Category.assoc] using hab)
        exact ⟨hpb.lift a' b' hab', hpb.lift_fst _ _ _, hpb.lift_snd _ _ _⟩
    have hpbY' := hp'.isPullback i.presentation j.presentation R a b i.point j.point hpb
    have hpbY'' := hp.isPullback i.presentation j.presentation R a b
      (RingPoints.map f i.point) (RingPoints.map f j.point) hpbY
    rw [he' i, he' j] at h
    let l := hpbY''.lift r s h
    have hr := hpbY''.lift_fst r s h
    have hs := hpbY''.lift_snd r s h
    exact (congrArg (· ≫ g i) hr).symm.trans
      ((Category.assoc _ _ _).trans
        (congrArg (l ≫ ·) hpbY'.w |>.trans
          ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ g j) hs))))
  obtain ⟨e, h⟩ := openImageIsoOfEtaleSourceCover
    (hBase := hBase) (hHom := hHom) (f := F) (g := g) (hg := hg)
    (hcover := hcover) (he := he) (hCompat := hCompat)
  exact ⟨_, isOpen_range_of_etale_composites F g hcover he, e, h⟩

end Langlands.Analytic.SpaceAnalytification
