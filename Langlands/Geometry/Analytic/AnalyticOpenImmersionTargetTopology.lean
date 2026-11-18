import Langlands.Geometry.Analytic.AnalyticImmersion
import Langlands.Geometry.Analytic.EtaleOpenMap.Proof
import Langlands.Geometry.Analytic.LocalizedPullbackPoints

/-! # Underlying topology in etale target descent of open immersions -/

noncomputable section

universe u w

namespace Langlands.Analytic.SaturatedAtlasPresentation

open CategoryTheory Limits Set Topology

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {X Y V P : LocalizedCategory.{u, u, u} (K := K)}

/-- The inverse image of a point-set image in a categorical pullback is the
image of the inverse image. Only existence of compatible point lifts is used. -/
theorem preimage_image_eq_image_preimage_of_isPullback
    {p : P ⟶ X} {q : P ⟶ V} {f : X ⟶ Y} {g : V ⟶ Y}
    (h : IsPullback p q f g) (S : Set (localizedSpaceFunctor.obj X)) :
    localizedSpaceFunctor.map g ⁻¹' (localizedSpaceFunctor.map f '' S) =
      localizedSpaceFunctor.map q '' (localizedSpaceFunctor.map p ⁻¹' S) := by
  ext v
  constructor
  · rintro ⟨x, hx, hxv⟩
    obtain ⟨z, hzp, hzq⟩ := exists_point_of_isPullback p q f g h x v hxv
    exact ⟨z, by simpa only [Set.mem_preimage, hzp] using hx, hzq⟩
  · rintro ⟨z, hz, rfl⟩
    refine ⟨localizedSpaceFunctor.map p z, hz, ?_⟩
    have hw := congrArg (fun k => localizedSpaceFunctor.map k z) h.w
    simpa only [Functor.map_comp, TopCat.comp_app] using hw

variable {ι : Type w} {V P : ι → LocalizedCategory.{u, u, u} (K := K)}
  {f : X ⟶ Y} {g : ∀ i, V i ⟶ Y}
  {p : ∀ i, P i ⟶ X} {q : ∀ i, P i ⟶ V i}

/-- Images can be computed from the supplied pullbacks along a jointly
surjective family. This does not assert uniqueness of point lifts. -/
theorem image_eq_iUnion_of_isPullbacks
    (h : ∀ i, IsPullback (p i) (q i) f (g i))
    (hcover : ∀ y : localizedSpaceFunctor.obj Y,
      ∃ (i : ι) (v : localizedSpaceFunctor.obj (V i)),
        localizedSpaceFunctor.map (g i) v = y)
    (S : Set (localizedSpaceFunctor.obj X)) :
    localizedSpaceFunctor.map f '' S =
      ⋃ i, localizedSpaceFunctor.map (g i) ''
        (localizedSpaceFunctor.map (q i) '' (localizedSpaceFunctor.map (p i) ⁻¹' S)) := by
  ext y
  constructor
  · intro hy
    obtain ⟨i, v, hv⟩ := hcover y
    refine Set.mem_iUnion.mpr ⟨i, v, ?_, hv⟩
    rw [← preimage_image_eq_image_preimage_of_isPullback (h i) S]
    simpa only [Set.mem_preimage, hv] using hy
  · intro hy
    obtain ⟨i, v, hv, rfl⟩ := Set.mem_iUnion.mp hy
    rw [← preimage_image_eq_image_preimage_of_isPullback (h i) S] at hv
    exact hv

/-- Openness of the local pullback maps descends along an etale cover. -/
theorem isOpenMap_of_etalePullbacks
    (h : ∀ i, IsPullback (p i) (q i) f (g i))
    (hg : ∀ i, etale (g i))
    (hcover : ∀ y : localizedSpaceFunctor.obj Y,
      ∃ (i : ι) (v : localizedSpaceFunctor.obj (V i)),
        localizedSpaceFunctor.map (g i) v = y)
    (hq : ∀ i, IsOpenMap (localizedSpaceFunctor.map (q i))) :
    IsOpenMap (localizedSpaceFunctor.map f) := by
  intro S hS
  rw [image_eq_iUnion_of_isPullbacks h hcover S]
  apply isOpen_iUnion
  intro i
  exact etaleOpenMap K (g i) (hg i) _
    (hq i _ (hS.preimage (localizedSpaceFunctor.map (p i)).hom.continuous))

/-- Injectivity of point maps descends along a jointly surjective target
family when every supplied pullback has an injective second projection. -/
theorem injective_of_pullbacks
    (h : ∀ i, IsPullback (p i) (q i) f (g i))
    (hcover : ∀ y : localizedSpaceFunctor.obj Y,
      ∃ (i : ι) (v : localizedSpaceFunctor.obj (V i)),
        localizedSpaceFunctor.map (g i) v = y)
    (hq : ∀ i, Function.Injective (localizedSpaceFunctor.map (q i))) :
    Function.Injective (localizedSpaceFunctor.map f) := by
  intro x x' hxx'
  obtain ⟨i, v, hv⟩ := hcover (localizedSpaceFunctor.map f x)
  obtain ⟨z, hzp, hzq⟩ := exists_point_of_isPullback (p i) (q i) f (g i)
    (h i) x v hv.symm
  obtain ⟨z', hzp', hzq'⟩ := exists_point_of_isPullback (p i) (q i) f (g i)
    (h i) x' v (hxx'.symm.trans hv.symm)
  have hzz' : z = z' := hq i (hzq.trans hzq'.symm)
  exact hzp.symm.trans ((congrArg (localizedSpaceFunctor.map (p i)) hzz').trans hzp')

/-- Local analytic open immersions along an etale target cover make the
global point map an open embedding. This does not construct an analytic inverse. -/
theorem isOpenEmbedding_of_openImmersion_etalePullbacks
    (h : ∀ i, IsPullback (p i) (q i) f (g i))
    (hg : ∀ i, etale (g i))
    (hcover : ∀ y : localizedSpaceFunctor.obj Y,
      ∃ (i : ι) (v : localizedSpaceFunctor.obj (V i)),
        localizedSpaceFunctor.map (g i) v = y)
    (hq : ∀ i, openImmersion (q i)) :
    IsOpenEmbedding (localizedSpaceFunctor.map f) :=
  IsOpenEmbedding.of_continuous_injective_isOpenMap
    (localizedSpaceFunctor.map f).hom.continuous
    (injective_of_pullbacks h hcover fun i => (hq i).isOpenEmbedding.injective)
    (isOpenMap_of_etalePullbacks h hg hcover fun i => (hq i).isOpenEmbedding.isOpenMap)

/-- The image is an open subset, the candidate open analytic domain in
target descent of open immersions. -/
theorem isOpen_range_of_openImmersion_etalePullbacks
    (h : ∀ i, IsPullback (p i) (q i) f (g i))
    (hg : ∀ i, etale (g i))
    (hcover : ∀ y : localizedSpaceFunctor.obj Y,
      ∃ (i : ι) (v : localizedSpaceFunctor.obj (V i)),
        localizedSpaceFunctor.map (g i) v = y)
    (hq : ∀ i, openImmersion (q i)) :
    IsOpen (Set.range (localizedSpaceFunctor.map f)) :=
  (isOpenEmbedding_of_openImmersion_etalePullbacks h hg hcover hq).isOpen_range

/-- The open image domain detected by the local analytic open immersions. -/
def openImageDomainOfEtalePullbacks
    (h : ∀ i, IsPullback (p i) (q i) f (g i))
    (hg : ∀ i, etale (g i))
    (hcover : ∀ y : localizedSpaceFunctor.obj Y,
      ∃ (i : ι) (v : localizedSpaceFunctor.obj (V i)),
        localizedSpaceFunctor.map (g i) v = y)
    (hq : ∀ i, openImmersion (q i)) :
    (presentationOf Y).AnalyticDomain :=
  (presentationOf Y).openDomain (Set.range (localizedSpaceFunctor.map f))
    (isOpen_range_of_openImmersion_etalePullbacks h hg hcover hq)

/-- The canonical factorization through that open image domain. No analytic
inverse is asserted by this construction. -/
def openImageLiftOfEtalePullbacks
    (h : ∀ i, IsPullback (p i) (q i) f (g i))
    (hg : ∀ i, etale (g i))
    (hcover : ∀ y : localizedSpaceFunctor.obj Y,
      ∃ (i : ι) (v : localizedSpaceFunctor.obj (V i)),
        localizedSpaceFunctor.map (g i) v = y)
    (hq : ∀ i, openImmersion (q i)) :
    X ⟶ domainObj Y (openImageDomainOfEtalePullbacks h hg hcover hq) :=
  domainLift _ f fun x => ⟨x, rfl⟩

@[reassoc (attr := simp)]
theorem openImageLiftOfEtalePullbacks_comp
    (h : ∀ i, IsPullback (p i) (q i) f (g i))
    (hg : ∀ i, etale (g i))
    (hcover : ∀ y : localizedSpaceFunctor.obj Y,
      ∃ (i : ι) (v : localizedSpaceFunctor.obj (V i)),
        localizedSpaceFunctor.map (g i) v = y)
    (hq : ∀ i, openImmersion (q i)) :
    openImageLiftOfEtalePullbacks h hg hcover hq ≫
      domainι Y (openImageDomainOfEtalePullbacks h hg hcover hq) = f :=
  domainLift_comp _ _ _

end Langlands.Analytic.SaturatedAtlasPresentation
