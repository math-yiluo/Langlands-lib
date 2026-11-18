import Langlands.Geometry.Analytic.AnalyticImmersion
import Mathlib.CategoryTheory.MorphismProperty.Limits

/-! # Pullbacks of analytic open immersions -/

noncomputable section

universe u v w

namespace Langlands.Analytic.SaturatedAtlasPresentation

open CategoryTheory Limits Set Topology

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {X Y Z T : LocalizedCategory.{u, v, w} (K := K)}

/-- The inverse image of an open analytic domain under an analytic morphism. -/
def preimageOpenDomain (f : X ⟶ Y)
    (U : Set (presentationOf Y).presentation.space) (hU : IsOpen U) :
    (presentationOf X).AnalyticDomain :=
  (presentationOf X).openDomain (localizedSpaceFunctor.map f ⁻¹' U)
    (hU.preimage (localizedSpaceFunctor.map f).hom.continuous)

/-- The restriction of an analytic morphism to the inverse image of an open domain. -/
def preimageOpenDomainMap (f : X ⟶ Y)
    (U : Set (presentationOf Y).presentation.space) (hU : IsOpen U) :
    domainObj X (preimageOpenDomain f U hU) ⟶
      domainObj Y ((presentationOf Y).openDomain U hU) :=
  domainRestrict (preimageOpenDomain f U hU) ((presentationOf Y).openDomain U hU)
    f (fun _ hx => hx)

@[reassoc (attr := simp)]
theorem preimageOpenDomainMap_comp (f : X ⟶ Y)
    (U : Set (presentationOf Y).presentation.space) (hU : IsOpen U) :
    preimageOpenDomainMap f U hU ≫ domainι Y ((presentationOf Y).openDomain U hU) =
      domainι X (preimageOpenDomain f U hU) ≫ f :=
  domainRestrict_comp _ _ _ _

/-- The inverse image open domain is the categorical pullback of its inclusion. -/
theorem isPullback_preimageOpenDomain (f : X ⟶ Y)
    (U : Set (presentationOf Y).presentation.space) (hU : IsOpen U) :
    IsPullback (preimageOpenDomainMap f U hU) (domainι X (preimageOpenDomain f U hU))
      (domainι Y ((presentationOf Y).openDomain U hU)) f := by
  apply IsPullback.mk' (preimageOpenDomainMap_comp f U hU)
  · intro T a b _ hab
    exact (cancel_mono (domainι X (preimageOpenDomain f U hU))).1 hab
  · intro T a b hab
    have hb : ∀ t, localizedSpaceFunctor.map b t ∈ (preimageOpenDomain f U hU).carrier := by
      intro t
      change localizedSpaceFunctor.map f (localizedSpaceFunctor.map b t) ∈ U
      have ht := congrArg (fun k => localizedSpaceFunctor.map k t) hab
      rw [Functor.map_comp, TopCat.comp_app, domainι_apply,
        Functor.map_comp, TopCat.comp_app] at ht
      exact ht ▸ (localizedSpaceFunctor.map a t).property
    refine ⟨domainLift (preimageOpenDomain f U hU) b hb, ?_, domainLift_comp _ _ _⟩
    apply (cancel_mono (domainι Y ((presentationOf Y).openDomain U hU))).1
    rw [Category.assoc, preimageOpenDomainMap_comp, ← Category.assoc,
      domainLift_comp, hab]

/-- Any pullback of an open-domain inclusion is canonically the inverse image domain. -/
def openDomainPullbackIso (f : X ⟶ Y)
    (U : Set (presentationOf Y).presentation.space) (hU : IsOpen U)
    {P : LocalizedCategory.{u, v, w} (K := K)}
    {p : P ⟶ domainObj Y ((presentationOf Y).openDomain U hU)} {q : P ⟶ X}
    (h : IsPullback p q (domainι Y ((presentationOf Y).openDomain U hU)) f) :
    P ≅ domainObj X (preimageOpenDomain f U hU) :=
  h.isoIsPullback _ _ (isPullback_preimageOpenDomain f U hU)

@[reassoc (attr := simp)]
theorem openDomainPullbackIso_hom_snd (f : X ⟶ Y)
    (U : Set (presentationOf Y).presentation.space) (hU : IsOpen U)
    {P : LocalizedCategory.{u, v, w} (K := K)}
    {p : P ⟶ domainObj Y ((presentationOf Y).openDomain U hU)} {q : P ⟶ X}
    (h : IsPullback p q (domainι Y ((presentationOf Y).openDomain U hU)) f) :
    (openDomainPullbackIso f U hU h).hom ≫ domainι X (preimageOpenDomain f U hU) = q :=
  h.isoIsPullback_hom_snd _ _ (isPullback_preimageOpenDomain f U hU)

/-- Analytic open immersions remain open immersions in every pullback square. -/
theorem openImmersion.of_isPullback {p : T ⟶ Y} {q : T ⟶ X} {g : Y ⟶ Z} {f : X ⟶ Z}
    (h : IsPullback p q g f) (hg : openImmersion g) : openImmersion q := by
  obtain ⟨U, hU, e, he⟩ := hg
  have h' : IsPullback (p ≫ e.hom) q (domainι Z ((presentationOf Z).openDomain U hU)) f :=
    h.of_iso (Iso.refl _) e (Iso.refl _) (Iso.refl _)
      (by simp) (by simp) (by simpa using he.symm) (by simp)
  exact ⟨_, _, openDomainPullbackIso f U hU h', openDomainPullbackIso_hom_snd f U hU h'⟩

instance : (openImmersion : MorphismProperty (LocalizedCategory.{u, v, w} (K := K))).IsStableUnderBaseChange where
  of_isPullback h hg := openImmersion.of_isPullback h hg

end Langlands.Analytic.SaturatedAtlasPresentation
