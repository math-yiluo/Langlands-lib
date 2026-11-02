import Langlands.AlgebraicGeometry.AlgebraicSpace.EtalePresentationComparison
import Langlands.AlgebraicGeometry.AlgebraicSpace.SmoothRelationQuotientStatement

/-! # Etale local sections of smooth surjective scheme morphisms -/

universe u

open CategoryTheory Opposite AlgebraicGeometry

namespace Langlands.AlgebraicGeometry

/-- Every smooth surjective morphism of actual schemes has a section after
pullback along a single surjective etale morphism of schemes. -/
def SmoothSurjectiveEtaleLocalSectionsStatement : Prop :=
  ∀ (W T : Scheme.{u}) (f : W ⟶ T), Smooth f → Surjective f →
    ∃ (V : Scheme.{u}) (e : V ⟶ T) (s : V ⟶ W),
      Etale e ∧ Surjective e ∧ s ≫ f = e

namespace AlgebraicSpace

/-- The scheme local-sections statement makes every represented smooth
surjection locally surjective for the full big etale topology. -/
theorem isLocallySurjective_smooth_schemeYoneda_map
    (h : SmoothSurjectiveEtaleLocalSectionsStatement.{u})
    {S : Scheme.{u}} {W T : Over S} (f : W ⟶ T)
    [Smooth f.left] [Surjective f.left] :
    CategoryTheory.Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S)
      ((schemeYoneda S).map f) := by
  obtain ⟨V, e, s, he, hs, hfac⟩ :=
    h W.left T.left f.left inferInstance inferInstance
  let V' : Over S := Over.mk (e ≫ T.hom)
  let e' : V' ⟶ T := Over.homMk e
  let s' : V' ⟶ W := Over.homMk s (by
    change s ≫ W.hom = e ≫ T.hom
    rw [← f.w, ← Category.assoc, hfac])
  have : Etale e'.left := he
  have : Surjective e'.left := hs
  have := isLocallySurjective_etale_schemeYoneda_map e'
  have hcomp : s' ≫ f = e' := Over.OverMorphism.ext hfac
  have hmap : (schemeYoneda S).map s' ≫ (schemeYoneda S).map f =
      (schemeYoneda S).map e' := by
    rw [← Functor.map_comp, hcomp]
  exact CategoryTheory.Presheaf.isLocallySurjective_of_isLocallySurjective_fac
    (Scheme.etaleTopology.over S) hmap

/-- Conditional on scheme local sections, a representable smooth and
geometrically surjective transformation is locally surjective on the full
big etale site, including every section of its target presheaf. -/
theorem isLocallySurjective_etale_of_isSmooth_isSurjective
    (h : SmoothSurjectiveEtaleLocalSectionsStatement.{u})
    {S : Scheme.{u}} {F G : Presheaf S} (a : F ⟶ G)
    (ha : IsSmooth a) (hs : IsSurjective a) :
    CategoryTheory.Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) a := by
  constructor
  intro T x
  let g : (schemeYoneda S).obj T ⟶ G := uliftYonedaEquiv.symm x
  let p := ha.representable.snd g
  have : Smooth p.left :=
    ha.projection g (ha.representable.fst g) p (ha.representable.isPullback g)
  have : Surjective p.left :=
    hs.projection g (ha.representable.fst g) p (ha.representable.isPullback g)
  have := isLocallySurjective_smooth_schemeYoneda_map h p
  apply (Scheme.etaleTopology.over S).superset_covering ?_
    (CategoryTheory.Presheaf.imageSieve_mem (Scheme.etaleTopology.over S)
      ((schemeYoneda S).map p) (⟨𝟙 T⟩ : ((schemeYoneda S).obj T).obj (op T)))
  intro V k hk
  obtain ⟨y, hy⟩ := hk
  refine ⟨(ha.representable.fst g).app (op V) y, ?_⟩
  have hy' : ((schemeYoneda S).map p).app (op V) y = ⟨k⟩ := by
    simpa using hy
  have hw := congrArg (fun z : (schemeYoneda S).obj (ha.representable.pullback g) ⟶ G =>
    z.app (op V) y) (ha.representable.isPullback g).w
  change a.app (op V) ((ha.representable.fst g).app (op V) y) =
    g.app (op V) (((schemeYoneda S).map p).app (op V) y) at hw
  rw [hy'] at hw
  simpa [g] using hw

end AlgebraicSpace

end Langlands.AlgebraicGeometry
