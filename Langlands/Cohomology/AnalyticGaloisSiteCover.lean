import Langlands.Cohomology.GaloisCovering
import Langlands.Geometry.Analytic.AnalyticGaloisCoverFreeness
import Langlands.Geometry.Analytic.EtaleOpenDomains.Proof
import Langlands.Geometry.Analytic.EtaleOpenMap.Proof
import Langlands.Geometry.Analytic.EtaleSite
import Langlands.Geometry.Analytic.LocalizedEtalePullbackProof
import Mathlib.Topology.Maps.Proper.Basic

/-! # Analytic Galois covers on the ordinary étale site -/

noncomputable section

universe u v z

namespace Langlands.Analytic.SaturatedAtlasPresentation

open _root_.CategoryTheory _root_.CategoryTheory.Limits Set Topology
open Langlands.Cohomology

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

/-- An arrow between two étale objects over the same base is étale. -/
theorem EtaleSite.etale_left {X : LocalizedCategory.{u, v, v} (K := K)}
    {A B : EtaleSite X} (f : A ⟶ B) : etale f.left := by
  obtain ⟨P, p, q, h, hq⟩ := localizedEtalePullbackBaseChange B.hom A.hom B.prop
  obtain ⟨P', q', p', h', hp'⟩ := localizedEtalePullbackBaseChange A.hom B.hom A.prop
  let e := h.isoIsPullback _ _ h'.flip
  have hp : etale p := by
    rw [← h.isoIsPullback_hom_fst _ _ h'.flip]
    exact MorphismProperty.RespectsIso.precomp etale e.hom p' hp'
  have hw : f.left ≫ B.hom = 𝟙 A.left ≫ A.hom :=
    (MorphismProperty.Over.w f).trans (Category.id_comp _).symm
  obtain ⟨O, hO, i, hi⟩ := localizedEtaleSectionsOpen hq (h.lift_snd _ _ hw)
  have hgraph : etale (h.lift f.left (𝟙 A.left) hw) :=
    hi ▸ etale_comp (etale_of_isIso i.hom) (etaleOpenDomainStatement P O hO)
  exact h.lift_fst _ _ hw ▸ etale_comp hgraph hp

namespace AnalyticGaloisCover

variable {Γ : Type z} [Group Γ]

/-- An analytic deck graph cover between étale objects defines a Galois covering
of the ordinary site. -/
def toEtaleSiteCover {X : LocalizedCategory.{u, v, v} (K := K)}
    {A B : EtaleSite X} (p : A ⟶ B) (c : AnalyticGaloisCover Γ p.left) :
    GaloisCovering (etaleTopology X) Γ A B := by
  let d (γ : Γ) : A ⟶ A := MorphismProperty.Over.homMk (c.deck γ).hom (by
    rw [← MorphismProperty.Over.w p, ← Category.assoc, c.deck_over])
  refine ⟨p, ?_, d, ?_, ?_, ?_, ?_, ?_⟩
  · apply mem_etaleTopology_of_jointlySurjective
    intro x
    exact ⟨A, p, ⟨A, 𝟙 A, p, ⟨()⟩, Category.id_comp _⟩, c.surjective x⟩
  · apply MorphismProperty.Over.Hom.ext
    change (c.deck 1).hom = 𝟙 _
    rw [map_one]
    rfl
  · intro γ δ
    apply MorphismProperty.Over.Hom.ext
    change (c.deck (γ * δ)).hom = (c.deck δ).hom ≫ (c.deck γ).hom
    rw [map_mul]
    rfl
  · intro γ
    exact MorphismProperty.Over.Hom.ext (c.deck_over γ)
  · intro U f g hfg
    apply mem_etaleTopology_of_jointlySurjective
    intro x
    have he : f.left ≫ p.left = g.left ≫ p.left :=
      congrArg (fun a : U ⟶ B => a.left) hfg
    obtain ⟨O, hO, hx, γ, heq⟩ := c.exists_open_deck_eq f.left g.left he x
    let j := domainι U.left ((presentationOf U.left).openDomain O hO)
    let W : EtaleSite X := MorphismProperty.Over.mk ⊤ (j ≫ U.hom)
      (etale_comp (etaleOpenDomainStatement U.left O hO) U.prop)
    let a : W ⟶ U := MorphismProperty.Over.homMk j rfl
    refine ⟨W, a, ⟨γ, ?_⟩, ⟨⟨x, hx⟩, rfl⟩⟩
    exact MorphismProperty.Over.Hom.ext heq
  · intro U f γ hf
    classical
    by_cases hU : Nonempty (localizedSpaceFunctor.obj U.left)
    · exact Or.inl (c.eq_one_of_comp_deck_eq f.left (Classical.choice hU)
        (congrArg (fun a : U ⟶ A => a.left) hf))
    · exact Or.inr (mem_etaleTopology_of_jointlySurjective _ fun x => (hU ⟨x⟩).elim)

variable {Y X : LocalizedCategory.{u, v, v} (K := K)} {p : Y ⟶ X}

/-- A finite analytic Galois covering is proper on underlying spaces. -/
theorem isProperMap [Finite Γ] (c : AnalyticGaloisCover Γ p) :
    IsProperMap (localizedSpaceFunctor.map p) := by
  let f := localizedSpaceFunctor.map p
  let act (γ : Γ) := localizedSpaceFunctor.map (c.deck γ).hom
  have hact (γ : Γ) (y : localizedSpaceFunctor.obj Y) : f (act γ y) = f y := by
    simpa only [f, act, Functor.map_comp, TopCat.comp_app] using
      congrArg (fun a : Y ⟶ X => localizedSpaceFunctor.map a y) (c.deck_over γ)
  have hq := (etaleOpenMap K p c.etale_map).isQuotientMap f.hom.continuous c.surjective
  refine isProperMap_iff_isClosedMap_and_compact_fibers.mpr ⟨f.hom.continuous, ?_, ?_⟩
  · intro s hs
    apply hq.isCoinducing.isClosed_preimage.mp
    have heq : f ⁻¹' (f '' s) = ⋃ γ, act γ ⁻¹' s := by
      ext y
      constructor
      · rintro ⟨z, hz, he⟩
        obtain ⟨γ, hγ⟩ := c.fibre_transitive y z he.symm
        refine mem_iUnion.mpr ⟨γ, ?_⟩
        change localizedSpaceFunctor.map (c.deck γ).hom y ∈ s
        rwa [hγ]
      · intro hy
        obtain ⟨γ, hγ⟩ := mem_iUnion.mp hy
        exact ⟨act γ y, hγ, hact γ y⟩
    rw [heq]
    exact isClosed_iUnion_of_finite fun γ => hs.preimage (act γ).hom.continuous
  · intro x
    obtain ⟨y, hy⟩ := c.surjective x
    apply Set.Finite.isCompact
    refine (Set.finite_range fun γ => act γ y).subset fun z hz => ?_
    obtain ⟨γ, hγ⟩ := c.fibre_transitive y z (hy.trans (Set.mem_singleton_iff.mp hz).symm)
    exact ⟨γ, hγ⟩

end AnalyticGaloisCover
end Langlands.Analytic.SaturatedAtlasPresentation
