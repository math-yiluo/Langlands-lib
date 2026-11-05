import Langlands.Geometry.Analytic.SaturatedDomainQuotientSeparation
import Langlands.Geometry.Analytic.OriginalDomainRefinement

/-! # Separation of arbitrary source-quotient arrows over domain covers -/

noncomputable section

universe u v w z

namespace Langlands.Analytic.SaturatedAtlasPresentation

open CategoryTheory Set
open AffinoidAtlasPresentation

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A B : SaturatedAtlasPresentation.{u, v, w} K}

/-- Precomposition by the actual domain inclusion retains the complete
bounded pullback of the literal source-subspace restriction. -/
theorem originalDomainInclusion_comp_eq_restrictSubspace
    (S : A.presentation.atlas.OriginalChartDomain) (f : A ⟶ B) :
    A.originalDomainInclusion S ≫ f =
      f.restrictSubspace S.carrier S.is_domain := by
  refine StrongHom.ext_of_saturated
    (A.originalDomain S).hasAllLocalDomains rfl ?_
  intro i
  obtain ⟨j, hj⟩ := f.target_exists i.val
  have hi : (A.originalDomainInclusion S).baseMap ''
      Set.range ((A.originalDomain S).presentation.atlas.chart i) ⊆
        Set.range (A.presentation.atlas.chart i.val) := by
    rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
    exact ⟨x, rfl⟩
  have hcomp := (A.originalDomainInclusion S).comp_admissible f i i.val j hi hj
  refine ⟨j, hcomp, ?_⟩
  refine (StrongHom.saturatedComp_pullback (A.originalDomainInclusion S) f
    (A.originalDomain S).hasAllLocalDomains A.hasAllLocalDomains
    i i.val j hi hj hcomp).trans ?_
  change (A.presentation.atlas.restriction i.val i.val _).comp
    (f.pullback i.val j hj) = f.pullback i.val j _
  rw [A.presentation.atlas.restriction_id, BoundedAlgHom.id_comp]

namespace SourceCategory

/-- The canonical denominator cancels its represented fraction in the
constructed source quotient. -/
theorem strongFunctor_map_inclusion_comp_ι
    (P : A.presentation.atlas.RefiningSelection)
    (f : A.refiningSubpresentation P ⟶ B) :
    strongFunctor.map (A.refiningSubatlasInclusion P) ≫
        (sourceHomι P f : ofPresentation A ⟶ ofPresentation B) =
      strongFunctor.map f := by
  apply sourceHomEquiv.injective
  change sourceHomEquiv (sourceHomComp
      (strongFunctor.map (A.refiningSubatlasInclusion P)) (sourceHomι P f)) =
    sourceHomEquiv (strongFunctor.map f)
  erw [sourceHomEquiv_comp, sourceHomEquiv_ι]
  change sourceHomEquiv (sourceHomEquiv.symm
      (localizationFunctor.map (A.refiningSubatlasInclusion P))) ≫
      localizedRightFraction (sourceRefinementFraction P f) =
    sourceHomEquiv (sourceHomEquiv.symm (localizationFunctor.map f))
  rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  exact localizationFunctor_map_s_comp_localizedRightFraction (sourceRefinementFraction P f)

/-- A smaller common selection restricts the entire represented numerator. -/
theorem strongFunctor_map_inclusion_comp_ι_of_le
    {P Q : A.presentation.atlas.RefiningSelection} (h : P ≤ Q)
    (f : A.refiningSubpresentation Q ⟶ B) :
    strongFunctor.map (A.refiningSubatlasInclusion P) ≫
        (sourceHomι Q f : ofPresentation A ⟶ ofPresentation B) =
      strongFunctor.map (refiningHomRestriction h f) := by
  erw [← refiningSubatlasMap_inclusion h, Functor.map_comp, Category.assoc,
    strongFunctor_map_inclusion_comp_ι, ← Functor.map_comp]
  rfl

/-- Two arbitrary quotient arrows have actual full numerators on the same
constructed intersection of refining source selections. -/
theorem exists_commonSourceNumerators
    (F G : ofPresentation A ⟶ ofPresentation B) :
    ∃ (P : A.presentation.atlas.RefiningSelection)
      (f g : A.refiningSubpresentation P ⟶ B),
      strongFunctor.map (A.refiningSubatlasInclusion P) ≫ F = strongFunctor.map f ∧
      strongFunctor.map (A.refiningSubatlasInclusion P) ≫ G = strongFunctor.map g := by
  change SourceHomQuotient A B at F G
  refine Quotient.inductionOn₂ F G ?_
  rintro ⟨P, f⟩ ⟨Q, g⟩
  refine ⟨P ⊓ Q, refiningHomRestriction inf_le_left f,
    refiningHomRestriction inf_le_right g, ?_, ?_⟩
  · exact strongFunctor_map_inclusion_comp_ι_of_le inf_le_left f
  · exact strongFunctor_map_inclusion_comp_ι_of_le inf_le_right g

variable {ι : Type z} (D : ι → A.presentation.atlas.OriginalChartDomain)

/-- Restrict an actual quotient arrow along every actual domain inclusion. -/
def domainCoverRestriction :
    (ofPresentation A ⟶ ofPresentation B) →
      ∀ k, (ofPresentation (A.originalDomain (D k)) ⟶ ofPresentation B) :=
  fun F k => domainInclusion A (D k) ≫ F

/-- The same actual domain subsets in a refining source presentation. -/
def selectedSourceCover (P : A.presentation.atlas.RefiningSelection) :
    ι → (A.refiningSubpresentation P).presentation.atlas.OriginalChartDomain :=
  fun k => A.presentation.atlas.originalDomainSubatlasOrderIso
    P.carrier P.locally_refining (D k)

/-- Image-only domain factorization transfers local equality to any common
selected source without assuming faithfulness of the original functor. -/
theorem locallyEqual_commonSourceNumerators
    (F G : ofPresentation A ⟶ ofPresentation B)
    (P : A.presentation.atlas.RefiningSelection)
    (f g : A.refiningSubpresentation P ⟶ B)
    (hf : strongFunctor.map (A.refiningSubatlasInclusion P) ≫ F = strongFunctor.map f)
    (hg : strongFunctor.map (A.refiningSubatlasInclusion P) ≫ G = strongFunctor.map g)
    (h : ∀ k, domainInclusion A (D k) ≫ F = domainInclusion A (D k) ≫ G) :
    StrongLocallyEqualOnDomains f g (selectedSourceCover D P) := by
  intro k
  let E := selectedSourceCover D P k
  let q := domainInclusion (A.refiningSubpresentation P) E ≫
    strongFunctor.map (A.refiningSubatlasInclusion P)
  have hq : ∀ x, spaceFunctor.map q x ∈ D k := by
    intro x
    dsimp only [q]
    erw [Functor.map_comp]
    change spaceFunctor.map (strongFunctor.map (A.refiningSubatlasInclusion P))
      (spaceFunctor.map (domainInclusion (A.refiningSubpresentation P) E) x) ∈ D k
    erw [spaceFunctor_map_strong, domainInclusion_apply]
    exact x.property
  let t := domainLift (D k) q hq
  have ht : t ≫ domainInclusion A (D k) = q :=
    domainLift_comp_inclusion (D k) q hq
  have heq := congrArg
    (fun r : ofPresentation (A.originalDomain (D k)) ⟶ ofPresentation B => t ≫ r) (h k)
  rw [← Category.assoc, ← Category.assoc] at heq
  simp only [ht, q] at heq
  erw [Category.assoc, Category.assoc, hf, hg] at heq
  have hm : strongFunctor.map
      ((A.refiningSubpresentation P).originalDomainInclusion E ≫ f) =
      strongFunctor.map
        ((A.refiningSubpresentation P).originalDomainInclusion E ≫ g) := by
    rw [Functor.map_comp, Functor.map_comp]
    exact heq
  erw [originalDomainInclusion_comp_eq_restrictSubspace,
    originalDomainInclusion_comp_eq_restrictSubspace] at hm
  exact hm

/-- Equality after restriction to an actual original-domain quasinet cover
detects equality of every arrow in the constructed source quotient category. -/
theorem eq_of_domainCover
    (hD : AtlasTopology.LocallyRefines
      (Set.range (fun k => (D k).carrier)) {Set.univ})
    (F G : ofPresentation A ⟶ ofPresentation B)
    (h : ∀ k, domainInclusion A (D k) ≫ F = domainInclusion A (D k) ≫ G) : F = G := by
  obtain ⟨P, f, g, hf, hg⟩ := exists_commonSourceNumerators F G
  have hlocal := locallyEqual_commonSourceNumerators D F G P f g hf hg h
  have hcover : AtlasTopology.LocallyRefines
      (Set.range (fun k => (selectedSourceCover D P k).carrier)) {Set.univ} := hD
  have heq := strongFunctor_map_eq_of_domainCover f g (selectedSourceCover D P) hcover hlocal
  have : IsIso (strongFunctor.map (A.refiningSubatlasInclusion P)) :=
    Localization.inverts strongFunctor (quasiIsomorphisms (K := K))
      (A.refiningSubatlasInclusion P) (isQuasiIso_refiningSubatlasInclusion P)
  apply (cancel_epi (strongFunctor.map (A.refiningSubatlasInclusion P))).1
  exact hf.trans (heq.trans hg.symm)

/-- The full quotient-valued domain restriction map is injective for every
original-domain quasinet covering family, with independent cover universe. -/
theorem domainCoverRestriction_injective
    (hD : AtlasTopology.LocallyRefines
      (Set.range (fun k => (D k).carrier)) {Set.univ}) :
    Function.Injective (domainCoverRestriction (B := B) D) := by
  intro F G h
  exact eq_of_domainCover D hD F G (fun k => congrFun h k)

end SourceCategory
end Langlands.Analytic.SaturatedAtlasPresentation
