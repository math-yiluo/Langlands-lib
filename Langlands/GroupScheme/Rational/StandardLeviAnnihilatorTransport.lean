import Langlands.GroupScheme.Rational.StandardLeviRootTransport
import Langlands.GroupScheme.Rational.StandardLeviAnnihilator

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct
open scoped CategoryTheory.MonObj
open Langlands.LinearAlgebra.RationalSpan

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}

/-- The integer submodule of cocharacters annihilating a set of characters. -/
def cocharacterAnnihilator (T : CommGroupScheme (Spec (CommRingCat.of k)))
    (J : Set (characterLattice T)) : Submodule ℤ (cocharacterLattice T) :=
  ⨅ α ∈ J, (latticePairing T α).ker

@[simp] theorem mem_cocharacterAnnihilator {J : Set (characterLattice T)}
    {zeta : cocharacterLattice T} :
    zeta ∈ cocharacterAnnihilator T J ↔
      ∀ α ∈ J, latticePairing T α zeta = 0 := by
  simp only [cocharacterAnnihilator, Submodule.mem_iInf, LinearMap.mem_ker]

/-- The cocharacter automorphism carries the annihilator onto that of the transported set. -/
theorem cocharacterAut_mem_annihilator_iff (σ : T ≅ T)
    {J J' : Set (characterLattice T)} (h : characterAut σ '' J' = J)
    (zeta : cocharacterLattice T) :
    cocharacterAut σ zeta ∈ cocharacterAnnihilator T J ↔
      zeta ∈ cocharacterAnnihilator T J' := by
  simpa only [mem_cocharacterAnnihilator] using annihilates_image_iff σ h zeta

/-- The annihilator-centralizer intersection conjugates under actual normalizer transport
of the character sets. This is equality on every test scheme. -/
theorem cocharacterAnnihilatorCentralizer_eq_comap
    (i : T.toGrp ⟶ G) [Mono i.hom.hom.left] {J J' : Set (characterLattice T)}
    (n : normalizerPoints i) (h : weylAction i n '' J' = J) :
    cocharacterAnnihilatorCentralizer i J' =
      (cocharacterAnnihilatorCentralizer i J).comap
        (G.innerIso (n : Over.mk (𝟙 _) ⟶ G.X)).hom := by
  let σ := normalizingAut i n
  have hσ : characterAut σ '' J' = J := h
  have hconj (zeta : cocharacterLattice T) :
      Dynamic.centralizer (CommGroupScheme.groupHom zeta ≫ i) =
        (Dynamic.centralizer (CommGroupScheme.groupHom (cocharacterAut σ zeta) ≫ i)).comap
          (G.innerIso (n : Over.mk (𝟙 _) ⟶ G.X)).hom := by
    rw [groupHom_cocharacterAut_comp]
    exact Dynamic.centralizer_eq_comap_of_iso _ _
  apply SubgroupFunctor.ext
  intro U
  apply Subgroup.ext
  intro g
  rw [SubgroupFunctor.mem_comap, mem_cocharacterAnnihilatorCentralizer,
    mem_cocharacterAnnihilatorCentralizer]
  constructor
  · intro hg zeta hzeta
    obtain ⟨xi, rfl⟩ := (cocharacterAut σ).surjective zeta
    have hxi := (annihilates_image_iff σ hσ xi).mp hzeta
    have hgxi := hg xi hxi
    rwa [hconj, SubgroupFunctor.mem_comap] at hgxi
  · intro hg zeta hzeta
    have hxi := (annihilates_image_iff σ hσ zeta).mpr hzeta
    have hgxi := hg (cocharacterAut σ zeta) hxi
    rwa [hconj, SubgroupFunctor.mem_comap]

/-- Finite simple roots and standard-cocharacter existence suffice for the actual
character-set form of standard-Levi conjugation. -/
theorem standardLevi_eq_comap_of_finite_of_exists
    [IsAffineHom G.X.hom] (i : T.toGrp ⟶ G) [Mono i.hom.hom.left]
    (ν : cocharacterLattice T) (hfinite : (simpleRelativeRoots i ν).Finite)
    {J J' : Set (characterLattice T)}
    (hJ : ∃ zeta, IsStandardCocharacter i ν J zeta)
    (hJ' : ∃ zeta, IsStandardCocharacter i ν J' zeta)
    (n : normalizerPoints i) (h : weylAction i n '' J' = J) :
    standardLevi i ν J' =
      (standardLevi i ν J).comap (G.innerIso (n : Over.mk (𝟙 _) ⟶ G.X)).hom := by
  rw [standardLevi_eq_cocharacterAnnihilatorCentralizer i ν hfinite J hJ,
    standardLevi_eq_cocharacterAnnihilatorCentralizer i ν hfinite J' hJ']
  exact cocharacterAnnihilatorCentralizer_eq_comap i n h

/-- The target's exact encoded-root-set condition gives standard-Levi conjugation
under the displayed structural finiteness and existence hypotheses. -/
theorem standardLevi_eq_comap_of_rootSubset_image
    [IsAffineHom G.X.hom] (i : T.toGrp ⟶ G) [Mono i.hom.hom.left]
    (hT : IsSplitTorus T.toGrp) (ν : cocharacterLattice T)
    (hfinite : (simpleRelativeRoots i ν).Finite)
    {J J' : Set (characterLattice T)}
    (hJ : ∃ zeta, IsStandardCocharacter i ν J zeta)
    (hJ' : ∃ zeta, IsStandardCocharacter i ν J' zeta)
    (n : normalizerPoints i)
    (h : relativeWeylAction i (QuotientGroup.mk n) ''
        {x : relativeRootSpan i |
          (x : ℚ ⊗[ℤ] characterLattice T) ∈ toRat '' J'} =
      {x : relativeRootSpan i |
        (x : ℚ ⊗[ℤ] characterLattice T) ∈ toRat '' J}) :
    standardLevi i ν J' =
      (standardLevi i ν J).comap (G.innerIso (n : Over.mk (𝟙 _) ⟶ G.X)).hom := by
  have hroots : simpleRelativeRoots i ν ⊆ relativeRoots i :=
    (simpleRelativeRoots_subset_positive i ν).trans
      (positiveRelativeRoots_subset_relativeRoots i ν)
  have hJroots : J ⊆ relativeRoots i := hJ.choose_spec.subset.trans hroots
  have hJ'roots : J' ⊆ relativeRoots i := hJ'.choose_spec.subset.trans hroots
  exact standardLevi_eq_comap_of_finite_of_exists i ν hfinite hJ hJ' n
    (weylAction_image_eq_of_relativeWeylAction_image_eq i hT hJroots hJ'roots n h)

end Langlands.GroupScheme
