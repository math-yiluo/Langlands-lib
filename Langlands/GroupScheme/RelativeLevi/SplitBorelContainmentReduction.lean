import Langlands.GroupScheme.AffineConjugatingCover
import Langlands.GroupScheme.RelativeParabolicNormalizerProof
import Langlands.GroupScheme.RelativeLevi.ParabolicClosedProof
import Langlands.GroupScheme.RelativeLevi.ParabolicBaseChange
import Langlands.GroupScheme.Torus.SplitReductiveProof

/-! # Local Borel containment from a supplied split-solvable Borel -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {S : Scheme.{u}} {G B B₀ T : GroupScheme S}

/-- Every base point has an open neighbourhood on which a rational conjugate
of the given subgroup contains the represented subgroup `t`. -/
def HasZariskiLocalConjugateContaining (t : T ⟶ G) (i : B ⟶ G) : Prop :=
  ∀ s : S, ∃ V : S.Opens, s ∈ V ∧
    ∃ g : Over.mk (𝟙 V.toScheme) ⟶ ((GroupScheme.baseChange V.ι).obj G).X,
      SubgroupFunctor.range ((GroupScheme.baseChange V.ι).map t) ≤
        SubgroupFunctor.range ((GroupScheme.baseChange V.ι).map i ≫
          (((GroupScheme.baseChange V.ι).obj G).innerIso g).hom)

namespace SplitBorelContainmentReduction

open SubgroupFunctor

/-- Reverse local conjugacy from a subgroup containing `t` to obtain the
required local conjugate containing `t`. -/
theorem hasZariskiLocalConjugateContaining_of_localConjugacy
    (t : T ⟶ G) (i₀ : B₀ ⟶ G) (i : B ⟶ G)
    (ht : range t ≤ range i₀) (hc : HasZariskiLocalSubgroupConjugacy i₀ i) :
    HasZariskiLocalConjugateContaining t i := by
  intro s
  obtain ⟨V, hs, g, hg⟩ := hc s
  refine ⟨V, hs, g⁻¹, ?_⟩
  have hg' : IsConjugatingPoint
      (range ((GroupScheme.baseChange V.ι).map i₀))
      (range ((GroupScheme.baseChange V.ι).map i)) g :=
    (isConjugatingPoint_iff_range_innerIso _ _ _).mpr hg
  rw [(isConjugatingPoint_iff_range_innerIso _ _ _).mp hg'.inv]
  simpa only [range_baseChangeHom] using baseChange_mono V.ι ht

variable {R : Type u} [CommRing R]
  {G B B₀ K Q T : GroupScheme (Spec (CommRingCat.of R))}

/-- The affine etale conjugating cover and self-normalization remove the
cover and normalizer premises from vector-series local conjugacy for Borels. -/
theorem hasZariskiLocalSubgroupConjugacy_of_vectorSeries
    (i₀ : B₀ ⟶ G) (i : B ⟶ G) (hG : IsReductive G)
    (hi₀ : IsRelativeBorelSubgroup i₀) (hi : IsRelativeBorelSubgroup i)
    (j : K ⟶ B₀) (q : B₀ ⟶ Q) [Mono j.hom.hom]
    (hjq : range (kernelι q) = range j)
    [IsAffineHom K.X.hom]
    [Flat q.hom.hom.left] [Surjective q.hom.hom.left]
    [LocallyOfFinitePresentation q.hom.hom.left]
    {n : ℕ} (hK : HasAffineVectorSeries n K) (hQ : IsSplitTorus Q) :
    HasZariskiLocalSubgroupConjugacy i₀ i := by
  let : Mono i₀.hom.hom := hi₀.isRelativeParabolicSubgroup.mono
  let : Mono i.hom.hom := hi.isRelativeParabolicSubgroup.mono
  let : IsAffineHom B₀.X.hom := hi₀.isRelativeParabolicSubgroup.isAffineHom
  let : IsAffineHom Q.X.hom := hQ.isAffineHom
  let : IsAffine B₀.X.left := isAffine_of_isAffineHom B₀.X.hom
  let : IsAffine Q.X.left := isAffine_of_isAffineHom Q.X.hom
  have hself : (range i₀).normalizer = range i₀ :=
    relativeParabolicSelfNormalizer R G B₀ i₀ hG
      hi₀.isRelativeParabolicSubgroup.smooth
      (relativeParabolicClosed _ _ _ _ hG hi₀.isRelativeParabolicSubgroup)
      (fun k _ _ => hi₀.isRelativeParabolicSubgroup.isParabolicSubgroup_baseChange hG
        (Spec.algebraMap R k))
  obtain ⟨U, hU, he, hs, g, hg⟩ :=
    AffineConjugatingCover.hasAffineEtaleConjugatingCover_of_borels i₀ i hG hi₀ hi
  let : IsAffine U.left := hU
  let : Etale U.hom := he
  let : Surjective U.hom := hs
  exact LocalSubgroupConjugacy.hasZariskiLocalSubgroupConjugacy_of_vectorSeries
    i₀ i j q hjq hK hQ hself U g hg

/-- A supplied Borel containing `t`, with a split-torus quotient and a finite
vector-series kernel, gives the first local-containment conclusion for every
relative Borel of the reductive group over an arbitrary ring. -/
theorem hasZariskiLocalConjugateContaining_of_vectorSeries
    (t : T ⟶ G) (i₀ : B₀ ⟶ G) (i : B ⟶ G) (hG : IsReductive G)
    (hi₀ : IsRelativeBorelSubgroup i₀) (hi : IsRelativeBorelSubgroup i)
    (ht : range t ≤ range i₀)
    (j : K ⟶ B₀) (q : B₀ ⟶ Q) [Mono j.hom.hom]
    (hjq : range (kernelι q) = range j)
    [IsAffineHom K.X.hom]
    [Flat q.hom.hom.left] [Surjective q.hom.hom.left]
    [LocallyOfFinitePresentation q.hom.hom.left]
    {n : ℕ} (hK : HasAffineVectorSeries n K) (hQ : IsSplitTorus Q) :
    HasZariskiLocalConjugateContaining t i :=
  hasZariskiLocalConjugateContaining_of_localConjugacy t i₀ i ht
    (hasZariskiLocalSubgroupConjugacy_of_vectorSeries i₀ i hG hi₀ hi j q hjq hK hQ)

end SplitBorelContainmentReduction

end Langlands.GroupScheme
