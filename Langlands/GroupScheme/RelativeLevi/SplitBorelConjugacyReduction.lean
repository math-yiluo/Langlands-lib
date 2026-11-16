import Langlands.GroupScheme.RelativeLevi.SplitBorelVectorSeriesStatement
import Langlands.GroupScheme.RelativeLevi.SplitBorelContainmentReduction
import Langlands.GroupScheme.RelativeLevi.BorelNormalizerLocalConjugacy

/-! # Split Borel local conjugacy from structure and normalizer lifting -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

open SubgroupFunctor

section Containment

variable {R : Type u} [CommRing R]
  {G B : GroupScheme (Spec (CommRingCat.of R))}
  {I : Type u} [Fintype I]
  {t : splitTorus (Spec (CommRingCat.of R)) I ⟶ G}

/-- The supplied split Borel structure implies local containment for any Borel. -/
theorem HasSplitBorelVectorSeries.hasZariskiLocalConjugateContaining
    (h : HasSplitBorelVectorSeries t) (hG : IsReductive G)
    (i : B ⟶ G) (hi : IsRelativeBorelSubgroup i) :
    HasZariskiLocalConjugateContaining t i := by
  obtain ⟨B₀, K, i₀, j, q, t₀, hi₀, hj, hK, ht, _, hq, n, hseries⟩ := h
  let : IsClosedImmersion j.hom.hom.left := hj
  let : Mono j.hom.hom := Over.mono_of_mono_left _
  let : IsAffineHom K.X.hom := hK
  obtain ⟨hflat, hsurj, hlfp, hker⟩ := hq
  let : Flat q.hom.hom.left := hflat
  let : Surjective q.hom.hom.left := hsurj
  let : LocallyOfFinitePresentation q.hom.hom.left := hlfp
  have hti : range t ≤ range i₀ := by
    intro U x hx
    rw [← ht] at hx
    obtain ⟨y, rfl⟩ := mem_range.mp hx
    exact mem_range.mpr ⟨y ≫ t₀.hom.hom, Category.assoc _ _ _⟩
  exact SplitBorelContainmentReduction.hasZariskiLocalConjugateContaining_of_vectorSeries
    t i₀ i hG hi₀ hi hti j q hker hseries (isSplitTorus_splitTorus I)

/-- Choose an open and an actual local conjugator containing the specified torus
from the supplied split Borel structure. -/
def splitBorelLocalConjugatorOfVectorSeries
    (h : HasSplitBorelVectorSeries t) (hG : IsReductive G)
    (i : B ⟶ G) (hi : IsRelativeBorelSubgroup i) (s : Spec (CommRingCat.of R)) :
    Σ V : (Spec (CommRingCat.of R)).Opens,
      {g : Over.mk (𝟙 V.toScheme) ⟶ ((GroupScheme.baseChange V.ι).obj G).X //
        s ∈ V ∧
        range ((GroupScheme.baseChange V.ι).map t) ≤
          range ((GroupScheme.baseChange V.ι).map i ≫
            (((GroupScheme.baseChange V.ι).obj G).innerIso g).hom)} :=
  let hs := h.hasZariskiLocalConjugateContaining hG i hi s
  ⟨hs.choose, hs.choose_spec.2.choose, hs.choose_spec.1, hs.choose_spec.2.choose_spec⟩

end Containment

/-- The two explicit structural inputs imply the unchanged full split Borel
Zariski-local conjugacy statement, uniformly in every universe. -/
theorem splitBorelZariskiLocalConjugacy_of_structure_and_lifting
    (hStructure : SplitBorelVectorSeriesStatement.{u})
    (hLift : SplitNormalizerGeometricLocalLiftingStatement.{u}) :
    SplitBorelZariskiLocalConjugacyStatement.{u} := by
  intro R _ G hG I _ t J P ht hmax hroot hfree
  constructor
  · intro B i hi
    exact (hStructure R G hG I t J P ht hmax hroot hfree).hasZariskiLocalConjugateContaining
      hG i hi
  · exact splitBorel_exists_open_normalizer_conjugacy_of_lifting
      hLift R G hG I t J P ht hmax hroot hfree

end Langlands.GroupScheme
