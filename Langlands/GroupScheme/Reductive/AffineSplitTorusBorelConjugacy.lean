import Langlands.GroupScheme.RelativeLevi.PicardSplitTorusConjugacy
import Langlands.GroupScheme.RelativeLevi.PicardSplitBorelConjugacy
import Langlands.GroupScheme.RelativeLevi.SplitBorelVectorSeriesStatement
import Langlands.GroupScheme.Torus.FibrewiseMaximalTransport
import Langlands.GroupScheme.InnerAutomorphismHom
import Langlands.GroupScheme.ConjugacyBaseChange
import Langlands.GroupScheme.Rational.ParabolicAmbientTransport

/-! # Simultaneous affine conjugacy from a split Borel vector series -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

open SubgroupFunctor Langlands.AlgebraicGeometry.Picard

namespace RelativeLevi

/-- Correct a supplied global Borel conjugator inside its target Borel to
carry the supplied split maximal tori simultaneously. -/
theorem exists_simultaneousConjugatingPoint_of_borelConjugator
    {S : Scheme.{u}} [IsAffine S] {G B B' : GroupScheme S}
    (hG : IsReductive G)
    (hPic : ∀ L : LineBundle S, Nonempty (L ≅ LineBundle.trivial S))
    {I I' : Type u} [Finite I] [Finite I']
    (t : splitTorus S I ⟶ G) (t' : splitTorus S I' ⟶ G)
    (ht : IsClosedSubgroup t)
    (hmax : IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme S I) t)
    (ht' : IsClosedSubgroup t')
    (hmax' : IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme S I') t')
    (i : B ⟶ G) (i' : B' ⟶ G)
    (_hi : IsRelativeBorelSubgroup i) (hi' : IsRelativeBorelSubgroup i')
    (hti : range t ≤ range i) (hti' : range t' ≤ range i')
    (g₀ : Over.mk (𝟙 S) ⟶ G.X)
    (hg₀ : range (i ≫ (G.innerIso g₀).hom) = range i') :
    ∃ g : Over.mk (𝟙 S) ⟶ G.X,
      range (t ≫ (G.innerIso g).hom) = range t' ∧
      range (i ≫ (G.innerIso g).hom) = range i' := by
  let : Mono t'.hom.hom := ht'.mono_overHom
  let : Mono i'.hom.hom := hi'.1.mono
  let : Mono (t ≫ (G.innerIso g₀).hom).hom.hom :=
    (ht.comp_iso (G.innerIso g₀)).mono_overHom
  have hle : range (t ≫ (G.innerIso g₀).hom) ≤ range i' := by
    rw [← hg₀]
    exact range_comp_mono hti _
  let a := factorOfRangeLE hle
  let a' := factorOfRangeLE hti'
  have ha : a ≫ i' = t ≫ (G.innerIso g₀).hom := factorOfRangeLE_comp hle
  have ha' : a' ≫ i' = t' := factorOfRangeLE_comp hti'
  have hac : IsClosedSubgroup (a ≫ i') := by
    rw [ha]
    exact ht.comp_iso (G.innerIso g₀)
  have ham : IsFibrewiseMaximalTorus
      (T := splitTorus.commGroupScheme S I) (a ≫ i') := by
    rw [ha]
    exact hmax.comp_iso (G.innerIso g₀)
  have hac' : IsClosedSubgroup (a' ≫ i') := by rwa [ha']
  have ham' : IsFibrewiseMaximalTorus
      (T := splitTorus.commGroupScheme S I') (a' ≫ i') := by rwa [ha']
  obtain ⟨b, hb⟩ := exists_commonBorelSplitTorusConjugatingPoint
    i' hG hi' a a' hac ham hac' ham' hPic
  let c := b ≫ i'.hom.hom
  have hbc : range ((a ≫ (B'.innerIso b).hom) ≫ i') = range (a' ≫ i') :=
    le_antisymm (range_comp_mono hb.le i') (range_comp_mono hb.ge i')
  have htor : range ((t ≫ (G.innerIso g₀).hom) ≫ (G.innerIso c).hom) = range t' := by
    calc
      _ = range ((a ≫ (B'.innerIso b).hom) ≫ i') := by
        rw [Category.assoc a (B'.innerIso b).hom i', innerIso_hom_comp i' b,
          ← Category.assoc a i' (G.innerIso c).hom, ha]
      _ = range (a' ≫ i') := hbc
      _ = range t' := by rw [ha']
  have hnorm : range (i' ≫ (G.innerIso c).hom) = range i' := by
    rw [← innerIso_hom_comp i' b]
    exact range_iso_comp (B'.innerIso b) i'
  refine ⟨c * g₀, ?_, ?_⟩
  · simpa only [innerIso_mul_hom, ← Category.assoc] using htor
  · rw [innerIso_mul_hom, ← Category.assoc]
    exact (le_antisymm (range_comp_mono hg₀.le _) (range_comp_mono hg₀.ge _)).trans hnorm

end RelativeLevi

namespace HasSplitBorelVectorSeries

variable {R : Type u} [CommRing R]
    {G : GroupScheme (Spec (CommRingCat.of R))}
    {I : Type u} [Fintype I]
    {t : splitTorus (Spec (CommRingCat.of R)) I ⟶ G}
    (h : HasSplitBorelVectorSeries t) (hG : IsReductive G)
    (hPic : ∀ L : LineBundle (Spec (CommRingCat.of R)),
      Nonempty (L ≅ LineBundle.trivial (Spec (CommRingCat.of R))))

include h hG hPic in
/-- A supplied standard split Borel vector series makes all relative Borels
globally conjugate over the Picard-trivial ring spectrum. -/
theorem exists_borelConjugatingPoint (B B' : GroupScheme (Spec (CommRingCat.of R)))
    (i : B ⟶ G) (i' : B' ⟶ G)
    (hi : IsRelativeBorelSubgroup i) (hi' : IsRelativeBorelSubgroup i') :
    ∃ g : Over.mk (𝟙 (Spec (CommRingCat.of R))) ⟶ G.X,
      range (i ≫ (G.innerIso g).hom) = range i' := by
  obtain ⟨B₀, K, i₀, j, q, t₀, hi₀, hj, hKaff, _, hsec, hq, n, hK⟩ := h
  let : Mono j.hom.hom := hj.mono_overHom
  let : IsAffineHom K.X.hom := hKaff
  have hσ : t₀.hom.hom ≫ q.hom.hom = 𝟙 _ :=
    congrArg (fun f => f.hom.hom) hsec
  obtain ⟨g, hg⟩ := RelativeLevi.exists_globalSplitVectorBorelConjugatingPoint
    i₀ i hG hi₀ hi j q hq.2.2.2 t₀.hom.hom hσ hK hPic
  obtain ⟨g', hg'⟩ := RelativeLevi.exists_globalSplitVectorBorelConjugatingPoint
    i₀ i' hG hi₀ hi' j q hq.2.2.2 t₀.hom.hom hσ hK hPic
  have hc := ((isConjugatingPoint_iff_range_innerIso i₀ i g).mpr hg).inv.trans
    ((isConjugatingPoint_iff_range_innerIso i₀ i' g').mpr hg')
  exact ⟨g' * g⁻¹, (isConjugatingPoint_iff_range_innerIso i i' _).mp hc⟩

include h hG hPic in
/-- The vector-series structure supplies a global conjugator carrying both
a split maximal torus and its supplied containing Borel. -/
theorem exists_simultaneousConjugatingPoint
    {I' : Type u} [Finite I']
    (t' : splitTorus (Spec (CommRingCat.of R)) I' ⟶ G)
    (ht : IsClosedSubgroup t)
    (hmax : IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I) t)
    (ht' : IsClosedSubgroup t')
    (hmax' : IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I') t')
    (B B' : GroupScheme (Spec (CommRingCat.of R))) (i : B ⟶ G) (i' : B' ⟶ G)
    (hi : IsRelativeBorelSubgroup i) (hi' : IsRelativeBorelSubgroup i')
    (hti : range t ≤ range i) (hti' : range t' ≤ range i') :
    ∃ g : Over.mk (𝟙 (Spec (CommRingCat.of R))) ⟶ G.X,
      range (t ≫ (G.innerIso g).hom) = range t' ∧
      range (i ≫ (G.innerIso g).hom) = range i' := by
  obtain ⟨g, hg⟩ := h.exists_borelConjugatingPoint hG hPic B B' i i' hi hi'
  exact RelativeLevi.exists_simultaneousConjugatingPoint_of_borelConjugator
    hG hPic t t' ht hmax ht' hmax' i i' hi hi' hti hti' g hg

/-- Choose a simultaneous global torus and Borel conjugating section. -/
def simultaneousConjugatingPoint
    {I' : Type u} [Finite I']
    (t' : splitTorus (Spec (CommRingCat.of R)) I' ⟶ G)
    (ht : IsClosedSubgroup t)
    (hmax : IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I) t)
    (ht' : IsClosedSubgroup t')
    (hmax' : IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I') t')
    (B B' : GroupScheme (Spec (CommRingCat.of R))) (i : B ⟶ G) (i' : B' ⟶ G)
    (hi : IsRelativeBorelSubgroup i) (hi' : IsRelativeBorelSubgroup i')
    (hti : range t ≤ range i) (hti' : range t' ≤ range i') :
    Over.mk (𝟙 (Spec (CommRingCat.of R))) ⟶ G.X :=
  Classical.choose (h.exists_simultaneousConjugatingPoint
    hG hPic t' ht hmax ht' hmax' B B' i i' hi hi' hti hti')

/-- The chosen point has both actual represented-range equalities. -/
theorem simultaneousConjugatingPoint_spec
    {I' : Type u} [Finite I']
    (t' : splitTorus (Spec (CommRingCat.of R)) I' ⟶ G)
    (ht : IsClosedSubgroup t)
    (hmax : IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I) t)
    (ht' : IsClosedSubgroup t')
    (hmax' : IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I') t')
    (B B' : GroupScheme (Spec (CommRingCat.of R))) (i : B ⟶ G) (i' : B' ⟶ G)
    (hi : IsRelativeBorelSubgroup i) (hi' : IsRelativeBorelSubgroup i')
    (hti : range t ≤ range i) (hti' : range t' ≤ range i') :
    let g := h.simultaneousConjugatingPoint hG hPic t' ht hmax ht' hmax'
      B B' i i' hi hi' hti hti'
    range (t ≫ (G.innerIso g).hom) = range t' ∧
      range (i ≫ (G.innerIso g).hom) = range i' :=
  Classical.choose_spec (h.exists_simultaneousConjugatingPoint
    hG hPic t' ht hmax ht' hmax' B B' i i' hi hi' hti hti')

end HasSplitBorelVectorSeries

end Langlands.GroupScheme
