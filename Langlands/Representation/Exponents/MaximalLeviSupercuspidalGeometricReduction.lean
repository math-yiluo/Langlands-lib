import Langlands.GroupScheme.Rational.MaximalLeviParabolicFamilyProof
import Langlands.Representation.Geometric.MaximalLeviParabolicBudget
import Langlands.Representation.Geometric.RepresentedGeometricLemmaProof
import Langlands.Representation.Exponents.LeviSupercuspidalInductionDetection
import Langlands.Representation.Exponents.LeviJacquetNonSupercuspidalReduction
import Langlands.Representation.Exponents.RepresentedCuspidalRemainderSplittingStatement

/-! # The represented maximal-Levi length bound from VI.5.1 and VI.5.3(ii) -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

/-- The actual-parabolic family and survivor count construct the exact maximal-Levi
Jacquet witness from the geometric lemma and VI.5.3(ii). Neither finite length,
a detecting family nor Coxeter coordinates are additional premises. -/
theorem maximalLeviSupercuspidalJacquetLengthWitness_of_geometricLemma_noSupercuspidal
    (hgeom : RepresentedGeometricLemmaStatement.{u, v})
    (hns : LeviJacquetInductionNoSupercuspidalStatement.{u, v}) :
    MaximalLeviSupercuspidalJacquetLengthWitnessStatement.{u, v} := by
  classical
  intro k _ _ _ _ _ G hG
  let := hG.isAffineHom
  let : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
  intro _ _ P M N p l r hp hl hr hmul hproper hmax
  let := hl.isConnectedReductive.isAffineHom
  let : TopologicalSpace (rationalPoints M) := leviPointTopology l hl
  let : LocallyCompactSpace (rationalPoints M) := leviPoints_locallyCompactSpace p l hp hl
  let : NonarchimedeanGroup (rationalPoints M) := leviPoints_nonarchimedeanGroup p l hp hl
  intro ρ hρ hcusp
  obtain ⟨n, -, Q, U, q, lQ, rQ, hq, hlQ, hrQ, hmulQ, hcomp, hsep, hcover⟩ :=
    maximalLeviParabolicFamily k G hG P M p l hp hl hproper hmax
  have hfil (a : Fin n) :=
    hgeom k G hG P M N (Q a) M (U a) p l r hp hl hr hmul
      (q a) (lQ a) (rQ a) (hq a) (hlQ a) (hrQ a) (hmulQ a)
  choose m c z hz D hglue using hfil
  have hdetect : ∀ A : SmoothRep.{0, u, max u v} ℂ (rationalPoints G),
      A.IsIrreducible →
      SmoothRep.IsSubquotient A ((leviInductionFunctor p l r hp hr hl hmul).obj ρ) →
      ∃ a, letI := leviPointTopology (lQ a) (hlQ a)
        Nontrivial ((leviJacquetFunctor (q a) (lQ a) (rQ a)
          (hq a) (hrQ a) (hlQ a) (hmulQ a)).obj A) := by
    intro A hA hsub
    obtain ⟨Q', L', U', q', l', r', hq', hl', hr', hmul', ⟨g, φ, hφ⟩, hJ, -⟩ :=
      exists_conjugateLevi_supercuspidal_jacquetQuotient
        hns hG p l r hp hl hr hmul ρ hcusp A hA hsub
    obtain ⟨a, t, ht⟩ := hcover Q' L' q' l' hq' hl' φ g hφ
    have hrange : SubgroupFunctor.range (q a) =
        SubgroupFunctor.range (q' ≫ (G.innerIso t).hom) := by
      rw [range_comp_iso_hom_eq_comap]
      exact ((SubgroupFunctor.eq_comap_iso_iff (G.innerIso t)).mp ht).symm
    refine ⟨a, ?_⟩
    exact nontrivial_leviJacquet_of_range_eq_comp_innerIso
      q' l' r' hq' hl' hr' hmul'
      (q a) (lQ a) (rQ a) (hq a) (hlQ a) (hrQ a) (hmulQ a) t hrange A hJ
  exact hasRepresentedJacquetLengthWitness_of_separated_geometric_family
    D ρ hρ hcusp hG hproper hmax (fun _ => Iso.refl M) hsep c hz hglue hdetect

/-- The geometric lemma and VI.5.3(ii) imply the exact maximal-Levi length bound. -/
theorem maximalLeviSupercuspidalLengthBound_of_geometricLemma_noSupercuspidal
    (hgeom : RepresentedGeometricLemmaStatement.{u, v})
    (hns : LeviJacquetInductionNoSupercuspidalStatement.{u, v}) :
    MaximalLeviSupercuspidalInductionLengthBoundStatement.{u, v} :=
  maximalLeviSupercuspidalLengthBound_of_jacquetLengthWitness
    (maximalLeviSupercuspidalJacquetLengthWitness_of_geometricLemma_noSupercuspidal hgeom hns)

/-- VI.5.3(ii) is supplied by its separate reduction from the geometric lemma
and exclusion of supercuspidal subquotients from proper induction (VI.5.2). -/
theorem maximalLeviSupercuspidalLengthBound_of_geometricLemma_properInductionExclusion
    (hgeom : RepresentedGeometricLemmaStatement.{u, v})
    (hind : LeviInductionNoSupercuspidalSubquotientStatement.{u, v}) :
    MaximalLeviSupercuspidalInductionLengthBoundStatement.{u, v} :=
  maximalLeviSupercuspidalLengthBound_of_geometricLemma_noSupercuspidal hgeom
    (leviJacquetInductionNoSupercuspidal_of_geometricLemma hgeom hind)

/-- The exact maximal-Levi length bound follows from the geometric lemma and
the objectwise cuspidal/remainder splitting, at the carrier universe required
by proper-induction exclusion. Both inputs remain explicit hypotheses. -/
theorem maximalLeviSupercuspidalLengthBound_of_geometricLemma_cuspidalSplitting
    (hgeom : RepresentedGeometricLemmaStatement.{u, v})
    (hsplit : RepresentedCuspidalRemainderSplittingStatement.{u, max u v}) :
    MaximalLeviSupercuspidalInductionLengthBoundStatement.{u, v} :=
  maximalLeviSupercuspidalLengthBound_of_geometricLemma_properInductionExclusion hgeom
    (leviInductionNoSupercuspidalSubquotient_of_cuspidalRemainderSplitting hsplit)

/-- The published geometric lemma leaves only the exact objectwise
cuspidal/remainder splitting as a premise of the length-bound reduction. -/
theorem maximalLeviSupercuspidalLengthBound_of_cuspidalSplitting
    (hsplit : RepresentedCuspidalRemainderSplittingStatement.{u, max u v}) :
    MaximalLeviSupercuspidalInductionLengthBoundStatement.{u, v} :=
  maximalLeviSupercuspidalLengthBound_of_geometricLemma_cuspidalSplitting
    representedGeometricLemma hsplit

end Langlands.Aubert.General.RepresentedParabolic
