import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalSemistandardProjectionContinuityProof
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalIwasawaCompactExistenceProof
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalXiChangeMinimal
import Langlands.GroupScheme.Rational.GenericMinimalParabolicProof
import Langlands.GroupScheme.Rational.MinimalParabolicConjugacyProof
import Langlands.GroupScheme.Rational.MinimalParabolicConjugacyReduction
import Langlands.GroupScheme.Rational.ParabolicContainsMinimalProof

/-! # Compact-picture data from compact-open Iwasawa existence -/

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.HarishChandraSchwartz.RationalSemistandard

/-- Compact-picture data for every intrinsic semistandard index. -/
theorem compactDataExistence {F : Type u} [Field F]
    {S : CommGroupScheme (Spec (CommRingCat.of F))}
    {G : GroupScheme (Spec (CommRingCat.of F))} {i : S.toGrp ⟶ G}
    [ValuativeRel F] [TopologicalSpace F] [IsAffineHom G.X.hom] :
    CompactDataExistenceStatement (i := i) := by
  intro hF hG hi p
  let : IsNonarchimedeanLocalField F := hF
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let : Smooth G.X.hom := hG.smooth
  let : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
  obtain ⟨T, j, ν, K, hj, hν, hK, hPK⟩ := rationalIwasawaCompactExistence F G hG
  have hMin : IsMinimalParabolicFunctor (standardParabolic j ν ∅) := by
    rw [standardParabolic_empty_eq_dynamic_of_generic j ν hG hj hν]
    exact genericMinimalParabolic F G hG T j hj ν hν
  obtain ⟨Q, hQ, hle⟩ := IsParabolicFunctor.exists_minimal_le_of_statement
    parabolicContainsMinimalStatement hG p.isParabolicWithLeviAndRadical.isParabolicFunctor
  obtain ⟨g, hg⟩ := IsMinimalParabolicFunctor.isRationallyConjugate_of_statement
    minimalParabolicConjugacy hG hMin hQ
  have hconj (x : rationalPoints G) :
      x ∈ standardParabolicPoints j ν ∅ ↔ g * x * g⁻¹ ∈ Q.rationalPoints := by
    change x ∈ (standardParabolic j ν ∅).rationalPoints ↔ _
    rw [hg]
    exact SubgroupFunctor.mem_rationalPoints_comap_innerIso_hom Q g x
  obtain ⟨k, hk, hkconj⟩ := hPK.exists_mem_conjugator ⟨g, hconj⟩
  have hQK : IsIwasawaPair Q.rationalPoints K.toSubgroup := hPK.of_mem_conjugator hk hkconj
  have hpK : IsIwasawaPair (parabolic p) K.toSubgroup := hQK.mono (hle (Over.mk (𝟙 _)))
  exact ⟨{
    compact := K
    isCompact := hK
    projection_continuous := projectionContinuity hF hG hi p
    factorization := factorization_subtype hpK }⟩

end Langlands.HarishChandraSchwartz.RationalSemistandard
