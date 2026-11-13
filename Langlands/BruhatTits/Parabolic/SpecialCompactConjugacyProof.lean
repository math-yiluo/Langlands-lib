import Langlands.BruhatTits.Parabolic.SpecialCompactConjugacyStatement
import Langlands.GroupScheme.Rational.StandardParabolicClassificationProof
import Langlands.GroupScheme.Rational.StandardParabolicOrderProof
import Langlands.GroupScheme.Rational.StandardLeviLiftIndependence

/-! # Parabolic conjugacy under a subgroup satisfying Iwasawa factorization -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Pointwise

namespace Langlands.BruhatTits

open Langlands.GroupScheme

/-- Renard V.5.1, first assertion of the Corollary: Iwasawa factorization for the
standard minimal parabolic makes every dynamic parabolic conjugate to a standard
one by a point of the given subgroup. -/
theorem specialCompactParabolicConjugacy :
    SpecialCompactParabolicConjugacyStatement.{u} := by
  intro F _ G hG S i hi ν
  have : IsAffineHom G.X.hom := hG.isAffineHom
  have : Mono i.hom.hom.left := hi.isSplitSubtorus.mono
  intro hν K hK zeta
  obtain ⟨⟨J, hJ⟩, ⟨g, hg⟩, -⟩ :=
    (standardParabolicClassification F G hG S i hi ν hν).2 zeta
  have hminJ : standardParabolic i ν ∅ ≤ standardParabolic i ν J :=
    ((standardParabolicOrder F G hG S i hi ν hν).1 ∅ J
      (Set.empty_subset _) hJ).1.mp (Set.empty_subset _)
  have hgPK : g ∈ (standardParabolicPoints i ν ∅ : Set (rationalPoints G)) * K := by
    rw [← hK.1]
    exact Set.mem_univ g
  obtain ⟨p, hp, k, hk, rfl⟩ := Set.mem_mul.mp hgPK
  refine ⟨J, hJ, k, hk, ?_⟩
  rw [hg, innerIso_mul_hom, SubgroupFunctor.comap_comp,
    SubgroupFunctor.comap_innerIso_hom_eq_of_mem _ (hminJ _ hp)]

end Langlands.BruhatTits
