import Langlands.AlgebraicGeometry.AlgebraicSpace.CoordinatePointTopologyFacts
import Langlands.AlgebraicGeometry.AlgebraicSpace.RelativeIntegralPoints
import Langlands.AlgebraicGeometry.AlgebraicSpace.EtaleChartSeparated
import Langlands.Global.AdelicSpaceLocalFields

/-!
# The factors of an adelic level

For a separated algebraic space `X` of finite type over a ring `C`, the factor topologies of
the adelic levels are of two kinds. Over a henselian valued field `K`, along a bijective field
map, the factor is homeomorphic to the étale-chart topology on `X_K(K)`: it is Hausdorff, and
locally compact when `K` is. Along the inclusion of a henselian valuation ring `O ⊆ K` that is
the closed unit ball, the factor embeds in `X_K(K)` with open image (Corollary 5.7), and it is
compact when `K` is locally compact.
-/

noncomputable section

universe u

open CategoryTheory Topology
open _root_.AlgebraicGeometry
open Langlands.AlgebraicGeometry (AlgebraicSpace)
open Langlands.AlgebraicGeometry.AlgebraicSpace
open Langlands.AlgebraicGeometry.AlgebraicSpace.CoordinatePointTopologyFacts
open Langlands.AlgebraicGeometry.PointTopology (IsHenselianValuedField)

namespace Langlands.Global

namespace AdelicSpaceLevelFactors

variable {C : Type u} [CommRing C] {X : AlgebraicSpace (Spec (CommRingCat.of C))}

theorem locallyOfFiniteTypeOverBase (hft : FiniteTypeOverRing C X) :
    LocallyOfFiniteTypeOverBase X := by
  obtain ⟨U, a, ha, hs, hP⟩ := hft
  exact ⟨U, a, ha, hs, hP.1⟩

variable {K : Type u} [NontriviallyNormedField K] [Algebra C K]

theorem isQuasiSeparatedLocallyFiniteType (hX : IsSeparated X) (hft : FiniteTypeOverRing C X) :
    IsQuasiSeparatedLocallyFiniteType K (baseChange (Spec.algebraMap C K) X) :=
  ⟨(SpaceProductPoints.isQuasiSeparated_of_isSeparated hX).baseChange,
    (locallyOfFiniteTypeOverBase hft).baseChange⟩

theorem t2Space_etale (hK : IsHenselianValuedField K) (hX : IsSeparated X)
    (hft : FiniteTypeOverRing C X) :
    @T2Space _ (etaleChartTopology K (baseChange (Spec.algebraMap C K) X)) :=
  t2Space_etaleChartTopology hK (isQuasiSeparatedLocallyFiniteType hX hft) hX.baseChange

section FieldFactor

variable {R : Type u} [CommRing R] [Algebra C R] (φ : R →ₐ[C] K) (hφ : Function.Bijective φ)
include hφ

/-- A field factor is Hausdorff. -/
theorem t2Space_field (hK : IsHenselianValuedField K) (hX : IsSeparated X)
    (hft : FiniteTypeOverRing C X) : @T2Space _ (fieldValuedPointTopology C X φ) :=
  t2Space_fieldValuedPointTopology X φ (fieldValuedPointMap_bijective X φ hφ).1
    (t2Space_etale hK hX hft)

/-- A field factor over a locally compact field is locally compact. -/
theorem locallyCompactSpace_field (hK : IsHenselianValuedField K) [LocallyCompactSpace K]
    (hX : IsSeparated X) (hft : FiniteTypeOverRing C X) :
    @LocallyCompactSpace _ (fieldValuedPointTopology C X φ) := by
  let : TopologicalSpace (RingPoints C X R) := fieldValuedPointTopology C X φ
  let : TopologicalSpace (RingPoints K (baseChange (Spec.algebraMap C K) X) K) :=
    etaleChartTopology K (baseChange (Spec.algebraMap C K) X)
  have : LocallyCompactSpace (RingPoints K (baseChange (Spec.algebraMap C K) X) K) :=
    locallyCompactSpace_etaleChartTopology hK (isQuasiSeparatedLocallyFiniteType hX hft)
  exact (isHomeomorph_fieldValuedPointMap X φ hφ).isOpenEmbedding.locallyCompactSpace

end FieldFactor

section IntegerFactor

variable (O : Subring K) [Algebra C O] [IsScalarTower C O K]

/-- For separated `X`, the map `X(O) → X_K(K)` is injective. -/
theorem injective_integer (hX : IsSeparated X) :
    Function.Injective (fieldValuedPointMap C X (IsScalarTower.toAlgHom C O K)) :=
  (baseChangeRingPointsEquiv C K K X).symm.injective.comp
    (RelativeIntegralPoints.changeRing_injective hX _ Subtype.val_injective)

/-- An integer factor is Hausdorff. -/
theorem t2Space_integer (hK : IsHenselianValuedField K) (hX : IsSeparated X)
    (hft : FiniteTypeOverRing C X) :
    @T2Space _ (fieldValuedPointTopology C X (IsScalarTower.toAlgHom C O K)) :=
  t2Space_fieldValuedPointTopology X _ (injective_integer O hX) (t2Space_etale hK hX hft)

/-- An integer factor over a locally compact field is compact. -/
theorem compactSpace_integer (hO : ∀ x : K, x ∈ O ↔ ‖x‖ ≤ 1) (hhen : HenselianLocalRing O)
    [LocallyCompactSpace K] (hX : IsSeparated X) (hft : FiniteTypeOverRing C X) :
    @CompactSpace _ (fieldValuedPointTopology C X (IsScalarTower.toAlgHom C O K)) :=
  compactSpace_fieldValuedPointTopology X _
    (RelativeIntegralPoints.isCompact_range_fieldValuedPointMap O hO hhen
      (SpaceProductPoints.isQuasiSeparated_of_isSeparated hX) hft)

/-- An integer factor over a locally compact field is locally compact. -/
theorem locallyCompactSpace_integer (hK : IsHenselianValuedField K)
    (hO : ∀ x : K, x ∈ O ↔ ‖x‖ ≤ 1) (hhen : HenselianLocalRing O) [LocallyCompactSpace K]
    (hX : IsSeparated X) (hft : FiniteTypeOverRing C X) :
    @LocallyCompactSpace _ (fieldValuedPointTopology C X (IsScalarTower.toAlgHom C O K)) := by
  let : TopologicalSpace (RingPoints C X O) :=
    fieldValuedPointTopology C X (IsScalarTower.toAlgHom C O K)
  have : CompactSpace (RingPoints C X O) := compactSpace_integer O hO hhen hX hft
  have : T2Space (RingPoints C X O) := t2Space_integer O hK hX hft
  infer_instance

/-- The image of `X(O)` in `X_K(K)` is open. -/
theorem isOpen_range_integer (hO : ∀ x : K, x ∈ O ↔ ‖x‖ ≤ 1) (hhen : HenselianLocalRing O)
    (hX : IsSeparated X) (hft : FiniteTypeOverRing C X) :
    IsOpen[etaleChartTopology K (baseChange (Spec.algebraMap C K) X)]
      (Set.range (fieldValuedPointMap C X (IsScalarTower.toAlgHom C O K))) :=
  RelativeIntegralPoints.isOpen_range_fieldValuedPointMap O hO hhen
    (SpaceProductPoints.isQuasiSeparated_of_isSeparated hX) (locallyOfFiniteTypeOverBase hft)

end IntegerFactor

end AdelicSpaceLevelFactors

end Langlands.Global
