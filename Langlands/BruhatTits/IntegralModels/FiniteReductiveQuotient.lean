import Langlands.BruhatTits.IntegralModels.DepthZeroInduction
import Langlands.AlgebraicGeometry.PointTopology.AffineSchemeTopologyFamily
import Langlands.GroupScheme.IntegralModel.CongruenceNeighborhoodBasisProof
import Langlands.AlgebraicGeometry.LangWeil.AffineCurvePlaneComparison
import Mathlib.GroupTheory.Index

/-! # Finiteness of the depth-zero reductive quotient

Over a finite coefficient ring, an affine group scheme of finite type has only
finitely many rational points. For supplied KP models over a local base with
finite residue field, the residue-field points `Gred(f)` of a finite-type
quotient therefore form a finite group, and the radical preimage
`G(K)^{0+} ∩ G^0(R)` has finite index `|Gred(f)|` in `G^0(R)`.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

open Langlands.AlgebraicGeometry.PointTopology

/-- A finite-type affine group scheme over a finite commutative ring `k` has
finitely many `k`-points. -/
theorem finite_rationalPoints {k : Type u} [CommRing k] [Finite k]
    (G : GroupScheme (Spec (CommRingCat.of k))) [IsAffineHom G.X.hom]
    [LocallyOfFiniteType G.X.hom] : Finite (rationalPoints G) := by
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have : Finite (AffineCoordinateRing k G.X →ₐ[k] k) :=
    Langlands.AlgebraicGeometry.LangWeil.CurvePlane.finite_algHom_of_finiteType
  exact Finite.of_equiv _ ((rationalPointEquiv k G.X).trans
    ((affineSchemePointEquiv k G.X k).trans AlgPoint.algHomEquiv)).symm

end Langlands.GroupScheme

namespace Langlands.BruhatTits.IntegralModels

open GroupScheme

variable {R K : Type u} [CommRing R] [IsDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K]
  {G : GroupScheme (Spec (CommRingCat.of K))}

section Local

variable [IsLocalRing R] [Finite (IsLocalRing.ResidueField R)]

namespace SpecialFibreQuotientData

variable {D : RelativeComponentModelData R K G} (Q : SpecialFibreQuotientData D)

/-- With finite residue field, a finite-type supplied quotient has finitely
many residue-field points. -/
theorem finite_quotientPoints [LocallyOfFiniteType Q.quotient.X.hom] :
    Finite (rationalPoints Q.quotient) :=
  finite_rationalPoints Q.quotient

/-- A connected reductive supplied quotient over a finite residue field has
finitely many residue-field points. -/
theorem finite_quotientPoints_of_isConnectedReductive
    (h : IsConnectedReductive Q.quotient) : Finite (rationalPoints Q.quotient) := by
  have : Smooth Q.quotient.X.hom := h.smooth
  exact Q.finite_quotientPoints

/-- The finite group `Gred(f)` of residue-field points of a finite-type
supplied quotient. -/
def finiteQuotientGroup [LocallyOfFiniteType Q.quotient.X.hom] : FiniteGrp.{u} :=
  haveI := Q.finite_quotientPoints
  FiniteGrp.of (rationalPoints Q.quotient)

/-- The reduction kernel has finite index in `G^0(R)`. -/
theorem ker_parahoricReduction_finiteIndex [LocallyOfFiniteType Q.quotient.X.hom] :
    Q.parahoricReduction.ker.FiniteIndex := by
  have := Q.finite_quotientPoints
  infer_instance

/-- The radical preimage `G(K)^{0+} ∩ G^0(R)` has finite index in `G^0(R)`. -/
theorem positivePoints_subgroupOf_finiteIndex [LocallyOfFiniteType Q.quotient.X.hom]
    (hQ : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range Q.radicalInclusion)
      Q.projection) :
    (Q.positivePoints.subgroupOf D.neutral.integralPoints).FiniteIndex := by
  rw [← Q.ker_parahoricReduction hQ]
  exact Q.ker_parahoricReduction_finiteIndex

end SpecialFibreQuotientData

end Local

section Henselian

variable [HenselianLocalRing R] [Finite (IsLocalRing.ResidueField R)]

namespace SpecialFibreQuotientData

variable {D : RelativeComponentModelData R K G} (Q : SpecialFibreQuotientData D)

/-- Over a Henselian local base with finite residue field, the index of
`G(K)^{0+} ∩ G^0(R)` in `G^0(R)` is the number of points of `Gred(f)`. -/
theorem index_positivePoints_subgroupOf
    (hrad : IsUnipotentRadical Q.radicalInclusion)
    (hQ : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range Q.radicalInclusion)
      Q.projection) :
    (Q.positivePoints.subgroupOf D.neutral.integralPoints).index =
      Nat.card (rationalPoints Q.quotient) := by
  rw [← Q.ker_parahoricReduction hQ, Subgroup.index_ker,
    MonoidHom.range_eq_top.mpr (Q.parahoricReduction_surjective hrad hQ),
    Subgroup.card_top]

end SpecialFibreQuotientData

end Henselian

section LocalField

open Langlands.AlgebraicGeometry.PointTopology
open scoped ValuativeRel

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {G : GroupScheme (Spec (CommRingCat.of F))}

namespace SpecialFibreQuotientData

variable {D : RelativeComponentModelData 𝒪[F] F G} (Q : SpecialFibreQuotientData D)

/-- Over the valuation ring of a nonarchimedean local field `F`, the index of
`G(F)^{0+} ∩ G^0(𝒪)` in `G^0(𝒪)` is the number of points of `Gred(𝓀)`. -/
theorem localField_index_positivePoints_subgroupOf
    (hrad : IsUnipotentRadical Q.radicalInclusion)
    (hQ : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range Q.radicalInclusion)
      Q.projection) :
    (Q.positivePoints.subgroupOf D.neutral.integralPoints).index =
      Nat.card (rationalPoints Q.quotient) :=
  letI : HenselianLocalRing 𝒪[F] := henselianLocalRing_integer
  Q.index_positivePoints_subgroupOf hrad hQ

/-- Over a nonarchimedean local field, with `G(F)` carrying its canonical
topology, the reduction kernel is open in `G^0(𝒪)`. -/
theorem localField_isOpen_ker_parahoricReduction [IsAffine G.X.left]
    [LocallyOfFiniteType G.X.hom] :
    letI : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
    IsOpen (Q.parahoricReduction.ker : Set D.neutral.integralPoints) :=
  letI : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
  letI : IsTopologicalGroup (rationalPoints G) := rationalPoint_isTopologicalGroup F G
  Q.isOpen_ker_parahoricReduction
    (isOpen_congruenceSubgroup_of_congruenceBasis
      GroupScheme.LocalFieldIntegralModel.congruenceNeighborhoodBasis_proof D)

end SpecialFibreQuotientData

end LocalField

end Langlands.BruhatTits.IntegralModels
