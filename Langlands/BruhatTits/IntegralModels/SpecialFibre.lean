import Langlands.BruhatTits.IntegralModels.ModelMorphism
import Langlands.BruhatTits.IntegralModels.IntegralTorus
import Langlands.GroupScheme.SchematicImage
import Langlands.GroupScheme.Absolute.Borel
import Langlands.GroupScheme.Reductive.UnipotentRadical

/-! # Actual special-fibre quotients and parabolic images for KP models

These are supplied objects and expanded validity predicates. No radical,
quotient, parabolicity or model existence theorem is asserted.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.BruhatTits.IntegralModels

open GroupScheme

variable {R K : Type u} [CommRing R] [IsDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K] [IsLocalRing R]
  {G : GroupScheme (Spec (CommRingCat.of K))}

local instance neutralSpecialFibre_affine (D : RelativeComponentModelData R K G) :
    IsAffineHom D.neutral.specialFibre.X.hom := by
  change IsAffineHom (CategoryTheory.Limits.pullback.snd D.neutral.group.X.hom
    (IntegralModel.residueBaseMap R))
  infer_instance

local instance neutralSpecialFibre_isAffine (D : RelativeComponentModelData R K G) :
    IsAffine D.neutral.specialFibre.X.left :=
  isAffine_of_isAffineHom D.neutral.specialFibre.X.hom

/-- Supplied representatives of the radical and an affine quotient of the
actual neutral special fibre. Their defining properties are asserted by
`IsReductiveQuotient`, rather than by the existence of this data. -/
structure SpecialFibreQuotientData (D : RelativeComponentModelData R K G) where
  radical : GroupScheme (Spec (CommRingCat.of (IsLocalRing.ResidueField R)))
  radicalInclusion : radical ⟶ D.neutral.specialFibre
  quotient : GroupScheme (Spec (CommRingCat.of (IsLocalRing.ResidueField R)))
  [quotient_affine : IsAffineHom quotient.X.hom]
  projection : D.neutral.specialFibre ⟶ quotient

attribute [instance] SpecialFibreQuotientData.quotient_affine

local instance quotient_isAffine {D : RelativeComponentModelData R K G}
    (Q : SpecialFibreQuotientData D) : IsAffine Q.quotient.X.left :=
  isAffine_of_isAffineHom Q.quotient.X.hom

namespace SpecialFibreQuotientData

variable {D : RelativeComponentModelData R K G} (Q : SpecialFibreQuotientData D)

/-- The specified radical is the greatest smooth connected normal unipotent
closed subgroup, and the specified actual quotient is its represented fppf
quotient and a connected reductive group. -/
def IsReductiveQuotient : Prop :=
  IsUnipotentRadical Q.radicalInclusion ∧
    RelativeRoot.IsFppfQuotient (SubgroupFunctor.range Q.radicalInclusion) Q.projection ∧
      IsConnectedReductive Q.quotient

/-- The actual residue-field points of the represented radical, as a subgroup
of the neutral special-fibre points. -/
def radicalPoints : Subgroup (rationalPoints D.neutral.specialFibre) :=
  (rationalPoints.map Q.radicalInclusion).range

/-- The inverse image of the radical's residue-field points under reduction. -/
def positiveSections : Subgroup D.neutral.integralSections :=
  Q.radicalPoints.comap D.neutral.reduction

/-- The subgroup denoted `G(K)^{0+}_F`, inside the original generic group,
obtained from the actual radical preimage in integral sections. -/
def positivePoints : Subgroup (rationalPoints G) :=
  Q.positiveSections.map D.neutral.integralPointMap

/-- The positive subgroup is defined by an actual integral section reducing
to a point of the supplied radical. -/
theorem mem_positivePoints (g : rationalPoints G) :
    g ∈ Q.positivePoints ↔
      ∃ x : D.neutral.integralSections,
        D.neutral.reduction x ∈ Q.radicalPoints ∧ D.neutral.integralPointMap x = g :=
  Iff.rfl

/-- Every positive point belongs to the neutral integral-point image. -/
theorem positivePoints_le_integralPoints :
    Q.positivePoints ≤ D.neutral.integralPoints := by
  rintro g ⟨x, _, rfl⟩
  exact ⟨x, rfl⟩

end SpecialFibreQuotientData

namespace RelativeComponentModelHom

variable {source target : RelativeComponentModelData R K G}
  (φ : RelativeComponentModelHom source target)

/-- The actual schematic image denoted `p_F(F')`, in the neutral special
fibre for `F`, for a map with source indexed by `F'` and target by `F`. -/
abbrev specialFibreImage :=
  SchematicImage.image φ.neutralSpecialFibreMap

/-- The actual closed inclusion of `p_F(F')` into the neutral special fibre. -/
abbrev specialFibreImageInclusion : φ.specialFibreImage ⟶ target.neutral.specialFibre :=
  SchematicImage.inclusion φ.neutralSpecialFibreMap

/-- KP Axiom 4.1.22(2), for a supplied comparable pair of facets. -/
def HasParabolicSpecialFibreImage : Prop :=
  IsParabolicSubgroup φ.specialFibreImageInclusion

/-- The residue-field points of `p_F(F')`, including all points of the
image group scheme, without assuming surjectivity on rational points. -/
def specialFibreImagePoints : Subgroup (rationalPoints target.neutral.specialFibre) :=
  (rationalPoints.map φ.specialFibreImageInclusion).range

/-- KP Axiom 4.1.22(4): the reduction preimage of `p_F(F')(f)` is the
actual image of the integral sections for `F'` in those for `F`. -/
def HasParabolicReductionPreimage : Prop :=
  φ.specialFibreImagePoints.comap target.neutral.reduction =
    (rationalPoints.map φ.neutral.hom).range

variable (Q : SpecialFibreQuotientData target)

/-- The actual image denoted `℘_F(F')` in the specified maximal reductive
quotient, constructed from the same neutral special-fibre map. -/
abbrev reductiveImage :=
  SchematicImage.image (φ.neutralSpecialFibreMap ≫ Q.projection)

/-- The closed inclusion of the actual reductive-quotient image. -/
abbrev reductiveImageInclusion : φ.reductiveImage Q ⟶ Q.quotient :=
  SchematicImage.inclusion (φ.neutralSpecialFibreMap ≫ Q.projection)

/-- The quotient image is a parabolic subgroup of the actual quotient, as
used in KP Axiom 4.1.22(3) and the order correspondence in part (5). -/
def HasParabolicReductiveImage : Prop :=
  IsParabolicSubgroup (φ.reductiveImageInclusion Q)

variable {S : CommGroupScheme (Spec (CommRingCat.of K))} {i : S.toGrp ⟶ G}
  (T : IntegralTorusData source S i)

/-- The source integral torus's special fibre, included into the target
neutral special fibre using the actual model morphism. -/
def targetTorusInclusion : T.specialFibre.toGrp ⟶ target.neutral.specialFibre :=
  T.specialFibreInclusion ≫ φ.neutralSpecialFibreMap

/-- The same torus's specified image in the actual reductive quotient. -/
def quotientTorusInclusion : T.specialFibre.toGrp ⟶ Q.quotient :=
  φ.targetTorusInclusion T ≫ Q.projection

/-- The maximal-split-torus assertions of KP Axiom 4.1.22(3): the same
source torus is maximal split in both neutral special fibres and maps
isomorphically onto a maximal split torus of the actual reductive quotient.
The closed inclusions express the claimed isomorphisms onto those images. -/
def HasMaximalSplitTori : Prop :=
  T.HasMaximalSplitSpecialFibre ∧
    IsMaximalSplitTorus (φ.targetTorusInclusion T) ∧
      IsMaximalSplitTorus (φ.quotientTorusInclusion Q T)

variable (Qsource : SpecialFibreQuotientData source)

/-- KP Axiom 4.1.22(7), with the actual positive subgroups inside the same
original rational-point group. Source corresponds to `F'`, target to `F`.
Both reduction maps called surjective in the source remain explicit. -/
def SatisfiesPositiveRadicalClause : Prop :=
  Function.Surjective target.neutral.reduction ∧
    Function.Surjective source.neutral.reduction ∧
    Q.positivePoints ≤ Qsource.positivePoints

end RelativeComponentModelHom
end Langlands.BruhatTits.IntegralModels
