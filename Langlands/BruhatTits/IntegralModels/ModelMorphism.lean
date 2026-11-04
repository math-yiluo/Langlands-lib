import Langlands.BruhatTits.IntegralModels.RelativeComponent
import Langlands.GroupScheme.Torus.Lattice
import Langlands.GroupScheme.Reductive.Basic
import Langlands.AbelianScheme.Kernel

/-! # Compatible morphisms between supplied KP models

The source models correspond to the larger subset in the ordering of
KP Axiom 4.1.22. This unit supplies no ordering or model existence assertion.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.BruhatTits.IntegralModels

open GroupScheme

variable {R K : Type u} [CommRing R] [IsDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K]
  {G : GroupScheme (Spec (CommRingCat.of K))}

/-- A supplied full-model morphism with identity generic fibre and its
compatible restriction to the actual relative identity components.
For `Ω ≺ Ω'`, the direction is from the models of `Ω'` to those of `Ω`. -/
structure RelativeComponentModelHom
    (source target : RelativeComponentModelData R K G) where
  full : source.full.Hom target.full (𝟙 G)
  neutral : source.neutral.Hom target.neutral (𝟙 G)
  component_comm :
    neutral.hom ≫ target.inclusion.hom = source.inclusion.hom ≫ full.hom

namespace RelativeComponentModelHom

variable {source target : RelativeComponentModelData R K G}
  (φ : RelativeComponentModelHom source target)

/-- The full-model morphism acts on generic points as the identity of `G`. -/
theorem full_integralPointMap (x : source.full.integralSections) :
    target.full.integralPointMap (rationalPoints.map φ.full.hom x) =
      source.full.integralPointMap x := by
  simpa [rationalPoints.map] using φ.full.integralPointMap_naturality x

/-- The restricted morphism also acts on generic points as the identity. -/
theorem neutral_integralPointMap (x : source.neutral.integralSections) :
    target.neutral.integralPointMap (rationalPoints.map φ.neutral.hom x) =
      source.neutral.integralPointMap x := by
  simpa [rationalPoints.map] using φ.neutral.integralPointMap_naturality x

include φ

/-- The full integral-point images are included in the required direction. -/
theorem full_integralPoints_le :
    source.full.integralPoints ≤ target.full.integralPoints := by
  rintro g ⟨x, rfl⟩
  exact ⟨rationalPoints.map φ.full.hom x, φ.full_integralPointMap x⟩

/-- The same inclusion holds for the neutral integral-point images. -/
theorem neutral_integralPoints_le :
    source.neutral.integralPoints ≤ target.neutral.integralPoints := by
  rintro g ⟨x, rfl⟩
  exact ⟨rationalPoints.map φ.neutral.hom x, φ.neutral_integralPointMap x⟩

section Residue

variable [IsLocalRing R]

/-- The actual residue-base change of the full-model morphism. -/
abbrev fullSpecialFibreMap : source.full.specialFibre ⟶ target.full.specialFibre :=
  φ.full.specialFibreMap

/-- The homomorphism `ρ̄` of KP Axiom 4.1.22 is between the neutral
special fibres, rather than their maximal reductive quotients. -/
abbrev neutralSpecialFibreMap :
    source.neutral.specialFibre ⟶ target.neutral.specialFibre :=
  φ.neutral.specialFibreMap

/-- The restriction square remains commutative on the actual special fibres. -/
theorem specialFibre_component_comm :
    φ.neutralSpecialFibreMap ≫ target.specialFibreMap =
      source.specialFibreMap ≫ φ.fullSpecialFibreMap := by
  change
    (baseChange (IntegralModel.residueBaseMap R)).map φ.neutral.hom ≫
        (baseChange (IntegralModel.residueBaseMap R)).map target.inclusion.hom =
      (baseChange (IntegralModel.residueBaseMap R)).map source.inclusion.hom ≫
        (baseChange (IntegralModel.residueBaseMap R)).map φ.full.hom
  simpa only [Functor.map_comp] using
    congrArg
      (fun f : source.neutral.group ⟶ target.full.group =>
        (baseChange (IntegralModel.residueBaseMap R)).map f)
      φ.component_comm

/-- The full-model special-fibre morphism commutes with reduction. -/
theorem full_reduction_naturality (x : source.full.integralSections) :
    target.full.reduction (rationalPoints.map φ.full.hom x) =
      rationalPoints.map φ.fullSpecialFibreMap (source.full.reduction x) :=
  φ.full.reduction_naturality x

/-- The restricted morphism commutes with reduction to the neutral special fibre. -/
theorem neutral_reduction_naturality (x : source.neutral.integralSections) :
    target.neutral.reduction (rationalPoints.map φ.neutral.hom x) =
      rationalPoints.map φ.neutralSpecialFibreMap (source.neutral.reduction x) :=
  φ.neutral.reduction_naturality x

/-- KP Axiom 4.1.22, preamble: every torus of the source neutral special
fibre is carried isomorphically onto a torus of the target. The composite
being a closed immersion realizes that image as the same torus `T`.
The quantifier includes nonsplit tori. -/
def PreservesTori : Prop :=
  ∀ (T : GroupScheme (Spec (CommRingCat.of (IsLocalRing.ResidueField R))))
    (i : T ⟶ source.neutral.specialFibre),
    IsTorus T → IsClosedSubgroup i →
      IsClosedSubgroup (i ≫ φ.neutralSpecialFibreMap)

/-- The actual scheme-theoretic kernel of the neutral special-fibre map. -/
abbrev specialFibreKernel :
    GroupScheme (Spec (CommRingCat.of (IsLocalRing.ResidueField R))) :=
  kernel φ.neutralSpecialFibreMap

/-- KP Axiom 4.1.22(1): the scheme-theoretic kernel is smooth, connected
and unipotent over the residue field. -/
def HasSmoothConnectedUnipotentKernel : Prop :=
  Smooth φ.specialFibreKernel.X.hom ∧
    ConnectedSpace φ.specialFibreKernel.X.left ∧
      IsUnipotent φ.specialFibreKernel

/-- The special-fibre assertions of the preamble and part (1), which apply
to all ordered nonempty bounded subsets, before the facet-only clauses. -/
def SatisfiesGeneralSpecialFibreClauses : Prop :=
  φ.PreservesTori ∧ φ.HasSmoothConnectedUnipotentKernel

end Residue
end RelativeComponentModelHom
end Langlands.BruhatTits.IntegralModels
