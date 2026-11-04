import Langlands.BruhatTits.IntegralModels.SpecialFibre
import Langlands.Geometry.Building.ParahoricBuildingAxioms
import Langlands.GroupScheme.Lie.KernelTargetMaps
import Langlands.GroupScheme.Torus.SplitLatticeBaseChange
import Langlands.GroupScheme.Torus.WeightDecomposition

/-! # Actual special-fibre Lie weights and the KP facet sign formula

Character specialization is derived from the supplied integral split torus.
The sign formula compares the actual Lie image of the parabolic inclusion
with the actual roots of the supplied reductive quotient.
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

namespace IntegralTorusData

variable {D : RelativeComponentModelData R K G}
  {S : CommGroupScheme (Spec (CommRingCat.of K))} {i : S.toGrp ⟶ G}
  (T : IntegralTorusData D S i)

/-- The generic-fibre character of an actual integral character, using the
specified generic isomorphism of the integral torus. -/
def genericCharacter : characterLattice T.torus →+ characterLattice S :=
  (characterLattice.comapIso T.genericIso).symm.toAddMonoidHom.comp
    (characterLattice.baseChange (Spec.algebraMap R K) T.torus)

/-- The residue-base change of an actual integral character. -/
def specialCharacter : characterLattice T.torus →+ characterLattice T.specialFibre :=
  characterLattice.baseChange (IntegralModel.residueBaseMap R) T.torus

/-- Characters of a split integral torus are identified with characters of
its specified generic fibre by the actual base-change map. -/
def genericCharacterEquiv (hT : IsSplitTorus T.torus.toGrp) :
    characterLattice T.torus ≃+ characterLattice S :=
  (AddEquiv.ofBijective (characterLattice.baseChange (Spec.algebraMap R K) T.torus)
    (hT.characterLattice_baseChange_bijective (Spec.algebraMap R K) T.torus)).trans
      (characterLattice.comapIso T.genericIso).symm

/-- Characters of a split integral torus are identified with characters of
its actual special fibre by the residue-base-change map. -/
def specialCharacterEquiv (hT : IsSplitTorus T.torus.toGrp) :
    characterLattice T.torus ≃+ characterLattice T.specialFibre :=
  AddEquiv.ofBijective T.specialCharacter
    (hT.characterLattice_baseChange_bijective (IntegralModel.residueBaseMap R) T.torus)

/-- The canonical generic-to-special character identification through the
same integral split torus, with no freely chosen lattice map. -/
def characterSpecialization (hT : IsSplitTorus T.torus.toGrp) :
    characterLattice S ≃+ characterLattice T.specialFibre :=
  (T.genericCharacterEquiv hT).symm.trans (T.specialCharacterEquiv hT)

/-- Generic and special characters are obtained from the same integral
character. This is the compatibility used in the facet sign formula. -/
theorem characterSpecialization_genericCharacter (hT : IsSplitTorus T.torus.toGrp)
    (χ : characterLattice T.torus) :
    T.characterSpecialization hT (T.genericCharacter χ) = T.specialCharacter χ := by
  change T.specialCharacterEquiv hT
    ((T.genericCharacterEquiv hT).symm (T.genericCharacterEquiv hT χ)) = _
  rw [AddEquiv.symm_apply_apply]
  rfl

end IntegralTorusData

section LieImage

variable {k : Type u} [Field k]
  {S : CommGroupScheme (Spec (CommRingCat.of k))}
  {H Q : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom H.X.hom] [IsAffineHom Q.X.hom]

/-- Nonzero torus weights in the actual tangent image of an included
subgroup: the ambient weight space meets the differential image nontrivially.
For a closed subgroup containing the torus this is its adjoint Lie support. -/
def nonzeroLieImageWeights (i : S.toGrp ⟶ Q) (j : H ⟶ Q) :
    Set (characterLattice S) :=
  {χ | χ ≠ 0 ∧ weightSpace i χ ⊓ LinearMap.range (Lie.targetMapLinear j k) ≠ ⊥}

end LieImage

namespace RelativeComponentModelHom

variable [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [IsAffineHom G.X.hom]
  (B : Geometry.Building.ValuationBuildingData G)
  {source target : RelativeComponentModelData R K G}
  (φ : RelativeComponentModelHom source target)
  (Q : SpecialFibreQuotientData target)
  (T : IntegralTorusData source B.S B.i)

local instance neutralSpecialFibre_affine (D : RelativeComponentModelData R K G) :
    IsAffineHom D.neutral.specialFibre.X.hom := by
  change IsAffineHom (CategoryTheory.Limits.pullback.snd D.neutral.group.X.hom
    (IntegralModel.residueBaseMap R))
  infer_instance

local instance neutralSpecialFibre_isAffine (D : RelativeComponentModelData R K G) :
    IsAffine D.neutral.specialFibre.X.left :=
  isAffine_of_isAffineHom D.neutral.specialFibre.X.hom

local instance quotient_isAffine :
    IsAffine Q.quotient.X.left :=
  isAffine_of_isAffineHom Q.quotient.X.hom

/-- The second paragraph of KP Axiom 4.1.22(3), on a supplied pair of
apartment facets. For every `x ∈ F` and every actual cocharacter vector whose
projection carries `x` into `F'`, the nonzero weights in the actual Lie
image of `℘_F(F')` are exactly the quotient roots nonnegative on that vector.
Facet and incidence validity are supplied by the surrounding indexed clause. -/
def HasLieWeightSignFormula (hT : IsSplitTorus T.torus.toGrp)
    (F F' : Set B.Apartment) : Prop :=
  ∀ x ∈ F, ∀ v : RealTorusSpace.V B.S,
    (Submodule.Quotient.mk v : Geometry.Building.TranslationSpace B.i) +ᵥ x ∈ F' →
      nonzeroLieImageWeights (φ.quotientTorusInclusion Q T) (φ.reductiveImageInclusion Q) =
        {χ | χ ∈ relativeRoots (φ.quotientTorusInclusion Q T) ∧
          0 ≤ RealTorusSpace.eval B.S ((T.characterSpecialization hT).symm χ) v}

end RelativeComponentModelHom
end Langlands.BruhatTits.IntegralModels
