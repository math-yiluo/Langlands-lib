import Langlands.BruhatTits.IntegralModels.FacetAxioms
import Langlands.BruhatTits.IntegralModels.FacetLieImageRoots
import Langlands.GroupScheme.Torus.SignedRootRestriction

/-! # The facet sign formula as a root identity, and its restriction to subtori

The KP facet sign formula is rewritten as an equality of root sets of the
special-fibre torus. This root identity passes from an integral split torus
`A` of the source model to every integral split torus `T` mapping into `A`,
for compatible sign functions on integral characters.
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
  {S S' : CommGroupScheme (Spec (CommRingCat.of K))} {i : S.toGrp ⟶ G} {i' : S'.toGrp ⟶ G}

/-- The residue-base change of a homomorphism between the integral tori. -/
abbrev specialFibreMap (T : IntegralTorusData D S i) (T' : IntegralTorusData D S' i')
    (ρ : T.torus ⟶ T'.torus) : T.specialFibre ⟶ T'.specialFibre :=
  (CommGroupScheme.baseChange (IntegralModel.residueBaseMap R)).map ρ

variable {T : IntegralTorusData D S i} {T' : IntegralTorusData D S' i'}

/-- A factorization of the integral torus inclusions specializes to the
special fibres. -/
theorem specialFibreMap_comp_specialFibreInclusion (ρ : T.torus ⟶ T'.torus)
    (hρ : CommGroupScheme.groupHom ρ ≫ T'.inclusion = T.inclusion) :
    CommGroupScheme.groupHom (specialFibreMap T T' ρ) ≫ T'.specialFibreInclusion =
      T.specialFibreInclusion := by
  rw [specialFibreInclusion, specialFibreInclusion, ← hρ, Functor.map_comp]
  rfl

/-- Residue-base change of characters is compatible with composition. -/
theorem specialCharacter_comp (ρ : T.torus ⟶ T'.torus) (ψ : characterLattice T'.torus) :
    T.specialCharacter (ρ ≫ ψ) = specialFibreMap T T' ρ ≫ T'.specialCharacter ψ :=
  characterLattice.baseChange_precomp _ ρ ψ

/-- The inverse character specialization is the generic character of the
integral character with the given residue-base change. -/
theorem characterSpecialization_symm_apply (hT : IsSplitTorus T.torus.toGrp)
    (χ : characterLattice T.specialFibre) :
    (T.characterSpecialization hT).symm χ =
      T.genericCharacter ((T.specialCharacterEquiv hT).symm χ) :=
  rfl

end IntegralTorusData

namespace RelativeComponentModelHom

variable {source target : RelativeComponentModelData R K G}
  (φ : RelativeComponentModelHom source target)
  (Q : SpecialFibreQuotientData target)
  {S S' : CommGroupScheme (Spec (CommRingCat.of K))} {i : S.toGrp ⟶ G} {i' : S'.toGrp ⟶ G}

attribute [local instance] neutralSpecialFibre_affine neutralSpecialFibre_isAffine
  quotient_isAffine

/-- The reductive image is of finite type when the quotient is: it is a
closed subgroup scheme. -/
instance reductiveImage_locallyOfFiniteType [LocallyOfFiniteType Q.quotient.X.hom] :
    LocallyOfFiniteType (φ.reductiveImage Q).X.hom := by
  rw [← Over.w (φ.reductiveImageInclusion Q).hom.hom]
  infer_instance

/-- A factorization of the integral torus inclusions factors the tori in the
reductive image. -/
theorem specialFibreMap_comp_reductiveImageTorusMap (T : IntegralTorusData source S i)
    (T' : IntegralTorusData source S' i') (ρ : T.torus ⟶ T'.torus)
    (hρ : CommGroupScheme.groupHom ρ ≫ T'.inclusion = T.inclusion) :
    CommGroupScheme.groupHom (T.specialFibreMap T' ρ) ≫ φ.reductiveImageTorusMap Q T' =
      φ.reductiveImageTorusMap Q T := by
  unfold reductiveImageTorusMap
  rw [← Category.assoc, IntegralTorusData.specialFibreMap_comp_specialFibreInclusion ρ hρ]

/-- A factorization of the integral torus inclusions factors the tori in the
reductive quotient. -/
theorem specialFibreMap_comp_quotientTorusInclusion (T : IntegralTorusData source S i)
    (T' : IntegralTorusData source S' i') (ρ : T.torus ⟶ T'.torus)
    (hρ : CommGroupScheme.groupHom ρ ≫ T'.inclusion = T.inclusion) :
    CommGroupScheme.groupHom (T.specialFibreMap T' ρ) ≫ φ.quotientTorusInclusion Q T' =
      φ.quotientTorusInclusion Q T := by
  unfold quotientTorusInclusion targetTorusInclusion
  rw [← Category.assoc, ← Category.assoc,
    IntegralTorusData.specialFibreMap_comp_specialFibreInclusion ρ hρ]

/-- **Restriction of the root-form sign formula.** Let `ρ : T → T'` be a
homomorphism of split integral tori of the source model compatible with their
inclusions, and let the sign functions on integral characters satisfy
`σ (ρ ≫ ψ) = σ' ψ`. If the roots of `T'_s` in the reductive image are the
quotient roots with `σ' ≥ 0`, then the same holds for `T_s` and `σ`. -/
theorem roots_reductiveImageTorusMap_of_comp [LocallyOfFiniteType Q.quotient.X.hom]
    (T : IntegralTorusData source S i) (T' : IntegralTorusData source S' i')
    (hT : IsSplitTorus T.torus.toGrp) (hT' : IsSplitTorus T'.torus.toGrp)
    (ρ : T.torus ⟶ T'.torus) (hρ : CommGroupScheme.groupHom ρ ≫ T'.inclusion = T.inclusion)
    (σ : characterLattice T.torus → ℝ) (σ' : characterLattice T'.torus → ℝ)
    (hσ : ∀ ψ, σ (ρ ≫ ψ) = σ' ψ)
    (h : roots (φ.reductiveImageTorusMap Q T') =
      {χ | χ ∈ roots (φ.quotientTorusInclusion Q T') ∧
        0 ≤ σ' ((T'.specialCharacterEquiv hT').symm χ)}) :
    roots (φ.reductiveImageTorusMap Q T) =
      {χ | χ ∈ roots (φ.quotientTorusInclusion Q T) ∧
        0 ≤ σ ((T.specialCharacterEquiv hT).symm χ)} := by
  rw [← φ.specialFibreMap_comp_reductiveImageTorusMap Q T T' ρ hρ,
    ← φ.specialFibreMap_comp_quotientTorusInclusion Q T T' ρ hρ]
  refine roots_comp_eq_nonneg_of_roots_eq_nonneg
    (hT'.baseChange (IntegralModel.residueBaseMap R))
    (hT.baseChange (IntegralModel.residueBaseMap R)) _ _ _ _ _ ?_ h
  intro ψ
  obtain ⟨m₀, rfl⟩ := (T'.specialCharacterEquiv hT').surjective ψ
  rw [AddEquiv.symm_apply_apply, ← hσ m₀]
  congr 1
  rw [AddEquiv.symm_apply_eq]
  exact (IntegralTorusData.specialCharacter_comp ρ m₀).symm

variable [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [IsAffineHom G.X.hom]

/-- **The apartment sign formula as a root identity.** By the Lie-image
lemma, the KP facet sign formula says that the roots of the special-fibre
torus in the reductive image are the quotient roots whose generic character
is nonnegative on the displacement vector. -/
theorem hasApartmentLieWeightSignFormula_iff_roots
    (B : Geometry.Building.ValuationBuildingData G) {j : B.S.toGrp ⟶ G}
    (T : IntegralTorusData source B.S j) (hT : IsSplitTorus T.torus.toGrp)
    (Fa Fa' : Set B.Apartment) :
    φ.HasApartmentLieWeightSignFormula B Q T hT Fa Fa' ↔
      ∀ x ∈ Fa, ∀ v : RealTorusSpace.V B.S,
        (Submodule.Quotient.mk v : Geometry.Building.TranslationSpace B.i) +ᵥ x ∈ Fa' →
          roots (φ.reductiveImageTorusMap Q T) =
            {χ | χ ∈ roots (φ.quotientTorusInclusion Q T) ∧
              0 ≤ RealTorusSpace.eval B.S
                (T.genericCharacter ((T.specialCharacterEquiv hT).symm χ)) v} := by
  unfold HasApartmentLieWeightSignFormula
  simp only [nonzeroLieImageWeights_quotientTorusInclusion]
  rfl

end RelativeComponentModelHom

end Langlands.BruhatTits.IntegralModels
