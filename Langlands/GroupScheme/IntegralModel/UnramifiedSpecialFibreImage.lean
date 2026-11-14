import Langlands.GroupScheme.IntegralModel.SpecialFibreKernelBaseChange
import Langlands.GroupScheme.IntegralModel.UnramifiedModelDescent
import Langlands.GroupScheme.SchematicImageBaseChange
import Langlands.GroupScheme.Rational.ParabolicAmbientTransport

/-! # Actual special-fibre images under maximal-unramified extension -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped ValuativeRel CategoryTheory.MonObj

namespace Langlands.GroupScheme.SchematicImage

variable {k : Type u} [Field k]
    {A A' H H' : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom A.X.hom] [IsAffineHom A'.X.hom]
    [IsAffineHom H.X.hom] [IsAffineHom H'.X.hom]
    (f : A ⟶ H) (f' : A' ⟶ H') (e : A ≅ A') (d : H ≅ H')
    (h : f ≫ d.hom = e.hom ≫ f')

private instance affine_space (B : GroupScheme (Spec (CommRingCat.of k)))
    [IsAffineHom B.X.hom] : IsAffine B.X.left :=
  isAffine_of_isAffineHom B.X.hom

private instance iso_projection_dominant :
    IsSchemeTheoreticallyDominant (e.hom ≫ projection f').hom.hom.left := by
  change IsSchemeTheoreticallyDominant
    (e.hom.hom.hom.left ≫ (projection f').hom.hom.left)
  infer_instance

include h in
private theorem isoSquare_factorization :
    projection f ≫ (inclusion f ≫ d.hom) =
      (e.hom ≫ projection f') ≫ inclusion f' := by
  rw [← Category.assoc, projection_inclusion, Category.assoc, projection_inclusion]
  exact h

include h in
/-- An isomorphic square identifies the two actual images in the new target. -/
theorem range_inclusion_isoSquare :
    SubgroupFunctor.range (inclusion f ≫ d.hom) =
      SubgroupFunctor.range (inclusion f') :=
  range_eq_of_dominantFactorizations
    (projection f) (e.hom ≫ projection f')
    (inclusion f ≫ d.hom) (inclusion f')
    (IsClosedSubgroup.comp_iso
      (inferInstanceAs (IsClosedImmersion (inclusion f).hom.hom.left)) d)
    (inferInstanceAs (IsClosedImmersion (inclusion f').hom.hom.left))
    (isoSquare_factorization f f' e d h)

/-- The canonical image isomorphism induced by an actual isomorphic square. -/
def isoOfIsoSquare : image f ≅ image f' :=
  isoOfDominantFactorizations
    (projection f) (e.hom ≫ projection f')
    (inclusion f ≫ d.hom) (inclusion f')
    (IsClosedSubgroup.comp_iso
      (inferInstanceAs (IsClosedImmersion (inclusion f).hom.hom.left)) d)
    (inferInstanceAs (IsClosedImmersion (inclusion f').hom.hom.left))
    (isoSquare_factorization f f' e d h)

@[reassoc]
theorem isoOfIsoSquare_hom_comp :
    (isoOfIsoSquare f f' e d h).hom ≫ inclusion f' = inclusion f ≫ d.hom :=
  isoOfDominantFactorizations_hom_comp _ _ _ _ _ _ _

include h in
/-- Parabolicity of the actual schematic image is unchanged by such a square. -/
theorem isParabolic_inclusion_of_isoSquare
    (hp : IsParabolicSubgroup (inclusion f)) :
    IsParabolicSubgroup (inclusion f') := by
  have hq := (hp.comp_iso d).iso_comp (isoOfIsoSquare f f' e d h).symm
  have he : (isoOfIsoSquare f f' e d h).inv ≫ (inclusion f ≫ d.hom) =
      inclusion f' := by
    rw [← isoOfIsoSquare_hom_comp f f' e d h, Iso.inv_hom_id_assoc]
  change IsParabolicSubgroup
    ((isoOfIsoSquare f f' e d h).inv ≫ (inclusion f ≫ d.hom)) at hq
  rwa [he] at hq

end Langlands.GroupScheme.SchematicImage

namespace Langlands.GroupScheme.IntegralModel

section Coefficients

variable {R K : Type u} [CommRing R] [IsDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] [IsLocalRing R]
    {G H : GroupScheme (Spec (CommRingCat.of K))}
    {M : IntegralModel R K G} {N : IntegralModel R K H} {f : G ⟶ H}
    (φ : M.Hom N f)
    (A L : Type u) [CommRing A] [IsDomain A] [Field L]
    [Algebra R A] [Algebra A L] [IsFractionRing A L]
    [Algebra K L] [Algebra R L] [IsScalarTower R A L] [IsScalarTower R K L]
    [IsLocalRing A] [IsLocalHom (algebraMap R A)]

private instance fibre_affine (Z : IntegralModel R K G) :
    IsAffineHom Z.specialFibre.X.hom :=
  MorphismProperty.pullback_snd _ _ (inferInstanceAs (IsAffineHom Z.group.X.hom))

/-- The actual special-fibre image commutes with a local coefficient extension. -/
def Hom.specialFibreImageBaseChangeIso :
    (GroupScheme.baseChange
      (Spec.algebraMap (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField A))).obj
        (SchematicImage.image φ.specialFibreMap) ≅
      SchematicImage.image (φ.baseChangeCoefficients A L).specialFibreMap :=
  SchematicImage.baseChangeIso φ.specialFibreMap _ ≪≫
    SchematicImage.isoOfIsoSquare _ _
      (M.specialFibreBaseChangeIso A L) (N.specialFibreBaseChangeIso A L)
      (φ.specialFibreBaseChangeIso_naturality A L)

/-- The image comparison preserves the specified ambient inclusions. -/
theorem Hom.specialFibreImageBaseChangeIso_hom_comp :
    (φ.specialFibreImageBaseChangeIso A L).hom ≫
        SchematicImage.inclusion (φ.baseChangeCoefficients A L).specialFibreMap =
      (GroupScheme.baseChange
        (Spec.algebraMap (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField A))).map
          (SchematicImage.inclusion φ.specialFibreMap) ≫
        (N.specialFibreBaseChangeIso A L).hom := by
  dsimp only [Hom.specialFibreImageBaseChangeIso, Iso.trans_hom]
  rw [Category.assoc, SchematicImage.isoOfIsoSquare_hom_comp,
    ← Category.assoc, SchematicImage.baseChangeIso_hom_comp]

/-- Parabolicity of an actual special-fibre image reflects along a local
coefficient extension with algebraic residue-field extension. -/
theorem Hom.isParabolic_specialFibreImage_of_baseChange
    [Algebra.IsAlgebraic (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField A)]
    (hp : IsParabolicSubgroup
      (SchematicImage.inclusion (φ.baseChangeCoefficients A L).specialFibreMap)) :
    IsParabolicSubgroup (SchematicImage.inclusion φ.specialFibreMap) := by
  apply SchematicImage.isParabolic_inclusion_of_baseChange
    (L := IsLocalRing.ResidueField A) φ.specialFibreMap
  have hnat : (φ.baseChangeCoefficients A L).specialFibreMap ≫
      (N.specialFibreBaseChangeIso A L).inv =
        (M.specialFibreBaseChangeIso A L).inv ≫
          (GroupScheme.baseChange
            (Spec.algebraMap (IsLocalRing.ResidueField R)
              (IsLocalRing.ResidueField A))).map φ.specialFibreMap := by
    apply (cancel_mono (N.specialFibreBaseChangeIso A L).hom).mp
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [φ.specialFibreBaseChangeIso_naturality A L, Iso.inv_hom_id_assoc]
  exact SchematicImage.isParabolic_inclusion_of_isoSquare
    (φ.baseChangeCoefficients A L).specialFibreMap _
    (M.specialFibreBaseChangeIso A L).symm (N.specialFibreBaseChangeIso A L).symm
    hnat hp

end Coefficients

open Langlands.LocalGalois.Separable GaloisPointComparison

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    {G H : GroupScheme (Spec (CommRingCat.of F))}
    {M : IntegralModel ↥𝒪[F] F G} {N : IntegralModel ↥𝒪[F] F H}
    {f : G ⟶ H} (φ : M.Hom N f)

local instance unramifiedImage_integerAlgebra : Algebra ↥𝒪[F] (fixedFieldIntegers F) :=
  Valuation.HasExtension.instAlgebraInteger
    (vR := ValuativeRel.valuation F) (vA := fixedFieldValuation F)

local instance unramifiedImage_integerTower :
    IsScalarTower ↥𝒪[F] (fixedFieldIntegers F) (inertiaFixedField F) :=
  Valuation.HasExtension.instIsScalarTowerInteger
    (vR := ValuativeRel.valuation F) (vA := fixedFieldValuation F)

local instance unramifiedImage_integerLocal :
    IsLocalHom (algebraMap ↥𝒪[F] (fixedFieldIntegers F)) :=
  Valuation.HasExtension.instIsLocalHomValuationInteger
    (vR := ValuativeRel.valuation F) (vS := fixedFieldValuation F)

/-- The actual upstairs image is the residue extension of the original image. -/
def Hom.unramifiedSpecialFibreImageIso :
    SchematicImage.image
        (φ.baseChangeCoefficients (fixedFieldIntegers F) (inertiaFixedField F)).specialFibreMap ≅
      (GroupScheme.baseChange (Spec.algebraMap 𝓀[F]
        (IsLocalRing.ResidueField (fixedFieldIntegers F)))).obj
          (SchematicImage.image φ.specialFibreMap) :=
  (φ.specialFibreImageBaseChangeIso (fixedFieldIntegers F) (inertiaFixedField F)).symm

/-- Parabolicity of the actual upstairs image descends to the original image. -/
theorem Hom.isParabolic_specialFibreImage_of_unramified
    (hp : IsParabolicSubgroup (SchematicImage.inclusion
      (φ.baseChangeCoefficients (fixedFieldIntegers F) (inertiaFixedField F)).specialFibreMap)) :
    IsParabolicSubgroup (SchematicImage.inclusion φ.specialFibreMap) := by
  let : Algebra.IsAlgebraic 𝓀[F]
      (IsLocalRing.ResidueField (fixedFieldIntegers F)) :=
    by
      have hAlg : (inferInstance :
          Algebra 𝓀[F] (IsLocalRing.ResidueField (fixedFieldIntegers F))) =
          (residueToFixedField F).toAlgebra := by
        apply Algebra.algebra_ext
        intro x
        obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective x
        rfl
      exact (congrArg (fun a : Algebra 𝓀[F]
          (IsLocalRing.ResidueField (fixedFieldIntegers F)) =>
          @Algebra.IsAlgebraic _ _ _ _ a) hAlg).mpr
        (fixedFieldResidueIsAlgClosure F).isAlgebraic
  exact φ.isParabolic_specialFibreImage_of_baseChange
    (fixedFieldIntegers F) (inertiaFixedField F) hp

end Langlands.GroupScheme.IntegralModel
