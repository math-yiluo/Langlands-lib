import Langlands.GroupScheme.IntegralModel.SpecialFibreKernelBaseChange
import Langlands.GroupScheme.IntegralModel.UnramifiedModelDescent
import Langlands.GroupScheme.SchematicImageBaseChange
import Langlands.GroupScheme.Rational.ParabolicAmbientTransport
import Langlands.GroupScheme.IntegralModel.SpecialFibreKernelIso
import Langlands.BruhatTits.IntegralModels.UnramifiedSpecialFibreKernel
import Langlands.BruhatTits.IntegralModels.SpecialFibre

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

section IntegratedCompanion

/-! # Actual special-fibre images under model recovery -/



open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000

namespace Langlands.GroupScheme.SchematicImage

variable {k : Type u} [Field k]
    {A B C D : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom A.X.hom] [IsAffineHom B.X.hom]
    [IsAffineHom C.X.hom] [IsAffineHom D.X.hom]
    (f : A ⟶ B) (g : C ⟶ D) (e : A ≅ C) (d : B ≅ D)
    (h : e.hom ≫ g = f ≫ d.hom)

private instance dominant_iso_projection :
    IsSchemeTheoreticallyDominant (e.hom ≫ projection g).hom.hom.left := by
  change IsSchemeTheoreticallyDominant (e.hom.hom.hom.left ≫ (projection g).hom.hom.left)
  infer_instance

omit [IsAffineHom D.X.hom] in
private theorem inclusion_comp_iso_closed : IsClosedSubgroup (inclusion f ≫ d.hom) := by
  change IsClosedImmersion ((inclusion f).hom.hom.left ≫ d.hom.hom.hom.left)
  infer_instance

/-- A commutative isomorphism square identifies the actual schematic images. -/
def isoOfReverseIsoSquare : image f ≅ image g :=
  isoOfDominantFactorizations (projection f) (e.hom ≫ projection g)
    (inclusion f ≫ d.hom) (inclusion g)
    (inclusion_comp_iso_closed f d)
    (inferInstanceAs (IsClosedImmersion (inclusion g).hom.hom.left)) (by
      rw [Category.assoc, projection_inclusion, ← Category.assoc,
        projection_inclusion, h])

@[reassoc]
theorem isoOfReverseIsoSquare_hom_comp :
    (isoOfReverseIsoSquare f g e d h).hom ≫ inclusion g = inclusion f ≫ d.hom :=
  isoOfDominantFactorizations_hom_comp _ _ _ _ _ _ _

include h in
/-- Parabolicity transfers across a commutative isomorphism square. -/
theorem isParabolic_inclusion_of_reverseIsoSquare
    (hg : IsParabolicSubgroup (inclusion g)) :
    IsParabolicSubgroup (inclusion f) := by
  have hp : IsParabolicSubgroup (inclusion f ≫ d.hom) := by
    rw [← isoOfReverseIsoSquare_hom_comp f g e d h]
    exact hg.iso_comp (isoOfReverseIsoSquare f g e d h)
  have hp' := hp.comp_iso d.symm
  simpa only [Category.assoc, Iso.symm_hom, Iso.hom_inv_id, Category.comp_id] using hp'

end Langlands.GroupScheme.SchematicImage

namespace Langlands.GroupScheme.IntegralModel

variable {R K : Type u} [CommRing R] [IsDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] [IsLocalRing R]
    {G H : GroupScheme (Spec (CommRingCat.of K))}
    {M M' : IntegralModel R K G} {N N' : IntegralModel R K H}

private instance image_specialFibre_affine
    {G : GroupScheme (Spec (CommRingCat.of K))} (M : IntegralModel R K G) :
    IsAffineHom M.specialFibre.X.hom := by
  change IsAffineHom (CategoryTheory.Limits.pullback.snd M.group.X.hom (residueBaseMap R))
  infer_instance

/-- Compatible model isomorphisms identify the actual special-fibre images. -/
def Iso.specialFibreImageIso
    (e : M.Iso M' (CategoryTheory.Iso.refl G))
    (d : N.Iso N' (CategoryTheory.Iso.refl H)) {f : G ⟶ H}
    (φ : M.Hom N f) (ψ : M'.Hom N' f) :
    SchematicImage.image φ.specialFibreMap ≅ SchematicImage.image ψ.specialFibreMap :=
  SchematicImage.isoOfReverseIsoSquare φ.specialFibreMap ψ.specialFibreMap
    e.specialFibreIso d.specialFibreIso (by
      change (GroupScheme.baseChange (residueBaseMap R)).map e.iso.hom ≫
          (GroupScheme.baseChange (residueBaseMap R)).map ψ.hom =
        (GroupScheme.baseChange (residueBaseMap R)).map φ.hom ≫
          (GroupScheme.baseChange (residueBaseMap R)).map d.iso.hom
      simpa only [Functor.map_comp] using
        congrArg (GroupScheme.baseChange (residueBaseMap R)).map (e.hom_square d φ ψ))

include R K in
/-- Parabolicity of an actual special-fibre image is invariant under compatible
source and target model identifications. -/
theorem Iso.specialFibreImage_isParabolic
    (e : M.Iso M' (CategoryTheory.Iso.refl G))
    (d : N.Iso N' (CategoryTheory.Iso.refl H)) {f : G ⟶ H}
    (φ : M.Hom N f) (ψ : M'.Hom N' f)
    (hψ : IsParabolicSubgroup (SchematicImage.inclusion ψ.specialFibreMap)) :
    IsParabolicSubgroup (SchematicImage.inclusion φ.specialFibreMap) := by
  apply SchematicImage.isParabolic_inclusion_of_reverseIsoSquare φ.specialFibreMap
    ψ.specialFibreMap e.specialFibreIso d.specialFibreIso _ hψ
  change (GroupScheme.baseChange (residueBaseMap R)).map e.iso.hom ≫
      (GroupScheme.baseChange (residueBaseMap R)).map ψ.hom =
    (GroupScheme.baseChange (residueBaseMap R)).map φ.hom ≫
      (GroupScheme.baseChange (residueBaseMap R)).map d.iso.hom
  simpa only [Functor.map_comp] using
    congrArg (GroupScheme.baseChange (residueBaseMap R)).map (e.hom_square d φ ψ)

end Langlands.GroupScheme.IntegralModel

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
    [Algebra.IsAlgebraic (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField A)]

private instance image_residueBaseChange_affine
    (D : GroupScheme (Spec (CommRingCat.of (IsLocalRing.ResidueField R))))
    [IsAffineHom D.X.hom] :
    IsAffineHom ((GroupScheme.baseChange
      (Spec.algebraMap (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField A))).obj
        D).X.hom := by
  change IsAffineHom (CategoryTheory.Limits.pullback.snd D.X.hom _)
  infer_instance

/-- Parabolicity of the actual image descends along a local coefficient
extension with algebraic residue-field extension. -/
theorem Hom.specialFibreImage_isParabolic_of_baseChange
    (hφ : IsParabolicSubgroup
      (SchematicImage.inclusion (φ.baseChangeCoefficients A L).specialFibreMap)) :
    IsParabolicSubgroup (SchematicImage.inclusion φ.specialFibreMap) := by
  apply SchematicImage.isParabolic_inclusion_of_baseChange
    (L := IsLocalRing.ResidueField A) φ.specialFibreMap
  exact SchematicImage.isParabolic_inclusion_of_reverseIsoSquare _ _
    (M.specialFibreBaseChangeIso A L) (N.specialFibreBaseChangeIso A L)
    (φ.specialFibreBaseChangeIso_naturality A L).symm hφ

end Coefficients

section Unramified

open Langlands.LocalGalois.Separable GaloisPointComparison
open scoped ValuativeRel

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of F))}
    {M N : IntegralModel ↥𝒪[F] F G}

local instance image_unramifiedIntegerAlgebra : Algebra ↥𝒪[F] (fixedFieldIntegers F) :=
  Valuation.HasExtension.instAlgebraInteger
    (vR := ValuativeRel.valuation F) (vA := fixedFieldValuation F)

local instance image_unramifiedIntegerTower :
    IsScalarTower ↥𝒪[F] (fixedFieldIntegers F) (inertiaFixedField F) :=
  Valuation.HasExtension.instIsScalarTowerInteger
    (vR := ValuativeRel.valuation F) (vA := fixedFieldValuation F)

local instance image_unramifiedIntegerLocalHom :
    IsLocalHom (algebraMap ↥𝒪[F] (fixedFieldIntegers F)) :=
  Valuation.HasExtension.instIsLocalHomValuationInteger
    (vR := ValuativeRel.valuation F) (vS := fixedFieldValuation F)

private theorem image_unramifiedResidueAlgebra_eq :
    (inferInstance : Algebra (IsLocalRing.ResidueField ↥𝒪[F])
      (IsLocalRing.ResidueField (fixedFieldIntegers F))) =
        (residueToFixedField F).toAlgebra := by
  apply Algebra.algebra_ext
  intro x
  obtain ⟨y, rfl⟩ := IsLocalRing.residue_surjective x
  rfl

private theorem image_unramifiedResidue_isAlgebraic :
    Algebra.IsAlgebraic (IsLocalRing.ResidueField ↥𝒪[F])
      (IsLocalRing.ResidueField (fixedFieldIntegers F)) := by
  have h := (fixedFieldResidueIsAlgClosure F).isAlgebraic
  convert h
  exact image_unramifiedResidueAlgebra_eq

/-- Parabolicity of the actual image descends from any two characterized smooth
unramified models and any extension of the same generic identity map. -/
theorem Hom.specialFibreImage_isParabolic_of_unramifiedModels
    (φ : M.Hom N (𝟙 G))
    (Q P : IntegralModel (fixedFieldIntegers F) (inertiaFixedField F)
      (baseChanged F (inertiaFixedField F) G))
    (hM : M.IsSmooth) (hN : N.IsSmooth) (hQ : Q.IsSmooth) (hP : P.IsSmooth)
    (hsource : M.baseChangeUnramified.integralPoints = Q.integralPoints)
    (htarget : N.baseChangeUnramified.integralPoints = P.integralPoints)
    (ψ : Q.Hom P (𝟙 _))
    (hψ : IsParabolicSubgroup (SchematicImage.inclusion ψ.specialFibreMap)) :
    IsParabolicSubgroup (SchematicImage.inclusion φ.specialFibreMap) := by
  have h := Iso.specialFibreImage_isParabolic
    (M.unramifiedIsoOfIntegralPointsEq Q hM hQ hsource)
    (N.unramifiedIsoOfIntegralPointsEq P hN hP htarget)
    φ.baseChangeUnramifiedId ψ hψ
  have := image_unramifiedResidue_isAlgebraic (F := F)
  exact φ.specialFibreImage_isParabolic_of_baseChange
    (fixedFieldIntegers F) (inertiaFixedField F) h

end Unramified

end Langlands.GroupScheme.IntegralModel

namespace Langlands.BruhatTits.IntegralModels.RelativeComponentModelHom

open Langlands.GroupScheme Langlands.GroupScheme.GaloisPointComparison
open Langlands.LocalGalois.Separable
open scoped ValuativeRel

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of F))}
    {source target : RelativeComponentModelData ↥𝒪[F] F G}

/-- The actual neutral comparison image is parabolic if it is so on smooth
unramified models with the same two integral-point subgroups. -/
theorem hasParabolicSpecialFibreImage_of_unramifiedModels
    (φ : RelativeComponentModelHom source target)
    (Q P : IntegralModel (fixedFieldIntegers F) (inertiaFixedField F)
      (baseChanged F (inertiaFixedField F) G))
    (hQ : Q.IsSmooth) (hP : P.IsSmooth)
    (hsource : source.neutral.baseChangeUnramified.integralPoints = Q.integralPoints)
    (htarget : target.neutral.baseChangeUnramified.integralPoints = P.integralPoints)
    (ψ : Q.Hom P (𝟙 _))
    (hψ : IsParabolicSubgroup (SchematicImage.inclusion ψ.specialFibreMap)) :
    φ.HasParabolicSpecialFibreImage :=
  φ.neutral.specialFibreImage_isParabolic_of_unramifiedModels Q P
    source.neutral_smooth target.neutral_smooth hQ hP hsource htarget ψ hψ

end Langlands.BruhatTits.IntegralModels.RelativeComponentModelHom

end IntegratedCompanion
