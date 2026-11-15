import Langlands.GroupScheme.IntegralModel.UnramifiedSpecialFibreImage
import Langlands.GroupScheme.IntegralModel.UnramifiedReductionPoints
import Langlands.BruhatTits.IntegralModels.ReductionPreimage

/-! # Exact actual-image reduction preimages descend from unramified models -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 200000

namespace Langlands.GroupScheme.SchematicImage

variable {k l : Type u} [Field k] [Field l]
    {A B C D : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom A.X.hom] [IsAffineHom B.X.hom]
    [IsAffineHom C.X.hom] [IsAffineHom D.X.hom]

/-- The original rational points in the actual schematic image of a map. -/
irreducible_def rationalImage (f : A ⟶ B) : Subgroup (rationalPoints B) :=
  (rationalPoints.map (inclusion f)).range

/-- Membership in the actual rational-image subgroup retains its image point. -/
theorem mem_rationalImage (f : A ⟶ B) (x : rationalPoints B) :
    x ∈ rationalImage f ↔
      ∃ y : rationalPoints (image f), rationalPoints.map (inclusion f) y = x := by
  rw [rationalImage_def]
  rfl

/-- The image of every source point lies in the actual rational image. -/
theorem map_mem_rationalImage (f : A ⟶ B) (x : rationalPoints A) :
    rationalPoints.map f x ∈ rationalImage f := by
  apply (mem_rationalImage f _).mpr
  refine ⟨rationalPoints.map (projection f) x, ?_⟩
  change (x ≫ (projection f).hom.hom) ≫ (inclusion f).hom.hom = _
  rw [Category.assoc, ← Grp.comp_hom_hom, projection_inclusion]
  rfl

/-- An image point transports through an actual commutative isomorphism square. -/
theorem map_mem_rationalImage_of_isoSquare
    (f : A ⟶ B) (g : C ⟶ D) (e : A ≅ C) (d : B ≅ D)
    (h : e.hom ≫ g = f ≫ d.hom) {x : rationalPoints B}
    (hx : x ∈ rationalImage f) :
    rationalPoints.map d.hom x ∈ rationalImage g := by
  obtain ⟨y, rfl⟩ := (mem_rationalImage f x).mp hx
  apply (mem_rationalImage g _).mpr
  refine ⟨rationalPoints.map (isoOfReverseIsoSquare f g e d h).hom y, ?_⟩
  change (y ≫ (isoOfReverseIsoSquare f g e d h).hom.hom.hom) ≫
      (inclusion g).hom.hom = (y ≫ (inclusion f).hom.hom) ≫ d.hom.hom.hom
  rw [Category.assoc, ← Grp.comp_hom_hom, isoOfReverseIsoSquare_hom_comp]
  rfl

omit [IsAffineHom C.X.hom] [IsAffineHom D.X.hom] in
/-- Extending a point of the original image gives a point of the actual
extended image, without lifting it through the original source projection. -/
theorem baseChangeSectionHom_mem_rationalImage
    (f : A ⟶ B) (b : Spec (CommRingCat.of l) ⟶ Spec (CommRingCat.of k)) [Flat b]
    {x : rationalPoints B} (hx : x ∈ rationalImage f) :
    baseChangeSectionHom b B x ∈
      rationalImage ((GroupScheme.baseChange b).map f) := by
  obtain ⟨y, rfl⟩ := (mem_rationalImage f x).mp hx
  apply (mem_rationalImage _ _).mpr
  refine ⟨rationalPoints.map (baseChangeIso f b).hom
    (baseChangeSectionHom b (image f) y), ?_⟩
  change (baseChangeSectionHom b (image f) y ≫ (baseChangeIso f b).hom.hom.hom) ≫
    (inclusion ((GroupScheme.baseChange b).map f)).hom.hom = _
  rw [Category.assoc, ← Grp.comp_hom_hom, baseChangeIso_hom_comp]
  exact (baseChangeSectionHom_naturality b (inclusion f) y).symm

end Langlands.GroupScheme.SchematicImage

namespace Langlands.GroupScheme.IntegralModel

section Original

variable {R K : Type u} [CommRing R] [IsDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] [IsLocalRing R]
    {G H : GroupScheme (Spec (CommRingCat.of K))}
    {M M' : IntegralModel R K G} {N N' : IntegralModel R K H}
    {f : G ⟶ H}

private instance preimage_specialFibre_affine
    {G : GroupScheme (Spec (CommRingCat.of K))} (M : IntegralModel R K G) :
    IsAffineHom M.specialFibre.X.hom := by
  change IsAffineHom (CategoryTheory.Limits.pullback.snd M.group.X.hom (residueBaseMap R))
  infer_instance

/-- The original integral sections reducing into all rational points of the
actual schematic image of the special-fibre map. -/
def Hom.imageReductionPreimage (φ : M.Hom N f) : Subgroup N.integralSections :=
  (SchematicImage.rationalImage φ.specialFibreMap).comap
    N.reduction

/-- Every source section maps into the exact actual-image reduction preimage. -/
theorem Hom.sectionRange_le_imageReductionPreimage (φ : M.Hom N f) :
    (rationalPoints.map φ.hom).range ≤ φ.imageReductionPreimage := by
  rintro _ ⟨x, rfl⟩
  change N.reduction (rationalPoints.map φ.hom x) ∈
    SchematicImage.rationalImage φ.specialFibreMap
  rw [φ.reduction_naturality]
  exact SchematicImage.map_mem_rationalImage φ.specialFibreMap (M.reduction x)

omit [IsLocalRing R] in
/-- An identity-generic model map preserves the original generic evaluation. -/
theorem Hom.integralPointMap_identity {N : IntegralModel R K G}
    (φ : M.Hom N (𝟙 G)) (x : M.integralSections) :
    N.integralPointMap (rationalPoints.map φ.hom x) = M.integralPointMap x := by
  simpa only [rationalPoints.map_apply, Grp.id_hom_hom, Category.comp_id] using
    φ.integralPointMap_naturality x

/-- Exact actual-image reduction preimages transfer across compatible model
isomorphisms, independently of smoothness or residue rational surjectivity. -/
theorem Iso.imageReductionPreimage_eq_range
    (e : M.Iso M' (CategoryTheory.Iso.refl G))
    (d : N.Iso N' (CategoryTheory.Iso.refl H))
    (φ : M.Hom N f) (ψ : M'.Hom N' f)
    (hψ : ψ.imageReductionPreimage = (rationalPoints.map ψ.hom).range) :
    φ.imageReductionPreimage = (rationalPoints.map φ.hom).range := by
  apply le_antisymm _ φ.sectionRange_le_imageReductionPreimage
  intro x hx
  have hx' : d.integralSectionsEquiv x ∈ ψ.imageReductionPreimage := by
    have h := SchematicImage.map_mem_rationalImage_of_isoSquare
      φ.specialFibreMap ψ.specialFibreMap e.specialFibreIso d.specialFibreIso
      (by
        change (GroupScheme.baseChange (residueBaseMap R)).map e.iso.hom ≫
            (GroupScheme.baseChange (residueBaseMap R)).map ψ.hom =
          (GroupScheme.baseChange (residueBaseMap R)).map φ.hom ≫
            (GroupScheme.baseChange (residueBaseMap R)).map d.iso.hom
        simpa only [Functor.map_comp] using
          congrArg (GroupScheme.baseChange (residueBaseMap R)).map (e.hom_square d φ ψ)) hx
    change N'.reduction (d.integralSectionsEquiv x) ∈
      SchematicImage.rationalImage ψ.specialFibreMap
    change N'.reduction (rationalPoints.map d.toHom.hom x) ∈
      SchematicImage.rationalImage ψ.specialFibreMap
    rw [d.toHom.reduction_naturality]
    exact h
  obtain ⟨y, hy⟩ := hψ.le hx'
  refine ⟨e.integralSectionsEquiv.symm y, ?_⟩
  apply d.integralSectionsEquiv.injective
  have hs (z : M.integralSections) :
      rationalPoints.map ψ.hom (e.integralSectionsEquiv z) =
        d.integralSectionsEquiv (rationalPoints.map φ.hom z) := by
    change (z ≫ e.iso.hom.hom.hom) ≫ ψ.hom.hom.hom =
      (z ≫ φ.hom.hom.hom) ≫ d.iso.hom.hom.hom
    rw [Category.assoc, ← Grp.comp_hom_hom, e.hom_square d φ ψ]
    rfl
  rw [← hs, MulEquiv.apply_symm_apply]
  exact hy

end Original

end Langlands.GroupScheme.IntegralModel

namespace Langlands.GroupScheme.SchematicImage

private instance preimage_baseChange_affine {S T : Scheme.{u}}
    (b : T ⟶ S) (D : GroupScheme S) [IsAffineHom D.X.hom] :
    IsAffineHom ((GroupScheme.baseChange b).obj D).X.hom := by
  change IsAffineHom (CategoryTheory.Limits.pullback.snd D.X.hom b)
  exact MorphismProperty.pullback_snd _ _ ‹IsAffineHom D.X.hom›

/-- Actual-image membership of an original section transports through any
commuting coefficient square whose two final bases are fields. -/
theorem square_mem_rationalImage
    {S U : Scheme.{u}} {k l : Type u} [Field k] [Field l]
    (b : Spec (CommRingCat.of k) ⟶ S)
    (c : Spec (CommRingCat.of l) ⟶ Spec (CommRingCat.of k)) [Flat c]
    (d : U ⟶ S) (e : Spec (CommRingCat.of l) ⟶ U)
    (h : c ≫ b = e ≫ d)
    {B C : GroupScheme S} [IsAffineHom B.X.hom] [IsAffineHom C.X.hom]
    (f : B ⟶ C) (x : Over.mk (𝟙 S) ⟶ C.X)
    (hx : baseChangeSectionHom b C x ∈
      rationalImage ((GroupScheme.baseChange b).map f)) :
    baseChangeSectionHom e ((GroupScheme.baseChange d).obj C)
        (baseChangeSectionHom d C x) ∈
      rationalImage ((GroupScheme.baseChange e).map
        ((GroupScheme.baseChange d).map f)) := by
  have hx' := baseChangeSectionHom_mem_rationalImage
    ((GroupScheme.baseChange b).map f) c hx
  have hx'' := map_mem_rationalImage_of_isoSquare
    ((GroupScheme.baseChange c).map ((GroupScheme.baseChange b).map f))
    ((GroupScheme.baseChange e).map ((GroupScheme.baseChange d).map f))
    (Descent.squareComparison b c d e h B)
    (Descent.squareComparison b c d e h C)
    (Descent.squareComparison_naturality b c d e h f).symm hx'
  change baseChangeSectionHom c ((GroupScheme.baseChange b).obj C)
      (baseChangeSectionHom b C x) ≫
        (Descent.squareComparison b c d e h C).hom.hom.hom ∈
      rationalImage ((GroupScheme.baseChange e).map
        ((GroupScheme.baseChange d).map f)) at hx''
  rw [Descent.squareComparison_section] at hx''
  exact hx''

end Langlands.GroupScheme.SchematicImage

namespace Langlands.GroupScheme.SchematicImage

section CoefficientSections

open IntegralModel

variable {R A : Type u} [CommRing R] [CommRing A]
    [IsLocalRing R] [IsLocalRing A] [Algebra R A]
    [IsLocalHom (algebraMap R A)]
    {B C : GroupScheme (Spec (CommRingCat.of R))}
    [IsAffineHom B.X.hom] [IsAffineHom C.X.hom]

/-- The residue square carries an actual image point into the actual image
after local coefficient extension. -/
theorem residueSquare_mem_rationalImage
    (f : B ⟶ C) {x : rationalPoints C}
    (hx : baseChangeSectionHom (residueBaseMap R) C x ∈
      rationalImage ((GroupScheme.baseChange (residueBaseMap R)).map f)) :
    baseChangeSectionHom (residueBaseMap A)
        ((GroupScheme.baseChange (Spec.algebraMap R A)).obj C)
        (baseChangeSectionHom (Spec.algebraMap R A) C x) ∈
      rationalImage ((GroupScheme.baseChange (residueBaseMap A)).map
        ((GroupScheme.baseChange (Spec.algebraMap R A)).map f)) := by
  let b := Spec.algebraMap (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField A)
  have : Flat b := (fieldExtension_fpqc (IsLocalRing.ResidueField R)
    (IsLocalRing.ResidueField A)).2.1
  exact square_mem_rationalImage (residueBaseMap R) b
    (Spec.algebraMap R A) (residueBaseMap A)
    (residueCoefficientSquare (R := R) A) f x hx

end CoefficientSections

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

/-- An original section in the actual-image reduction preimage extends to a
section in the actual-image reduction preimage of the coefficient-extended map. -/
theorem Hom.baseChangeSection_mem_imageReductionPreimage
    {x : N.integralSections} (hx : x ∈ φ.imageReductionPreimage) :
    baseChangeSectionHom (Spec.algebraMap R A) N.group x ∈
      (φ.baseChangeCoefficients A L).imageReductionPreimage := by
  exact SchematicImage.residueSquare_mem_rationalImage (A := A) φ.hom hx

end Coefficients

section Unramified

open Langlands.LocalGalois.Separable GaloisPointComparison
open scoped ValuativeRel

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of F))}
    {M N : IntegralModel ↥𝒪[F] F G}

local instance preimage_unramifiedIntegerAlgebra :
    Algebra ↥𝒪[F] (fixedFieldIntegers F) :=
  Valuation.HasExtension.instAlgebraInteger
    (vR := ValuativeRel.valuation F) (vA := fixedFieldValuation F)

local instance preimage_unramifiedIntegerTower :
    IsScalarTower ↥𝒪[F] (fixedFieldIntegers F) (inertiaFixedField F) :=
  Valuation.HasExtension.instIsScalarTowerInteger
    (vR := ValuativeRel.valuation F) (vA := fixedFieldValuation F)

local instance preimage_unramifiedIntegerLocalHom :
    IsLocalHom (algebraMap ↥𝒪[F] (fixedFieldIntegers F)) :=
  Valuation.HasExtension.instIsLocalHomValuationInteger
    (vR := ValuativeRel.valuation F) (vS := fixedFieldValuation F)

/-- Exact image-preimage equality descends from the actual unramified coefficient
extension using exact descent of generic integrality. -/
theorem Hom.imageReductionPreimage_eq_range_of_unramified
    (φ : M.Hom N (𝟙 G))
    (hφ : φ.baseChangeUnramifiedId.imageReductionPreimage =
      (rationalPoints.map φ.baseChangeUnramifiedId.hom).range) :
    φ.imageReductionPreimage = (rationalPoints.map φ.hom).range := by
  apply le_antisymm _ φ.sectionRange_le_imageReductionPreimage
  intro x hx
  let x' := baseChangeSectionHom
    (Spec.algebraMap ↥𝒪[F] (fixedFieldIntegers F)) N.group x
  have hx' : x' ∈ φ.baseChangeUnramifiedId.imageReductionPreimage :=
    φ.baseChangeSection_mem_imageReductionPreimage
      (fixedFieldIntegers F) (inertiaFixedField F) hx
  obtain ⟨y, hy⟩ := hφ.le hx'
  have hgeneric : M.baseChangeUnramified.integralPointMap y =
      rationalExtend F (inertiaFixedField F) G (N.integralPointMap x) := by
    calc
      M.baseChangeUnramified.integralPointMap y =
          N.baseChangeUnramified.integralPointMap
            (rationalPoints.map φ.baseChangeUnramifiedId.hom y) := by
        exact (φ.baseChangeUnramifiedId.integralPointMap_identity y).symm
      _ = N.baseChangeUnramified.integralPointMap x' :=
        congrArg N.baseChangeUnramified.integralPointMap hy
      _ = _ := N.baseChangeUnramified_integralPointMap x
  have hint : rationalExtend F (inertiaFixedField F) G (N.integralPointMap x) ∈
      M.baseChangeUnramified.integralPoints := ⟨y, hgeneric⟩
  obtain ⟨z, hz⟩ :=
    (M.mem_integralPoints_rationalExtend_iff_unramified (N.integralPointMap x)).mp hint
  refine ⟨z, N.integralPointMap_injective ?_⟩
  exact (φ.integralPointMap_identity z).trans hz

/-- Any two characterized smooth unramified models may supply the exact
actual-image reduction-preimage equality of an original identity-generic map. -/
theorem Hom.imageReductionPreimage_eq_range_of_unramifiedModels
    (φ : M.Hom N (𝟙 G))
    (Q P : IntegralModel (fixedFieldIntegers F) (inertiaFixedField F)
      (baseChanged F (inertiaFixedField F) G))
    (hM : M.IsSmooth) (hN : N.IsSmooth) (hQ : Q.IsSmooth) (hP : P.IsSmooth)
    (hsource : M.baseChangeUnramified.integralPoints = Q.integralPoints)
    (htarget : N.baseChangeUnramified.integralPoints = P.integralPoints)
    (ψ : Q.Hom P (𝟙 _))
    (hψ : ψ.imageReductionPreimage = (rationalPoints.map ψ.hom).range) :
    φ.imageReductionPreimage = (rationalPoints.map φ.hom).range := by
  apply φ.imageReductionPreimage_eq_range_of_unramified
  exact Iso.imageReductionPreimage_eq_range
    (M.unramifiedIsoOfIntegralPointsEq Q hM hQ hsource)
    (N.unramifiedIsoOfIntegralPointsEq P hN hP htarget)
    φ.baseChangeUnramifiedId ψ hψ

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

/-- The exact KP neutral reduction-preimage clause descends from smooth
unramified models characterized by the two actual integral-point images. -/
theorem hasParabolicReductionPreimage_of_unramifiedModels
    (φ : RelativeComponentModelHom source target)
    (Q P : IntegralModel (fixedFieldIntegers F) (inertiaFixedField F)
      (baseChanged F (inertiaFixedField F) G))
    (hQ : Q.IsSmooth) (hP : P.IsSmooth)
    (hsource : source.neutral.baseChangeUnramified.integralPoints = Q.integralPoints)
    (htarget : target.neutral.baseChangeUnramified.integralPoints = P.integralPoints)
    (ψ : Q.Hom P (𝟙 _))
    (hψ : ψ.imageReductionPreimage = (rationalPoints.map ψ.hom).range) :
    φ.HasParabolicReductionPreimage := by
  have h := φ.neutral.imageReductionPreimage_eq_range_of_unramifiedModels Q P
    source.neutral_smooth target.neutral_smooth hQ hP hsource htarget ψ hψ
  rw [IntegralModel.Hom.imageReductionPreimage, SchematicImage.rationalImage_def] at h
  unfold HasParabolicReductionPreimage specialFibreImagePoints
  exact h

end Langlands.BruhatTits.IntegralModels.RelativeComponentModelHom
