import Langlands.BruhatTits.IntegralModels.GeneralLinearIwahoriImage
import Langlands.BruhatTits.IntegralModels.GeneralLinearDepthZero
import Langlands.GroupScheme.IntegralModel.SpecialFibreKernelIso
import Langlands.GroupScheme.IntegralModel.UnramifiedImagePreimage
import Langlands.GroupScheme.IntegralModel.SemilinearCoefficientDescent
import Langlands.GroupScheme.Dynamic.GeneralLinearBaseChange
import Langlands.AbelianScheme.KernelBaseChange
import Langlands.GroupScheme.IntegralModel.HenselianReduction
import Langlands.BruhatTits.IntegralModels.GeneralLinearIwahoriQuotient
import Langlands.BruhatTits.IntegralModels.GeneralLinearIwahoriComparison
import Langlands.GroupScheme.IntegralModel.SmoothIntersection

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-! # The Iwahori model of `GL_N` over the standard hyperspecial model -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct ValuativeRel CategoryTheory.MonObj

namespace Langlands.GroupScheme.IntegralModel

variable {R K : Type u} [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
  {G : GroupScheme (Spec (CommRingCat.of K))}

/-- The identity isomorphism of an integral model, over the identity of the generic group. -/
def reflIso (M : IntegralModel R K G) : M.Iso M (CategoryTheory.Iso.refl G) where
  iso := CategoryTheory.Iso.refl M.group
  generic_comm := by
    rw [CategoryTheory.Iso.refl_hom, CategoryTheory.Iso.refl_hom, CategoryTheory.Functor.map_id,
      Category.id_comp, Category.comp_id]

end Langlands.GroupScheme.IntegralModel

namespace Langlands.BruhatTits.IntegralModels.RelativeComponentModelHom

open GroupScheme

variable {R K : Type u} [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
  [IsLocalRing R] {G : GroupScheme (Spec (CommRingCat.of K))}
  {source target : RelativeComponentModelData R K G}

/-- The reduction-preimage clause of KP Axiom 4.1.22(4) is the exact actual-image reduction
preimage statement for the neutral model morphism. -/
theorem hasParabolicReductionPreimage_iff_imageReductionPreimage
    (φ : RelativeComponentModelHom source target) :
    φ.HasParabolicReductionPreimage ↔
      φ.neutral.imageReductionPreimage = (rationalPoints.map φ.neutral.hom).range := by
  unfold HasParabolicReductionPreimage specialFibreImagePoints
  rw [IntegralModel.Hom.imageReductionPreimage, SchematicImage.rationalImage_def]

end Langlands.BruhatTits.IntegralModels.RelativeComponentModelHom

namespace Langlands.BruhatTits.IntegralModels

open GroupScheme GroupScheme.FiniteFreeAlgebraUnits

variable (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] (N : ℕ)

/-- On tensors, the matrix of `s ⊗ M` read over `𝒪[F]` agrees with the matrix of its image
under base change to `F` and the order identification. -/
theorem matrixEquivTensor_symm_orderEquiv (S : Type u) [CommRing S] [Algebra 𝒪[F] S]
    [Algebra F S] [IsScalarTower 𝒪[F] F S]
    (w : S ⊗[𝒪[F]] Matrix (Fin N) (Fin N) 𝒪[F]) :
    (matrixEquivTensor (Fin N) 𝒪[F] S).symm w =
      (matrixEquivTensor (Fin N) F S).symm
        (Algebra.TensorProduct.congr (AlgEquiv.refl : S ≃ₐ[F] S)
          (orderEquiv 𝒪[F] F N (matrixInclusion F N) (matrixInclusion_injective F N)
            (matrixInclusion_spans F N))
          (baseChangeTensorEquiv (R := CommRingCat.of 𝒪[F]) (Matrix (Fin N) (Fin N) 𝒪[F])
            (CommRingCat.of F) S w)) := by
  induction w using TensorProduct.inductionOn with
  | tmul s M =>
      rw [baseChangeTensorEquiv_tmul, Algebra.TensorProduct.congr_apply,
        Algebra.TensorProduct.map_tmul]
      erw [orderEquiv_tmul]
      rw [one_smul]
      ext i j
      simp [matrixEquivTensor_apply_symm, Matrix.map_apply, Matrix.smul_apply,
        IsScalarTower.algebraMap_apply 𝒪[F] F S]
  | add w w' hw hw' => simp only [map_add, hw, hw']

/-- **The hyperspecial order model is the standard model.** The unit group scheme of
`M_N(𝒪[F])` is identified with `GL_{N,𝒪[F]}`, compatibly with both generic identifications. -/
def matrixOrderModelIso :
    (matrixOrderModel F N).Iso (GeneralLinear.standardIntegralModel 𝒪[F] F (Fin N))
      (CategoryTheory.Iso.refl _) where
  iso := generalLinearIso (CommRingCat.of 𝒪[F]) N
  generic_comm := by
    rw [CategoryTheory.Iso.refl_hom, Category.comp_id]
    refine hom_ext_points fun T t =>
      (GeneralLinear.pointsEquiv (Fin N) (CommRingCat.of F) T).injective ?_
    rw [Grp.comp_hom_hom, ← Category.assoc]
    change GeneralLinear.pointsEquiv (Fin N) (CommRingCat.of F) T
        ((t ≫ ((GroupScheme.baseChange (Spec.algebraMap 𝒪[F] F)).map
          (generalLinearIso (CommRingCat.of 𝒪[F]) N).hom).hom.hom) ≫
          (GeneralLinear.baseChangeIso (Fin N) (Spec.algebraMap 𝒪[F] F)).hom.hom.hom) = _
    rw [GeneralLinear.pointsEquiv_comp_baseChangeIso_hom, baseChangePointsEquiv_comp,
      generalLinearIso_hom_points]
    dsimp only [matrixOrderModel, orderModel, unitModel, unitGenericIso, unitGenericIso₁,
      unitGenericIso₂, CategoryTheory.Iso.trans_hom]
    rw [Grp.comp_hom_hom, Grp.comp_hom_hom, ← Category.assoc, ← Category.assoc]
    conv_rhs => rw [generalLinearIso_hom_points]
    conv_lhs => rw [matrixPointsEquiv, MulEquiv.trans_apply]
    conv_rhs => rw [matrixPointsEquiv, MulEquiv.trans_apply,
      congrIso_hom_points, congrPointsEquiv, MulEquiv.trans_apply,
      baseChangeIso_hom_points (matrixBasis (CommRingCat.of 𝒪[F]) N) (CommRingCat.of F) T,
      basePointsEquiv_apply (matrixBasis (CommRingCat.of 𝒪[F]) N) (CommRingCat.of F) T]
    let : Algebra (CommRingCat.of F) (WeilGm.restrictedSections (CommRingCat.of 𝒪[F])
        (CommRingCat.of F) T) :=
      WeilGm.restrictedSectionsAlgebra (CommRingCat.of 𝒪[F]) (CommRingCat.of F) T
    let : IsScalarTower (CommRingCat.of 𝒪[F]) (CommRingCat.of F)
        (WeilGm.restrictedSections (CommRingCat.of 𝒪[F]) (CommRingCat.of F) T) :=
      WeilGm.restrictedSectionsScalarTower (CommRingCat.of 𝒪[F]) (CommRingCat.of F) T
    apply Units.ext
    exact matrixEquivTensor_symm_orderEquiv F N _ _

/-- The standard model identified back with the order model of `M_N(𝒪[F])`. -/
def standardMatrixOrderIso :
    (GeneralLinear.standardIntegralModel 𝒪[F] F (Fin N)).Iso (matrixOrderModel F N)
      (CategoryTheory.Iso.refl _) :=
  (matrixOrderModelIso F N).symm.changeGeneric _ rfl

/-! ### The Iwahori model over the standard model -/

/-- The Iwahori model maps to the standard model `GL_{N,𝒪[F]}`: the inclusion of the Iwahori
order into `M_N(𝒪[F])`, followed by the identification of the order model of `M_N(𝒪[F])` with
the standard model. -/
def iwahoriStandardHom :
    (iwahoriModel F N).Hom (GeneralLinear.standardIntegralModel 𝒪[F] F (Fin N)) (𝟙 _) where
  hom := (iwahoriMatrixHom F N).hom ≫ (matrixOrderModelIso F N).iso.hom
  generic_comm := by
    rw [Functor.map_comp, Category.assoc, (matrixOrderModelIso F N).generic_comm]
    simpa only [CategoryTheory.Iso.refl_hom, Category.comp_id] using
      (iwahoriMatrixHom F N).generic_comm

/-- The Iwahori model data maps to the standard hyperspecial model data of `GL_N`. -/
def iwahoriStandardModelHom :
    RelativeComponentModelHom (iwahoriModelData F N) (generalLinearModelData F N) where
  full := iwahoriStandardHom F N
  neutral := iwahoriStandardHom F N
  component_comm := (Category.comp_id _).trans (Category.id_comp _).symm

/-- The two extensions of the identity, to the standard model and to the order model of
`M_N(𝒪[F])`, have isomorphic special-fibre maps. -/
theorem iwahoriStandardHom_specialFibreMap_square :
    (IntegralModel.reflIso (iwahoriModel F N)).specialFibreIso.hom ≫
        (iwahoriMatrixHom F N).specialFibreMap =
      (iwahoriStandardHom F N).specialFibreMap ≫ (standardMatrixOrderIso F N).specialFibreIso.hom := by
  change (GroupScheme.baseChange (IntegralModel.residueBaseMap 𝒪[F])).map
        (IntegralModel.reflIso (iwahoriModel F N)).iso.hom ≫
      (GroupScheme.baseChange (IntegralModel.residueBaseMap 𝒪[F])).map (iwahoriMatrixHom F N).hom =
    (GroupScheme.baseChange (IntegralModel.residueBaseMap 𝒪[F])).map (iwahoriStandardHom F N).hom ≫
      (GroupScheme.baseChange (IntegralModel.residueBaseMap 𝒪[F])).map
        (standardMatrixOrderIso F N).iso.hom
  simpa only [Functor.map_comp] using
    congrArg (GroupScheme.baseChange (IntegralModel.residueBaseMap 𝒪[F])).map
      ((IntegralModel.reflIso (iwahoriModel F N)).hom_square (standardMatrixOrderIso F N)
        (iwahoriStandardHom F N) (iwahoriMatrixHom F N))

/-! ### KP Axiom 4.1.22 for the Iwahori model over the standard model -/

/-- KP Axiom 4.1.22(1) and Theorem 8.4.19(1), first clause, over the standard model. -/
theorem iwahoriStandardModelHom_hasSmoothConnectedUnipotentKernel :
    (iwahoriStandardModelHom F N).HasSmoothConnectedUnipotentKernel :=
  IntegralModel.Iso.specialFibreKernel_properties (IntegralModel.reflIso (iwahoriModel F N))
    (standardMatrixOrderIso F N) (iwahoriStandardHom F N) (iwahoriMatrixHom F N)
    (iwahoriMatrixModelHom_hasSmoothConnectedUnipotentKernel F N)

/-- KP Axiom 4.1.22(2) and Theorem 8.4.19(2) over the standard model: the special-fibre image is
parabolic. -/
theorem iwahoriStandardModelHom_hasParabolicSpecialFibreImage :
    (iwahoriStandardModelHom F N).HasParabolicSpecialFibreImage :=
  IntegralModel.Iso.specialFibreImage_isParabolic (IntegralModel.reflIso (iwahoriModel F N))
    (standardMatrixOrderIso F N) (iwahoriStandardHom F N) (iwahoriMatrixHom F N)
    (iwahoriMatrixModelHom_hasParabolicSpecialFibreImage F N)

/-- The special-fibre image over the standard model is a Borel subgroup. -/
theorem iwahoriStandardModelHom_isBorelSubgroup_specialFibreImage :
    IsBorelSubgroup (iwahoriStandardModelHom F N).specialFibreImageInclusion := by
  have h := iwahoriStandardHom_specialFibreMap_square F N
  have hp : IsBorelSubgroup (SchematicImage.inclusion (iwahoriStandardHom F N).specialFibreMap ≫
      (standardMatrixOrderIso F N).specialFibreIso.hom) := by
    rw [← SchematicImage.isoOfReverseIsoSquare_hom_comp _ _ _ _ h]
    exact (iwahoriMatrixModelHom_isBorelSubgroup_specialFibreImage F N).iso_comp _
  change IsBorelSubgroup (SchematicImage.inclusion (iwahoriStandardHom F N).specialFibreMap)
  simpa only [Category.assoc, CategoryTheory.Iso.symm_hom, CategoryTheory.Iso.hom_inv_id,
    Category.comp_id] using hp.comp_iso (standardMatrixOrderIso F N).specialFibreIso.symm

/-- KP Axiom 4.1.22(4) and Theorem 8.4.19(3) over the standard model: the reduction preimage of
the residue-field points of the special-fibre image is the Iwahori image. -/
theorem iwahoriStandardModelHom_hasParabolicReductionPreimage :
    (iwahoriStandardModelHom F N).HasParabolicReductionPreimage := by
  rw [RelativeComponentModelHom.hasParabolicReductionPreimage_iff_imageReductionPreimage]
  exact IntegralModel.Iso.imageReductionPreimage_eq_range
    (IntegralModel.reflIso (iwahoriModel F N)) (standardMatrixOrderIso F N)
    (iwahoriStandardHom F N) (iwahoriMatrixModelHom F N).neutral
    ((RelativeComponentModelHom.hasParabolicReductionPreimage_iff_imageReductionPreimage _).mp
      (iwahoriMatrixModelHom_hasParabolicReductionPreimage F N))

/-- KP Axiom 4.1.22(3), parabolicity clause, over the standard model: the image in the reductive
quotient is parabolic. The reductive quotient of the standard model is its special fibre. -/
theorem iwahoriStandardModelHom_hasParabolicReductiveImage :
    (iwahoriStandardModelHom F N).HasParabolicReductiveImage (generalLinearQuotientData F N) := by
  unfold RelativeComponentModelHom.HasParabolicReductiveImage
  change IsParabolicSubgroup
    (SchematicImage.inclusion ((iwahoriStandardModelHom F N).neutralSpecialFibreMap ≫ 𝟙 _))
  rw [Category.comp_id]
  exact iwahoriStandardModelHom_hasParabolicSpecialFibreImage F N

/-- The image in the reductive quotient of the standard model is a Borel subgroup. -/
theorem iwahoriStandardModelHom_isBorelSubgroup_reductiveImage :
    IsBorelSubgroup
      ((iwahoriStandardModelHom F N).reductiveImageInclusion (generalLinearQuotientData F N)) := by
  change IsBorelSubgroup
    (SchematicImage.inclusion ((iwahoriStandardModelHom F N).neutralSpecialFibreMap ≫ 𝟙 _))
  rw [Category.comp_id]
  exact iwahoriStandardModelHom_isBorelSubgroup_specialFibreImage F N

/-- KP Axiom 4.1.22(7) for the hyperspecial vertex and the standard alcove: both reductions are
surjective and `G(F)^{0+}` at the hyperspecial vertex lies in `I^+`. The Library's predicate
depends only on the two quotient data, not on a model homomorphism. -/
theorem generalLinearIwahori_satisfiesPositiveRadicalClause :
    RelativeComponentModelHom.SatisfiesPositiveRadicalClause
      (generalLinearQuotientData F N) (iwahoriQuotientData F N) := by
  let : HenselianLocalRing 𝒪[F] := henselianLocalRing_integer
  refine ⟨IntegralModel.reduction_surjective _ (generalLinearModelData F N).neutral_smooth,
    IntegralModel.reduction_surjective _ (iwahoriModelData F N).neutral_smooth, ?_⟩
  rw [iwahoriQuotientData_positivePoints]
  exact positivePoints_le_generalLinearIwahoriPositivePoints F N

end Langlands.BruhatTits.IntegralModels
