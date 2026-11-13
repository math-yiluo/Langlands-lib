import Langlands.BruhatTits.IntegralModels.FiniteReductiveQuotient
import Langlands.GroupScheme.IntegralModel.LocalReductivity
import Langlands.GroupScheme.IntegralModel.Multiplicative
import Langlands.GroupScheme.Torus.SplitReductiveProof
import Langlands.GroupScheme.Reductive.TrivialUnipotentRadical
import Langlands.GroupScheme.CentralIsogeny.Basic

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-! # Depth-zero data for the split torus `G_m` over a local field

For a nonarchimedean local field `F`, the canonical model `G_{m,𝒪[F]}` of
`G_{m,F}` gives actual relative-component model data, with full and neutral
model equal. Its special fibre `G_{m,𝓀[F]}` is a split torus, so the trivial
subgroup is its unipotent radical and the identity is a reductive quotient.
This is the split-torus regression example for the depth-zero layer:
`G^0(𝒪) = 𝒪[F]ˣ`, `G(F)^{0+} = 1 + 𝔪`, and the index is `q - 1`.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj ValuativeRel

namespace Langlands.BruhatTits.IntegralModels

open GroupScheme

variable (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

/-- The canonical model `G_{m,𝒪[F]}` of `G_{m,F}`, as relative-component model
data whose full and neutral models are both this model. Smoothness and
connected fibres come from the published reductive-model criterion. -/
def multiplicativeModelData :
    RelativeComponentModelData 𝒪[F] F (Gm (Spec (CommRingCat.of F))).toGrp :=
  (IntegralModel.multiplicative 𝒪[F] F).relativeComponentData_of_reductive_localField
    isSplitTorus_gm.isConnectedReductive
    (isSplitTorus_gm.baseChange _).isConnectedReductive

/-- The neutral model is the canonical multiplicative model. -/
theorem multiplicativeModelData_neutral :
    (multiplicativeModelData F).neutral = IntegralModel.multiplicative 𝒪[F] F := rfl

/-- The special fibre of the multiplicative model is a split torus. -/
theorem isSplitTorus_multiplicativeSpecialFibre :
    IsSplitTorus (multiplicativeModelData F).neutral.specialFibre :=
  isSplitTorus_gm.baseChange _

/-- The special-fibre quotient data of the multiplicative model: the radical is
the trivial group with its unit inclusion, and the quotient is the special
fibre itself with the identity projection. -/
def multiplicativeQuotientData : SpecialFibreQuotientData (multiplicativeModelData F) where
  radical := Grp.trivial _
  radicalInclusion := kernelUnit _
  quotient := (multiplicativeModelData F).neutral.specialFibre
  quotient_affine := (isSplitTorus_multiplicativeSpecialFibre F).isAffineHom
  projection := 𝟙 _

/-- The trivial radical is the unipotent radical of the split special fibre,
the identity is the fppf quotient by it, and the quotient is connected
reductive. -/
theorem multiplicativeQuotientData_isReductiveQuotient :
    (multiplicativeQuotientData F).IsReductiveQuotient := by
  have hsplit := isSplitTorus_multiplicativeSpecialFibre F
  have : IsAffineHom (multiplicativeModelData F).neutral.specialFibre.X.hom :=
    hsplit.isAffineHom
  refine ⟨?_, ?_, hsplit.isConnectedReductive⟩
  · exact isUnipotentRadical_kernelUnit _ hsplit.hasTrivialUnipotentRadical
  · refine ⟨?_, ?_, ?_, ?_⟩
    · change Flat (𝟙 _)
      infer_instance
    · change Surjective (𝟙 _)
      infer_instance
    · change LocallyOfFinitePresentation (𝟙 _)
      infer_instance
    change SubgroupFunctor.range (kernelι (𝟙 _)) = SubgroupFunctor.range (kernelUnit _)
    rw [range_kernelUnit]
    ext T x
    rw [mem_range_kernelι_iff]
    change x ≫ 𝟙 _ = 1 ↔ x = 1
    rw [Category.comp_id]

/-- The residue-field points of the special fibre of the multiplicative model
are the units of the residue field. -/
def multiplicativeSpecialFibrePointsEquiv :
    rationalPoints (multiplicativeModelData F).neutral.specialFibre ≃* 𝓀[F]ˣ :=
  (Gm.baseChangeUnitsEquiv (IntegralModel.residueBaseMap 𝒪[F]) (Over.mk (𝟙 _))).trans
    (Units.mapEquiv
      (Scheme.ΓSpecIso (CommRingCat.of 𝓀[F])).commRingCatIsoToRingEquiv.toMulEquiv)

/-- The index of `G(F)^{0+}` in `G^0(𝒪) = 𝒪[F]ˣ` is `q - 1`, where `q` is the
cardinality of the residue field. -/
theorem multiplicative_index_positivePoints_subgroupOf :
    ((multiplicativeQuotientData F).positivePoints.subgroupOf
      (multiplicativeModelData F).neutral.integralPoints).index = Nat.card 𝓀[F] - 1 := by
  obtain ⟨hrad, hQ, -⟩ := multiplicativeQuotientData_isReductiveQuotient F
  rw [SpecialFibreQuotientData.localField_index_positivePoints_subgroupOf _ hrad hQ]
  change Nat.card (rationalPoints (multiplicativeModelData F).neutral.specialFibre) = _
  rw [Nat.card_congr (multiplicativeSpecialFibrePointsEquiv F).toEquiv, Nat.card_units]

/-- Small-residue case: when the residue field has two elements, `G(F)^{0+}`
is all of `G^0(𝒪)`. -/
theorem multiplicative_index_positivePoints_subgroupOf_eq_one
    (hq : Nat.card 𝓀[F] = 2) :
    ((multiplicativeQuotientData F).positivePoints.subgroupOf
      (multiplicativeModelData F).neutral.integralPoints).index = 1 := by
  rw [multiplicative_index_positivePoints_subgroupOf, hq]

/-- Under the unit identifications, reduction of integral sections is the
residue map on units of `𝒪[F]`. -/
theorem multiplicativeSpecialFibrePointsEquiv_reduction
    (x : (multiplicativeModelData F).neutral.integralSections) :
    multiplicativeSpecialFibrePointsEquiv F ((multiplicativeModelData F).neutral.reduction x) =
      Units.map (IsLocalRing.residue 𝒪[F]).toMonoidHom
        (IntegralModel.multiplicativeSectionsEquiv 𝒪[F] F x) := by
  apply Units.ext
  change (Gm.affinePointsEquiv (IntegralModel.residueBaseMap 𝒪[F])
      ((baseChangeBasePointsEquiv (IntegralModel.residueBaseMap 𝒪[F])
        (Gm (Spec (CommRingCat.of 𝒪[F]))).toGrp)
        ((baseChangeBasePointsEquiv (IntegralModel.residueBaseMap 𝒪[F])
          (Gm (Spec (CommRingCat.of 𝒪[F]))).toGrp).symm
          ((Over.homMk (IntegralModel.residueBaseMap 𝒪[F]) (by simp) :
            Over.mk (IntegralModel.residueBaseMap 𝒪[F]) ⟶
              Over.mk (𝟙 (Spec (CommRingCat.of 𝒪[F])))) ≫ x))) : 𝓀[F]) = _
  rw [MulEquiv.apply_symm_apply]
  rw [Gm.affinePointsEquiv_val, Gm.pointsEquiv_naturality]
  change ((IntegralModel.residueBaseMap 𝒪[F]).appTop ≫
      (Scheme.ΓSpecIso (CommRingCat.of 𝓀[F])).hom) _ =
    (IsLocalRing.residue 𝒪[F]) ((Scheme.ΓSpecIso (CommRingCat.of 𝒪[F])).hom _)
  rw [IntegralModel.residueBaseMap, Scheme.ΓSpecIso_naturality]
  rfl

/-- The radical has only the identity residue-field point. -/
theorem multiplicativeQuotientData_radicalPoints :
    (multiplicativeQuotientData F).radicalPoints = ⊥ := by
  rw [eq_bot_iff]
  rintro _ ⟨y, rfl⟩
  have hy : y ≫ (kernelUnit (multiplicativeModelData F).neutral.specialFibre).hom.hom ∈
      (SubgroupFunctor.range
        (kernelUnit (multiplicativeModelData F).neutral.specialFibre)).carrier
        (Over.mk (𝟙 _)) := ⟨y, rfl⟩
  rw [range_kernelUnit] at hy
  simp only [SubgroupFunctor.bot_carrier, Subgroup.mem_bot] at hy
  exact Subgroup.mem_bot.mpr hy

/-- `G(F)^{0+}` consists of the points whose unit in `Fˣ` is the image of a
unit `u` of `𝒪[F]` with residue `1`, that is, `1 + 𝔪`. -/
theorem mem_multiplicative_positivePoints
    (g : rationalPoints (Gm (Spec (CommRingCat.of F))).toGrp) :
    g ∈ (multiplicativeQuotientData F).positivePoints ↔
      ∃ u : 𝒪[F]ˣ, IsLocalRing.residue 𝒪[F] u = 1 ∧
        Gm.affinePointsEquiv (𝟙 _) g = Units.map (algebraMap 𝒪[F] F).toMonoidHom u := by
  rw [SpecialFibreQuotientData.mem_positivePoints, multiplicativeQuotientData_radicalPoints]
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨IntegralModel.multiplicativeSectionsEquiv 𝒪[F] F x, ?_,
      IntegralModel.multiplicative_integralPointMap 𝒪[F] F x⟩
    have h := congrArg (multiplicativeSpecialFibrePointsEquiv F) (Subgroup.mem_bot.mp hx)
    rw [multiplicativeSpecialFibrePointsEquiv_reduction, map_one] at h
    exact congrArg Units.val h
  · rintro ⟨u, hu, hg⟩
    refine ⟨(IntegralModel.multiplicativeSectionsEquiv 𝒪[F] F).symm u, ?_, ?_⟩
    · rw [Subgroup.mem_bot]
      apply (multiplicativeSpecialFibrePointsEquiv F).injective
      rw [multiplicativeSpecialFibrePointsEquiv_reduction, MulEquiv.apply_symm_apply, map_one]
      exact Units.ext hu
    · apply (Gm.affinePointsEquiv (𝟙 (Spec (CommRingCat.of F)))).injective
      change Gm.affinePointsEquiv (𝟙 _) ((IntegralModel.multiplicative 𝒪[F] F).integralPointMap
        ((IntegralModel.multiplicativeSectionsEquiv 𝒪[F] F).symm u)) = _
      rw [IntegralModel.multiplicative_integralPointMap, MulEquiv.apply_symm_apply, hg]

/-- `G^0(𝒪)` consists of the points whose unit in `Fˣ` is the image of a unit
of `𝒪[F]`. -/
theorem mem_multiplicative_integralPoints
    (g : rationalPoints (Gm (Spec (CommRingCat.of F))).toGrp) :
    g ∈ (multiplicativeModelData F).neutral.integralPoints ↔
      ∃ u : 𝒪[F]ˣ,
        Gm.affinePointsEquiv (𝟙 _) g = Units.map (algebraMap 𝒪[F] F).toMonoidHom u := by
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨IntegralModel.multiplicativeSectionsEquiv 𝒪[F] F x,
      IntegralModel.multiplicative_integralPointMap 𝒪[F] F x⟩
  · rintro ⟨u, hg⟩
    refine ⟨(IntegralModel.multiplicativeSectionsEquiv 𝒪[F] F).symm u, ?_⟩
    apply (Gm.affinePointsEquiv (𝟙 (Spec (CommRingCat.of F)))).injective
    change Gm.affinePointsEquiv (𝟙 _) ((IntegralModel.multiplicative 𝒪[F] F).integralPointMap
      ((IntegralModel.multiplicativeSectionsEquiv 𝒪[F] F).symm u)) = _
    rw [IntegralModel.multiplicative_integralPointMap, MulEquiv.apply_symm_apply, hg]

end Langlands.BruhatTits.IntegralModels
