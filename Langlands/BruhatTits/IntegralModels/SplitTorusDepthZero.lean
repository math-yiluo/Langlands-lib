import Langlands.BruhatTits.IntegralModels.FiniteReductiveQuotient
import Langlands.GroupScheme.IntegralModel.LocalReductivity
import Langlands.GroupScheme.IntegralModel.SplitIntegralPoints
import Langlands.GroupScheme.Torus.SplitReductiveProof
import Langlands.GroupScheme.Reductive.TrivialUnipotentRadical
import Langlands.GroupScheme.CentralIsogeny.Basic

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-! # Depth-zero data for split tori over a local field

For a finite index type `I`, the split torus `G_m^I` over an integral domain
`R` with fraction field `K` is a model of the split torus `G_m^I` over `K`,
through the published base-change isomorphism of split tori. Its integral
sections are the families `I → Rˣ`.

For a nonarchimedean local field `F`, this canonical model over `𝒪[F]` gives
actual relative-component model data, with full and neutral model equal. Its
special fibre is the split torus `G_m^I` over `𝓀[F]`, so the trivial subgroup is
its unipotent radical and the identity is a reductive quotient. This is the
split-torus regression example for the depth-zero layer:
`G^0(𝒪) = (𝒪[F]ˣ)^I`, `G(F)^{0+} = (1 + 𝔪)^I`, and the index is
`(q - 1) ^ |I|`.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj ValuativeRel

namespace Langlands.GroupScheme.IntegralModel

variable (R K : Type u) [CommRing R] [IsDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K] (I : Type u) [Finite I]

/-- The split torus on `I` over `R`, with the base-change isomorphism of split
tori as its generic identification, is a model of the split torus on `I` over
`K`. -/
def splitTorusModel : IntegralModel R K (splitTorus (Spec (CommRingCat.of K)) I) where
  group := splitTorus (Spec (CommRingCat.of R)) I
  affine := isAffineHom_splitTorus _ I
  flat := by
    have := smooth_splitTorus (S := Spec (CommRingCat.of R)) I
    infer_instance
  finiteType := by
    have := smooth_splitTorus (S := Spec (CommRingCat.of R)) I
    infer_instance
  genericIso := splitTorus.baseChangeIso (Spec.algebraMap R K) I

/-- The split-torus model is smooth over `R`. -/
theorem splitTorusModel_isSmooth : (splitTorusModel R K I).IsSmooth :=
  smooth_splitTorus I

/-- The integral sections of the split-torus model are the families, indexed
by `I`, of units of `R`. -/
def splitTorusSectionsEquiv : (splitTorusModel R K I).integralSections ≃* (I → Rˣ) :=
  splitTorus.affinePointsEquiv I (𝟙 (Spec (CommRingCat.of R)))

/-- The generic identification sends an integral section to the same family of
units, mapped into `K`. -/
theorem splitTorusModel_integralPointMap (x : (splitTorusModel R K I).integralSections) :
    splitTorus.affinePointsEquiv I (𝟙 (Spec (CommRingCat.of K)))
        ((splitTorusModel R K I).integralPointMap x) =
      fun j => Units.map (algebraMap R K).toMonoidHom (splitTorusSectionsEquiv R K I x j) := by
  funext j
  apply Units.ext
  have h := congrFun (pointsEquiv_baseChangeSectionHom (R := R) (K := K) (I := I) x) j
  change (Scheme.ΓSpecIso (CommRingCat.of K)).hom
      (splitTorus.pointsEquiv I (Over.mk (𝟙 (Spec (CommRingCat.of K))))
        (baseChangeSectionHom (Spec.algebraMap R K) (splitTorus (Spec (CommRingCat.of R)) I) x ≫
          (splitTorus.baseChangeIso (Spec.algebraMap R K) I).hom.hom.hom) j).val =
    (algebraMap R K) ((Scheme.ΓSpecIso (CommRingCat.of R)).hom
      (splitTorus.pointsEquiv I (Over.mk (𝟙 (Spec (CommRingCat.of R)))) x j).val)
  rw [h]
  change ((Spec.algebraMap R K).appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of K)).hom) _ = _
  rw [Spec.algebraMap, Scheme.ΓSpecIso_naturality]
  rfl

end Langlands.GroupScheme.IntegralModel

namespace Langlands.BruhatTits.IntegralModels

open GroupScheme

variable (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] (I : Type u) [Finite I]

/-- The canonical split-torus model over `𝒪[F]`, as relative-component model
data whose full and neutral models are both this model. Smoothness and
connected fibres come from the published reductive-model criterion. -/
def splitTorusModelData :
    RelativeComponentModelData 𝒪[F] F (splitTorus (Spec (CommRingCat.of F)) I) :=
  (IntegralModel.splitTorusModel 𝒪[F] F I).relativeComponentData_of_reductive_localField
    (isSplitTorus_splitTorus I).isConnectedReductive
    ((isSplitTorus_splitTorus I).baseChange _).isConnectedReductive

/-- The neutral model is the canonical split-torus model. -/
theorem splitTorusModelData_neutral :
    (splitTorusModelData F I).neutral = IntegralModel.splitTorusModel 𝒪[F] F I := rfl

/-- The special fibre of the split-torus model is a split torus. -/
theorem isSplitTorus_splitTorusSpecialFibre :
    IsSplitTorus (splitTorusModelData F I).neutral.specialFibre :=
  (isSplitTorus_splitTorus I).baseChange _

/-- The special-fibre quotient data of the split-torus model: the radical is
the trivial group with its unit inclusion, and the quotient is the special
fibre itself with the identity projection. -/
def splitTorusQuotientData : SpecialFibreQuotientData (splitTorusModelData F I) where
  radical := Grp.trivial _
  radicalInclusion := kernelUnit _
  quotient := (splitTorusModelData F I).neutral.specialFibre
  quotient_affine := (isSplitTorus_splitTorusSpecialFibre F I).isAffineHom
  projection := 𝟙 _

/-- The trivial radical is the unipotent radical of the split special fibre,
the identity is the fppf quotient by it, and the quotient is connected
reductive. -/
theorem splitTorusQuotientData_isReductiveQuotient :
    (splitTorusQuotientData F I).IsReductiveQuotient := by
  have hsplit := isSplitTorus_splitTorusSpecialFibre F I
  have : IsAffineHom (splitTorusModelData F I).neutral.specialFibre.X.hom :=
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

/-- The residue-field points of the special fibre of the split-torus model are
the families, indexed by `I`, of units of the residue field. -/
def splitTorusSpecialFibrePointsEquiv :
    rationalPoints (splitTorusModelData F I).neutral.specialFibre ≃* (I → 𝓀[F]ˣ) :=
  (splitTorus.baseChangePointsEquiv (IntegralModel.residueBaseMap 𝒪[F]) I
      (Over.mk (𝟙 _))).trans
    (MulEquiv.piCongrRight fun _ => Units.mapEquiv
      (Scheme.ΓSpecIso (CommRingCat.of 𝓀[F])).commRingCatIsoToRingEquiv.toMulEquiv)

/-- The index of `G(F)^{0+}` in `G^0(𝒪) = (𝒪[F]ˣ)^I` is `(q - 1) ^ |I|`, where
`q` is the cardinality of the residue field. -/
theorem splitTorus_index_positivePoints_subgroupOf :
    ((splitTorusQuotientData F I).positivePoints.subgroupOf
      (splitTorusModelData F I).neutral.integralPoints).index =
        (Nat.card 𝓀[F] - 1) ^ Nat.card I := by
  obtain ⟨hrad, hQ, -⟩ := splitTorusQuotientData_isReductiveQuotient F I
  rw [SpecialFibreQuotientData.localField_index_positivePoints_subgroupOf _ hrad hQ]
  change Nat.card (rationalPoints (splitTorusModelData F I).neutral.specialFibre) = _
  rw [Nat.card_congr (splitTorusSpecialFibrePointsEquiv F I).toEquiv, Nat.card_fun,
    Nat.card_units]

/-- Small-residue case: when the residue field has two elements, `G(F)^{0+}`
is all of `G^0(𝒪)`. -/
theorem splitTorus_index_positivePoints_subgroupOf_eq_one
    (hq : Nat.card 𝓀[F] = 2) :
    ((splitTorusQuotientData F I).positivePoints.subgroupOf
      (splitTorusModelData F I).neutral.integralPoints).index = 1 := by
  rw [splitTorus_index_positivePoints_subgroupOf, hq]
  exact one_pow _

/-- Under the unit identifications, reduction of integral sections is the
residue map on each unit coordinate. -/
theorem splitTorusSpecialFibrePointsEquiv_reduction
    (x : (splitTorusModelData F I).neutral.integralSections) :
    splitTorusSpecialFibrePointsEquiv F I ((splitTorusModelData F I).neutral.reduction x) =
      fun j => Units.map (IsLocalRing.residue 𝒪[F]).toMonoidHom
        (IntegralModel.splitTorusSectionsEquiv 𝒪[F] F I x j) := by
  have h := congrArg (splitTorus.pointsEquiv I _)
    (baseChangePointsEquiv_baseChangeSectionHom (IntegralModel.residueBaseMap 𝒪[F])
      (splitTorus (Spec (CommRingCat.of 𝒪[F])) I) x)
  rw [splitTorus.pointsEquiv_naturality] at h
  funext j
  apply Units.ext
  have hj := congrArg (fun v => (v j).val) h
  change (Scheme.ΓSpecIso (CommRingCat.of 𝓀[F])).hom
      ((splitTorus.pointsEquiv I _
        (GroupScheme.baseChangePointsEquiv (IntegralModel.residueBaseMap 𝒪[F])
          (splitTorus (Spec (CommRingCat.of 𝒪[F])) I) (Over.mk (𝟙 _))
          (baseChangeSectionHom (IntegralModel.residueBaseMap 𝒪[F])
            (splitTorus (Spec (CommRingCat.of 𝒪[F])) I) x))) j).val =
    (IsLocalRing.residue 𝒪[F]) ((Scheme.ΓSpecIso (CommRingCat.of 𝒪[F])).hom
      (splitTorus.pointsEquiv I (Over.mk (𝟙 (Spec (CommRingCat.of 𝒪[F])))) x j).val)
  rw [hj]
  change ((IntegralModel.residueBaseMap 𝒪[F]).appTop ≫
      (Scheme.ΓSpecIso (CommRingCat.of 𝓀[F])).hom) _ = _
  rw [IntegralModel.residueBaseMap, Scheme.ΓSpecIso_naturality]
  rfl

/-- The radical has only the identity residue-field point. -/
theorem splitTorusQuotientData_radicalPoints :
    (splitTorusQuotientData F I).radicalPoints = ⊥ := by
  rw [eq_bot_iff]
  rintro _ ⟨y, rfl⟩
  have hy : y ≫ (kernelUnit (splitTorusModelData F I).neutral.specialFibre).hom.hom ∈
      (SubgroupFunctor.range
        (kernelUnit (splitTorusModelData F I).neutral.specialFibre)).carrier
        (Over.mk (𝟙 _)) := ⟨y, rfl⟩
  rw [range_kernelUnit] at hy
  simp only [SubgroupFunctor.bot_carrier, Subgroup.mem_bot] at hy
  exact Subgroup.mem_bot.mpr hy

/-- `G(F)^{0+}` consists of the points whose family of units in `Fˣ` is the
image of a family `u` of units of `𝒪[F]` with every residue equal to `1`, that
is, `(1 + 𝔪)^I`. -/
theorem mem_splitTorus_positivePoints
    (g : rationalPoints (splitTorus (Spec (CommRingCat.of F)) I)) :
    g ∈ (splitTorusQuotientData F I).positivePoints ↔
      ∃ u : I → 𝒪[F]ˣ, (∀ j, IsLocalRing.residue 𝒪[F] (u j) = 1) ∧
        splitTorus.affinePointsEquiv I (𝟙 _) g =
          fun j => Units.map (algebraMap 𝒪[F] F).toMonoidHom (u j) := by
  rw [SpecialFibreQuotientData.mem_positivePoints, splitTorusQuotientData_radicalPoints]
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨IntegralModel.splitTorusSectionsEquiv 𝒪[F] F I x, fun j => ?_,
      IntegralModel.splitTorusModel_integralPointMap 𝒪[F] F I x⟩
    have h := congrArg (splitTorusSpecialFibrePointsEquiv F I) (Subgroup.mem_bot.mp hx)
    rw [splitTorusSpecialFibrePointsEquiv_reduction, map_one] at h
    exact congrArg Units.val (congrFun h j)
  · rintro ⟨u, hu, hg⟩
    refine ⟨(IntegralModel.splitTorusSectionsEquiv 𝒪[F] F I).symm u, ?_, ?_⟩
    · rw [Subgroup.mem_bot]
      apply (splitTorusSpecialFibrePointsEquiv F I).injective
      rw [splitTorusSpecialFibrePointsEquiv_reduction, MulEquiv.apply_symm_apply, map_one]
      funext j
      exact Units.ext (hu j)
    · apply (splitTorus.affinePointsEquiv I (𝟙 (Spec (CommRingCat.of F)))).injective
      change splitTorus.affinePointsEquiv I (𝟙 _)
        ((IntegralModel.splitTorusModel 𝒪[F] F I).integralPointMap
          ((IntegralModel.splitTorusSectionsEquiv 𝒪[F] F I).symm u)) = _
      rw [IntegralModel.splitTorusModel_integralPointMap, MulEquiv.apply_symm_apply, hg]

/-- `G^0(𝒪)` consists of the points whose family of units in `Fˣ` is the image
of a family of units of `𝒪[F]`. -/
theorem mem_splitTorus_integralPoints
    (g : rationalPoints (splitTorus (Spec (CommRingCat.of F)) I)) :
    g ∈ (splitTorusModelData F I).neutral.integralPoints ↔
      ∃ u : I → 𝒪[F]ˣ, splitTorus.affinePointsEquiv I (𝟙 _) g =
        fun j => Units.map (algebraMap 𝒪[F] F).toMonoidHom (u j) := by
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨IntegralModel.splitTorusSectionsEquiv 𝒪[F] F I x,
      IntegralModel.splitTorusModel_integralPointMap 𝒪[F] F I x⟩
  · rintro ⟨u, hg⟩
    refine ⟨(IntegralModel.splitTorusSectionsEquiv 𝒪[F] F I).symm u, ?_⟩
    apply (splitTorus.affinePointsEquiv I (𝟙 (Spec (CommRingCat.of F)))).injective
    change splitTorus.affinePointsEquiv I (𝟙 _)
      ((IntegralModel.splitTorusModel 𝒪[F] F I).integralPointMap
        ((IntegralModel.splitTorusSectionsEquiv 𝒪[F] F I).symm u)) = _
    rw [IntegralModel.splitTorusModel_integralPointMap, MulEquiv.apply_symm_apply, hg]

end Langlands.BruhatTits.IntegralModels
