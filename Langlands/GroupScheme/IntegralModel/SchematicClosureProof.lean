import Langlands.GroupScheme.IntegralModel.SchematicClosure
import Langlands.GroupScheme.ImageGenerationAppend
import Langlands.GroupScheme.ImageGenerationDominant
import Langlands.CategoryTheory.GroupObjectDescent
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.Flat.Localization

/-! # Construction of the schematic closure of a closed generic subgroup -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.IntegralModel.SchematicClosureConstruction

section Flatness

variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

/-- Over a discrete valuation ring, a morphism from an affine scheme to `Spec R` is flat when its
global sections embed into a ring in which every nonzero element of `R` becomes a unit. -/
theorem flat_of_appTop_injective {X Y : Scheme.{u}} [IsAffine X]
    (g : X ⟶ Spec (CommRingCat.of R)) (t : Y ⟶ X) (ht : Function.Injective t.appTop)
    (hunit : ∀ r : R, r ≠ 0 →
      IsUnit (((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ (t ≫ g).appTop) r)) :
    Flat g := by
  rw [HasRingHomProperty.iff_of_isAffine (P := @Flat)]
  let φ : CommRingCat.of R ⟶ Γ(X, ⊤) := (Scheme.ΓSpecIso _).inv ≫ g.appTop
  have hg : g.appTop = (Scheme.ΓSpecIso _).hom ≫ φ := by simp [φ]
  rw [hg, CommRingCat.hom_comp, RingHom.Flat.comp_iff_of_bijective_right
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso _).hom)]
  let : Algebra R Γ(X, ⊤) := φ.hom.toAlgebra
  have : Module.IsTorsionFree R Γ(X, ⊤) := by
    refine Module.IsTorsionFree.of_smul_eq_zero fun r m hrm => ?_
    by_cases hr : r = 0
    · exact Or.inl hr
    right
    rw [Algebra.smul_def] at hrm
    have h := congrArg t.appTop hrm
    rw [map_mul, map_zero] at h
    have hu : IsUnit (t.appTop (algebraMap R Γ(X, ⊤) r)) := hunit r hr
    apply ht
    rw [map_zero]
    exact hu.mul_right_eq_zero.mp h
  exact RingHom.flat_algebraMap_iff.mpr inferInstance

end Flatness

section Base

variable (R K : Type u) [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K]

instance mono_specAlgebraMap : Mono (Spec.algebraMap R K) := by
  have : Epi (CommRingCat.ofHom (algebraMap R K)) := IsLocalization.epi (nonZeroDivisors R) K
  exact (inferInstance : Mono (Scheme.Spec.map (CommRingCat.ofHom (algebraMap R K)).op))

instance flat_specAlgebraMap : Flat (Spec.algebraMap R K) := by
  rw [Flat.SpecMap_iff]
  exact RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat K (nonZeroDivisors R))

instance isSchemeTheoreticallyDominant_specAlgebraMap :
    IsSchemeTheoreticallyDominant (Spec.algebraMap R K) := by
  have hinj : Function.Injective (Spec.algebraMap R K).appTop := by
    intro x y hxy
    have h := congrArg (Scheme.ΓSpecIso (CommRingCat.of K)).hom hxy
    rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, Scheme.ΓSpecIso_naturality,
      CommRingCat.comp_apply, CommRingCat.comp_apply] at h
    exact (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of R)).hom).1
      (IsFractionRing.injective R K h)
  rw [isSchemeTheoreticallyDominant_iff, Scheme.ker_of_isAffine,
    (RingHom.injective_iff_ker_eq_bot _).mp hinj,
    ← Scheme.IdealSheafData.equivOfIsAffine_symm_apply, map_bot]

end Base

section MonHom

variable {C : Type*} [Category C] [CartesianMonoidalCategory C] {X Y Z : C}
  [MonObj X] [MonObj Y] [MonObj Z]

/-- A morphism is a monoid morphism when its composite with a monomorphic monoid morphism is. -/
theorem isMonHom_of_comp_mono (g : X ⟶ Y) (m : Y ⟶ Z) [Mono m] [IsMonHom m]
    [IsMonHom (g ≫ m)] : IsMonHom g where
  one_hom := by
    apply (cancel_mono m).mp
    rw [Category.assoc, IsMonHom.one_hom (g ≫ m), IsMonHom.one_hom m]
  mul_hom := by
    apply (cancel_mono m).mp
    rw [Category.assoc, IsMonHom.mul_hom (g ≫ m), Category.assoc, IsMonHom.mul_hom m,
      tensorHom_comp_tensorHom_assoc]

end MonHom

section Construction

variable {R K : Type u} [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
  {G H : GroupScheme (Spec (CommRingCat.of K))} (N : IntegralModel R K G) (j : H ⟶ G)

/-- The originally specified generic map `H → G → N.group`, as a morphism over `Spec R`. -/
def genericOver : (Over.map (Spec.algebraMap R K)).obj H.X ⟶ N.group.X :=
  Over.homMk (j.hom.hom.left ≫ N.genericToModel) (by
    have h1 : N.genericIso.inv.hom.hom.left ≫ pullback.snd N.group.X.hom (Spec.algebraMap R K) =
        G.X.hom := Over.w N.genericIso.inv.hom.hom
    have h2 : j.hom.hom.left ≫ G.X.hom = H.X.hom := Over.w j.hom.hom
    simp only [genericToModel, Category.assoc, pullback.condition, reassoc_of% h1,
      reassoc_of% h2]
    rfl)

theorem genericOver_left :
    (genericOver N j).left = j.hom.hom.left ≫ N.genericToModel := rfl

/-- The generic map is the pullback-adjunction transpose of `j` followed by `N.genericIso⁻¹`. -/
theorem baseChangePointsEquiv_generic :
    baseChangePointsEquiv (Spec.algebraMap R K) N.group H.X (j ≫ N.genericIso.inv).hom.hom =
      genericOver N j := by
  apply Over.OverMorphism.ext
  rw [baseChangePointsEquiv_left]
  rfl

/-- Naturality of the generic map in test schemes over `Spec K`. -/
theorem map_comp_genericOver {T : Over (Spec (CommRingCat.of K))} (a : T ⟶ H.X) :
    (Over.map (Spec.algebraMap R K)).map a ≫ genericOver N j =
      baseChangePointsEquiv (Spec.algebraMap R K) N.group T
        (a ≫ (j ≫ N.genericIso.inv).hom.hom) := by
  rw [baseChangePointsEquiv_naturality, baseChangePointsEquiv_generic]

/-- The schematic closure: the scheme-theoretic image of the generic map, over `Spec R`. -/
def closureOver : Over (Spec (CommRingCat.of R)) :=
  Over.mk ((genericOver N j).left.imageι ≫ N.group.X.hom)

/-- The closed immersion of the closure into the ambient integral model. -/
def inclusionOver : closureOver N j ⟶ N.group.X :=
  Over.homMk (genericOver N j).left.imageι rfl

/-- The generic map with codomain restricted to the closure. -/
def projectionOver : (Over.map (Spec.algebraMap R K)).obj H.X ⟶ closureOver N j :=
  Over.homMk (genericOver N j).left.toImage (by simp [closureOver])

@[reassoc (attr := simp)]
theorem projectionOver_fac : projectionOver N j ≫ inclusionOver N j = genericOver N j :=
  Over.OverMorphism.ext (genericOver N j).left.toImage_imageι

instance isClosedImmersion_inclusionOver : IsClosedImmersion (inclusionOver N j).left :=
  inferInstanceAs (IsClosedImmersion (genericOver N j).left.imageι)

instance mono_inclusionOver : Mono (inclusionOver N j) := Over.mono_of_mono_left _

instance isAffineHom_closureOver : IsAffineHom (closureOver N j).hom :=
  inferInstanceAs (IsAffineHom ((genericOver N j).left.imageι ≫ N.group.X.hom))

instance locallyOfFiniteType_closureOver : LocallyOfFiniteType (closureOver N j).hom :=
  inferInstanceAs (LocallyOfFiniteType ((genericOver N j).left.imageι ≫ N.group.X.hom))

instance isAffine_closureOver_left : IsAffine (closureOver N j).left :=
  isAffine_of_isAffineHom (closureOver N j).hom

instance flat_mapObj (T : Over (Spec (CommRingCat.of K))) :
    Flat ((Over.map (Spec.algebraMap R K)).obj T).hom :=
  inferInstanceAs (Flat (T.hom ≫ Spec.algebraMap R K))

variable [IsClosedImmersion j.hom.hom.left]

instance quasiCompact_genericOver : QuasiCompact (genericOver N j).left := by
  rw [genericOver_left, genericToModel]
  infer_instance

instance quasiCompact_projectionOver : QuasiCompact (projectionOver N j).left :=
  inferInstanceAs (QuasiCompact (genericOver N j).left.toImage)

instance isSchemeTheoreticallyDominant_projectionOver :
    IsSchemeTheoreticallyDominant (projectionOver N j).left := by
  have : IsAffine N.group.X.left := isAffine_of_isAffineHom N.group.X.hom
  exact ImageGeneration.isSchemeTheoreticallyDominant_toImage (genericOver N j).left

instance flat_closureOver [IsDiscreteValuationRing R] : Flat (closureOver N j).hom := by
  refine flat_of_appTop_injective (closureOver N j).hom (projectionOver N j).left
    ((projectionOver N j).left.app_injective ⊤) fun r hr => ?_
  have hw : (projectionOver N j).left ≫ (closureOver N j).hom =
      H.X.hom ≫ Spec.algebraMap R K := Over.w (projectionOver N j)
  rw [hw, Scheme.Hom.comp_appTop, ← Scheme.ΓSpecIso_inv_naturality_assoc, CommRingCat.comp_apply]
  have hK : algebraMap R K r ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr hr
  exact (isUnit_iff_ne_zero.mpr hK).map _

section Group

variable [IsDiscreteValuationRing R]

/-- The terminal morphism out of the generic base; its underlying map is `Spec K → Spec R`. -/
abbrev genericBaseOver :
    (Over.map (Spec.algebraMap R K)).obj (𝟙_ (Over (Spec (CommRingCat.of K)))) ⟶
      𝟙_ (Over (Spec (CommRingCat.of R))) := toUnit _

instance isSchemeTheoreticallyDominant_genericBaseOver :
    IsSchemeTheoreticallyDominant (genericBaseOver (R := R) (K := K)).left := by
  change IsSchemeTheoreticallyDominant (𝟙 _ ≫ Spec.algebraMap R K)
  infer_instance

omit [IsClosedImmersion j.hom.hom.left] [IsDiscreteValuationRing R] in
/-- The unit of the integral model factors through the closure. -/
theorem exists_closureOne :
    ∃ e : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ closureOver N j,
      e ≫ inclusionOver N j = η[N.group.X] := by
  refine exists_over_factor_of_schematic_precomp (inclusionOver N j)
    (genericBaseOver (R := R) (K := K)) η[N.group.X]
    ((Over.map (Spec.algebraMap R K)).map η[H.X] ≫ projectionOver N j) ?_
  have h1 : η[H.X] ≫ (j ≫ N.genericIso.inv).hom.hom =
      (1 : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ N.genericFibre.X) := by
    rw [IsMonHom.one_hom, MonObj.one_eq_one]
  rw [Category.assoc, projectionOver_fac, map_comp_genericOver, h1, map_one,
    CategoryTheory.Hom.one_def]

/-- The comparison from the base change of the generic square to the integral square. -/
def squareComparison :
    (Over.map (Spec.algebraMap R K)).obj (H.X ⊗ H.X) ⟶
      (Over.map (Spec.algebraMap R K)).obj H.X ⊗ (Over.map (Spec.algebraMap R K)).obj H.X :=
  lift ((Over.map (Spec.algebraMap R K)).map (fst H.X H.X))
    ((Over.map (Spec.algebraMap R K)).map (snd H.X H.X))

instance isIso_squareComparison_left :
    IsIso (squareComparison (R := R) (K := K) (H := H)).left := by
  have hc : pullback.fst (H.X.hom ≫ Spec.algebraMap R K) (H.X.hom ≫ Spec.algebraMap R K) ≫
      H.X.hom = pullback.snd (H.X.hom ≫ Spec.algebraMap R K)
        (H.X.hom ≫ Spec.algebraMap R K) ≫ H.X.hom := by
    rw [← cancel_mono (Spec.algebraMap R K)]
    simpa only [Category.assoc] using pullback.condition
  refine ⟨⟨pullback.lift _ _ hc, ?_, ?_⟩⟩
  · apply pullback.hom_ext <;> simp [squareComparison]
  · apply pullback.hom_ext <;> simp [squareComparison]

instance isSchemeTheoreticallyDominant_square :
    IsSchemeTheoreticallyDominant
      (squareComparison (R := R) (K := K) (H := H) ≫
        (projectionOver N j ⊗ₘ projectionOver N j)).left := by
  have := ImageGeneration.isSchemeTheoreticallyDominant_tensorHom (projectionOver N j)
  rw [Over.comp_left]
  infer_instance

/-- The multiplication of the integral model restricts to the closure. -/
theorem exists_closureMul :
    ∃ m : closureOver N j ⊗ closureOver N j ⟶ closureOver N j,
      m ≫ inclusionOver N j = (inclusionOver N j ⊗ₘ inclusionOver N j) ≫ μ[N.group.X] := by
  refine exists_over_factor_of_schematic_precomp (inclusionOver N j)
    (squareComparison ≫ (projectionOver N j ⊗ₘ projectionOver N j)) _
    ((Over.map (Spec.algebraMap R K)).map μ[H.X] ≫ projectionOver N j) ?_
  have hμ : μ[H.X] ≫ (j ≫ N.genericIso.inv).hom.hom =
      (fst H.X H.X ≫ (j ≫ N.genericIso.inv).hom.hom) *
        (snd H.X H.X ≫ (j ≫ N.genericIso.inv).hom.hom) := by
    rw [MonObj.mul_eq_mul, MonObj.mul_comp]
  simp only [Category.assoc]
  rw [projectionOver_fac, map_comp_genericOver, hμ, map_mul, ← map_comp_genericOver, ← map_comp_genericOver, CategoryTheory.Hom.mul_def,
    squareComparison, tensorHom_comp_tensorHom_assoc, projectionOver_fac, lift_map_assoc]

omit [IsDiscreteValuationRing R] in
/-- The inverse of the integral model restricts to the closure. -/
theorem exists_closureInv :
    ∃ w : closureOver N j ⟶ closureOver N j,
      w ≫ inclusionOver N j = inclusionOver N j ≫ ι[N.group.X] := by
  refine exists_over_factor_of_schematic_precomp (inclusionOver N j)
    (projectionOver N j) _ ((Over.map (Spec.algebraMap R K)).map ι[H.X] ≫ projectionOver N j) ?_
  have hι : ι[H.X] ≫ (j ≫ N.genericIso.inv).hom.hom =
      (𝟙 H.X ≫ (j ≫ N.genericIso.inv).hom.hom)⁻¹ := by
    rw [GrpObj.inv_eq_inv, GrpObj.inv_comp]
  rw [projectionOver_fac_assoc, Category.assoc, projectionOver_fac, map_comp_genericOver, hι,
    map_inv, ← map_comp_genericOver, CategoryTheory.Hom.inv_def, CategoryTheory.Functor.map_id,
    Category.id_comp]

/-- The restricted unit. -/
def closureOne : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ closureOver N j :=
  Classical.choose (exists_closureOne N j)

omit [IsClosedImmersion j.hom.hom.left] [IsDiscreteValuationRing R] in
theorem closureOne_fac : closureOne N j ≫ inclusionOver N j = η[N.group.X] :=
  Classical.choose_spec (exists_closureOne N j)

/-- The restricted multiplication. -/
def closureMul : closureOver N j ⊗ closureOver N j ⟶ closureOver N j :=
  Classical.choose (exists_closureMul N j)

theorem closureMul_fac : closureMul N j ≫ inclusionOver N j =
    (inclusionOver N j ⊗ₘ inclusionOver N j) ≫ μ[N.group.X] :=
  Classical.choose_spec (exists_closureMul N j)

/-- The restricted inverse. -/
def closureInv : closureOver N j ⟶ closureOver N j :=
  Classical.choose (exists_closureInv N j)

omit [IsDiscreteValuationRing R] in
theorem closureInv_fac : closureInv N j ≫ inclusionOver N j = inclusionOver N j ≫ ι[N.group.X] :=
  Classical.choose_spec (exists_closureInv N j)

instance closureGrpObj : GrpObj (closureOver N j) :=
  Langlands.CategoryTheory.GroupObjectDescent.grpObjOfMono (inclusionOver N j)
    (closureOne N j) (closureMul N j) (closureInv N j)
    (closureOne_fac N j) (closureMul_fac N j) (closureInv_fac N j)

instance isMonHom_inclusionOver : IsMonHom (inclusionOver N j) :=
  Langlands.CategoryTheory.GroupObjectDescent.isMonHom_grpObjOfMono (inclusionOver N j)
    (closureOne N j) (closureMul N j) (closureInv N j)
    (closureOne_fac N j) (closureMul_fac N j) (closureInv_fac N j)

/-- The closure as an actual group scheme over `Spec R`. -/
abbrev closureGroup : GroupScheme (Spec (CommRingCat.of R)) := { X := closureOver N j }

/-- The closed inclusion of the closure group scheme into the integral model. -/
def closureInclusion : closureGroup N j ⟶ N.group := Grp.homMk (inclusionOver N j)

theorem closureInclusion_hom_hom : (closureInclusion N j).hom.hom = inclusionOver N j := rfl

/-- The generic group mapped into the generic fibre of the closure: the pullback-adjunction
transpose of the projection onto the closure. -/
def genericToClosureOver :
    H.X ⟶ ((baseChange (Spec.algebraMap R K)).obj (closureGroup N j)).X :=
  (baseChangePointsEquiv (Spec.algebraMap R K) (closureGroup N j) H.X).symm (projectionOver N j)

theorem baseChangePointsEquiv_genericToClosureOver :
    baseChangePointsEquiv (Spec.algebraMap R K) (closureGroup N j) H.X
      (genericToClosureOver N j) = projectionOver N j :=
  MulEquiv.apply_symm_apply _ _

/-- Composing with the base-changed inclusion recovers `j` followed by `N.genericIso⁻¹`. -/
theorem genericToClosureOver_comp :
    genericToClosureOver N j ≫
        ((baseChange (Spec.algebraMap R K)).map (closureInclusion N j)).hom.hom =
      (j ≫ N.genericIso.inv).hom.hom := by
  apply (baseChangePointsEquiv (Spec.algebraMap R K) N.group H.X).injective
  rw [baseChangePointsEquiv_comp, baseChangePointsEquiv_genericToClosureOver,
    closureInclusion_hom_hom, projectionOver_fac, baseChangePointsEquiv_generic]

instance mono_baseChange_closureInclusion :
    Mono ((baseChange (Spec.algebraMap R K)).map (closureInclusion N j)).hom.hom := by
  change Mono ((Over.pullback (Spec.algebraMap R K)).map (inclusionOver N j))
  infer_instance

instance isMonHom_genericToClosureOver : IsMonHom (genericToClosureOver N j) := by
  have : IsMonHom (genericToClosureOver N j ≫
      ((baseChange (Spec.algebraMap R K)).map (closureInclusion N j)).hom.hom) := by
    rw [genericToClosureOver_comp]
    infer_instance
  exact isMonHom_of_comp_mono _
    ((baseChange (Spec.algebraMap R K)).map (closureInclusion N j)).hom.hom

theorem genericToClosureOver_left_fst :
    (genericToClosureOver N j).left ≫
        pullback.fst (closureOver N j).hom (Spec.algebraMap R K) =
      (projectionOver N j).left := by
  have h := congrArg Over.Hom.left (baseChangePointsEquiv_genericToClosureOver N j)
  rw [baseChangePointsEquiv_left] at h
  exact h

instance isClosedImmersion_genericToClosureOver :
    IsClosedImmersion (genericToClosureOver N j).left := by
  have h : (genericToClosureOver N j).left ≫
      ((baseChange (Spec.algebraMap R K)).map (closureInclusion N j)).hom.hom.left =
        j.hom.hom.left ≫ N.genericIso.inv.hom.hom.left := by
    rw [← Over.comp_left, genericToClosureOver_comp]
    rfl
  have : IsClosedImmersion ((genericToClosureOver N j).left ≫
      ((baseChange (Spec.algebraMap R K)).map (closureInclusion N j)).hom.hom.left) := by
    rw [h]
    infer_instance
  exact IsClosedImmersion.of_comp _
    ((baseChange (Spec.algebraMap R K)).map (closureInclusion N j)).hom.hom.left

instance isSchemeTheoreticallyDominant_genericToClosureOver :
    IsSchemeTheoreticallyDominant (genericToClosureOver N j).left := by
  have hsq : IsPullback (𝟙 H.X.left) (genericToClosureOver N j).left (projectionOver N j).left
      (pullback.fst (closureOver N j).hom (Spec.algebraMap R K)) :=
    IsPullback.of_horiz_isIso_mono ⟨by rw [Category.id_comp, genericToClosureOver_left_fst]⟩
  exact IsSchemeTheoreticallyDominant.of_isPullback hsq

instance isIso_genericToClosureOver_left : IsIso (genericToClosureOver N j).left :=
  IsClosedImmersion.isIso_iff_ker_eq_bot.mpr (genericToClosureOver N j).left.ker_eq_bot

instance isIso_genericToClosureOver : IsIso (genericToClosureOver N j) := by
  have : IsIso ((Over.forget _).map (genericToClosureOver N j)) :=
    inferInstanceAs (IsIso (genericToClosureOver N j).left)
  exact isIso_of_reflects_iso (genericToClosureOver N j) (Over.forget _)

/-- The generic group is identified with the generic fibre of the closure. -/
def genericToClosureIso : H ≅ (baseChange (Spec.algebraMap R K)).obj (closureGroup N j) :=
  Grp.mkIso (asIso (genericToClosureOver N j))
    (IsMonHom.one_hom (genericToClosureOver N j)) (IsMonHom.mul_hom (genericToClosureOver N j))

theorem genericToClosureIso_hom_hom_hom :
    (genericToClosureIso N j).hom.hom.hom = genericToClosureOver N j := rfl

/-- The schematic closure as an integral model of `H`. -/
def closureModel : IntegralModel R K H where
  group := closureGroup N j
  affine := isAffineHom_closureOver N j
  flat := flat_closureOver N j
  finiteType := locallyOfFiniteType_closureOver N j
  genericIso := (genericToClosureIso N j).symm

/-- The closed inclusion of the closure, as a model morphism extending `j`. -/
def closureModelHom : (closureModel N j).Hom N j where
  hom := closureInclusion N j
  generic_comm := by
    change _ = (genericToClosureIso N j).inv ≫ j
    rw [Iso.eq_inv_comp]
    apply Grp.hom_ext
    rw [Grp.comp_hom_hom, Grp.comp_hom_hom, genericToClosureIso_hom_hom_hom,
      ← Category.assoc, genericToClosureOver_comp, ← Grp.comp_hom_hom, Category.assoc,
      Iso.inv_hom_id, Category.comp_id]

theorem closureModelHom_isSchematicClosure : (closureModelHom N j).IsSchematicClosure := by
  refine ⟨isClosedImmersion_inclusionOver N j, ?_⟩
  change (genericOver N j).left.imageι.ker = (j.hom.hom.left ≫ N.genericToModel).ker
  exact Scheme.IdealSheafData.ker_subschemeι _

end Group

end Construction

end Langlands.GroupScheme.IntegralModel.SchematicClosureConstruction

namespace Langlands.GroupScheme

/-- Kaletha–Prasad Lemma A.2.1(1) and the group-scheme part of Lemma A.2.3: the schematic closure
of a closed generic subgroup in an integral model over a discrete valuation ring. -/
theorem integralModelSchematicClosure : IntegralModelSchematicClosureStatement.{u} := by
  intro R _ _ _ K _ _ _ G N H j hj
  have : IsClosedImmersion j.hom.hom.left := hj
  exact ⟨_, _, IntegralModel.SchematicClosureConstruction.closureModelHom_isSchematicClosure N j⟩

end Langlands.GroupScheme
