import Langlands.GroupScheme.IntegralModel.SchematicClosureProof
import Langlands.AlgebraicGeometry.Picard.GenericSectionSchematicClosure

/-! # Schematic closure of a generic subgroup in an arbitrary ambient group -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.GenericSubgroupClosure

open IntegralModel.SchematicClosureConstruction

/-- A scheme over a Dedekind domain is flat if it receives a quasi-compact
schematically dominant map from a scheme over the fraction field. -/
theorem flat_of_generic_dominance {R K : Type u}
    [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
    {X Y : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of R))
    (q : Y ⟶ Spec (CommRingCat.of K)) (t : Y ⟶ X)
    [QuasiCompact t] [IsSchemeTheoreticallyDominant t]
    (ht : t ≫ p = q ≫ Spec.algebraMap R K) : Flat p := by
  refine (IsZariskiLocalAtSource.iff_of_openCover X.affineCover).mpr fun i => ?_
  let d := pullback.snd t (X.affineCover.f i)
  have : IsSchemeTheoreticallyDominant d := by dsimp [d]; infer_instance
  have : QuasiCompact d := by dsimp [d]; infer_instance
  refine flat_of_appTop_injective (X.affineCover.f i ≫ p) d
    (d.app_injective ⊤) fun r hr => ?_
  have hw : d ≫ (X.affineCover.f i ≫ p) =
      (pullback.fst t (X.affineCover.f i) ≫ q) ≫ Spec.algebraMap R K := by
    dsimp [d]
    rw [← Category.assoc, ← pullback.condition, Category.assoc, ht, Category.assoc]
  rw [hw, Scheme.Hom.comp_appTop, ← Scheme.ΓSpecIso_inv_naturality_assoc,
    CommRingCat.comp_apply]
  have hK : algebraMap R K r ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr hr
  exact (isUnit_iff_ne_zero.mpr hK).map _


section Construction

variable {R K : Type u} [CommRing R] [Field K] [Algebra R K]
  (G : GroupScheme (Spec (CommRingCat.of R)))
  {H : GroupScheme (Spec (CommRingCat.of K))}
  (j : H ⟶ (baseChange (Spec.algebraMap R K)).obj G)

/-- The generic subgroup mapped to the ambient group over `Spec R`. -/
def genericOver : (Over.map (Spec.algebraMap R K)).obj H.X ⟶ G.X :=
  baseChangePointsEquiv (Spec.algebraMap R K) G H.X j.hom.hom

theorem genericOver_left :
    (genericOver G j).left = j.hom.hom.left ≫ pullback.fst G.X.hom (Spec.algebraMap R K) := rfl

theorem baseChangePointsEquiv_generic :
    baseChangePointsEquiv (Spec.algebraMap R K) G H.X j.hom.hom = genericOver G j := rfl

/-- Naturality of the generic map in test schemes over `Spec K`. -/
theorem map_comp_genericOver {T : Over (Spec (CommRingCat.of K))} (a : T ⟶ H.X) :
    (Over.map (Spec.algebraMap R K)).map a ≫ genericOver G j =
      baseChangePointsEquiv (Spec.algebraMap R K) G T (a ≫ j.hom.hom) := by
  rw [baseChangePointsEquiv_naturality, baseChangePointsEquiv_generic]

/-- The schematic closure: the scheme-theoretic image of the generic map, over `Spec R`. -/
def closureOver : Over (Spec (CommRingCat.of R)) :=
  Over.mk ((genericOver G j).left.imageι ≫ G.X.hom)

/-- The closed immersion of the closure into the ambient group. -/
def inclusionOver : closureOver G j ⟶ G.X :=
  Over.homMk (genericOver G j).left.imageι rfl

/-- The generic map with codomain restricted to the closure. -/
def projectionOver : (Over.map (Spec.algebraMap R K)).obj H.X ⟶ closureOver G j :=
  Over.homMk (genericOver G j).left.toImage (by simp [closureOver])

@[reassoc (attr := simp)]
theorem projectionOver_fac : projectionOver G j ≫ inclusionOver G j = genericOver G j :=
  Over.OverMorphism.ext (genericOver G j).left.toImage_imageι

instance isClosedImmersion_inclusionOver : IsClosedImmersion (inclusionOver G j).left :=
  inferInstanceAs (IsClosedImmersion (genericOver G j).left.imageι)

instance mono_inclusionOver : Mono (inclusionOver G j) := Over.mono_of_mono_left _

instance isAffineHom_closureOver [IsAffineHom G.X.hom] : IsAffineHom (closureOver G j).hom :=
  inferInstanceAs (IsAffineHom ((genericOver G j).left.imageι ≫ G.X.hom))

instance locallyOfFiniteType_closureOver [LocallyOfFiniteType G.X.hom] :
    LocallyOfFiniteType (closureOver G j).hom :=
  inferInstanceAs (LocallyOfFiniteType ((genericOver G j).left.imageι ≫ G.X.hom))

instance isAffine_closureOver_left [IsAffineHom G.X.hom] : IsAffine (closureOver G j).left :=
  isAffine_of_isAffineHom (closureOver G j).hom

instance quasiCompact_closureOver [QuasiCompact G.X.hom] : QuasiCompact (closureOver G j).hom :=
  inferInstanceAs (QuasiCompact ((genericOver G j).left.imageι ≫ G.X.hom))

instance isSeparated_closureOver [IsSeparated G.X.hom] : IsSeparated (closureOver G j).hom :=
  inferInstanceAs (IsSeparated ((genericOver G j).left.imageι ≫ G.X.hom))

variable [IsDomain R] [IsFractionRing R K]

instance flat_mapObj (T : Over (Spec (CommRingCat.of K))) :
    Flat ((Over.map (Spec.algebraMap R K)).obj T).hom :=
  inferInstanceAs (Flat (T.hom ≫ Spec.algebraMap R K))

variable [IsClosedImmersion j.hom.hom.left]

instance quasiCompact_genericOver : QuasiCompact (genericOver G j).left := by
  rw [genericOver_left]
  infer_instance

instance quasiCompact_projectionOver : QuasiCompact (projectionOver G j).left :=
  inferInstanceAs (QuasiCompact (genericOver G j).left.toImage)

instance isSchemeTheoreticallyDominant_projectionOver :
    IsSchemeTheoreticallyDominant (projectionOver G j).left := by
  exact Langlands.AlgebraicGeometry.toImage_schemeTheoreticallyDominant (genericOver G j).left

end Construction

section Group

variable {R K : Type u} [CommRing R] [IsDedekindDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K]
  (G : GroupScheme (Spec (CommRingCat.of R)))
  {H : GroupScheme (Spec (CommRingCat.of K))}
  (j : H ⟶ (baseChange (Spec.algebraMap R K)).obj G)
  [IsClosedImmersion j.hom.hom.left]

instance flat_closureOver : Flat (closureOver G j).hom :=
  flat_of_generic_dominance (closureOver G j).hom H.X.hom (projectionOver G j).left
    (Over.w (projectionOver G j))

/-- The terminal morphism out of the generic base; its underlying map is `Spec K → Spec R`. -/
abbrev genericBaseOver :
    (Over.map (Spec.algebraMap R K)).obj (𝟙_ (Over (Spec (CommRingCat.of K)))) ⟶
      𝟙_ (Over (Spec (CommRingCat.of R))) := toUnit _

instance isSchemeTheoreticallyDominant_genericBaseOver :
    IsSchemeTheoreticallyDominant (genericBaseOver (R := R) (K := K)).left := by
  change IsSchemeTheoreticallyDominant (𝟙 _ ≫ Spec.algebraMap R K)
  infer_instance

omit [IsClosedImmersion j.hom.hom.left] [IsDedekindDomain R] in
/-- The unit of the ambient group factors through the closure. -/
theorem exists_closureOne :
    ∃ e : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ closureOver G j,
      e ≫ inclusionOver G j = η[G.X] := by
  refine exists_over_factor_of_schematic_precomp (inclusionOver G j)
    (genericBaseOver (R := R) (K := K)) η[G.X]
    ((Over.map (Spec.algebraMap R K)).map η[H.X] ≫ projectionOver G j) ?_
  have h1 : η[H.X] ≫ j.hom.hom =
      (1 : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ ((baseChange (Spec.algebraMap R K)).obj G).X) := by
    rw [IsMonHom.one_hom, MonObj.one_eq_one]
  rw [Category.assoc, projectionOver_fac, map_comp_genericOver, h1, map_one,
    CategoryTheory.Hom.one_def]

/-- The comparison from the base change of the generic square to the ambient square. -/
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
        (projectionOver G j ⊗ₘ projectionOver G j)).left := by
  have := ImageGeneration.isSchemeTheoreticallyDominant_tensorHom (projectionOver G j)
  rw [Over.comp_left]
  infer_instance

/-- The multiplication of the ambient group restricts to the closure. -/
theorem exists_closureMul :
    ∃ m : closureOver G j ⊗ closureOver G j ⟶ closureOver G j,
      m ≫ inclusionOver G j = (inclusionOver G j ⊗ₘ inclusionOver G j) ≫ μ[G.X] := by
  refine exists_over_factor_of_schematic_precomp (inclusionOver G j)
    (squareComparison ≫ (projectionOver G j ⊗ₘ projectionOver G j)) _
    ((Over.map (Spec.algebraMap R K)).map μ[H.X] ≫ projectionOver G j) ?_
  have hμ : μ[H.X] ≫ j.hom.hom =
      (fst H.X H.X ≫ j.hom.hom) *
        (snd H.X H.X ≫ j.hom.hom) := by
    rw [MonObj.mul_eq_mul, MonObj.mul_comp]
  simp only [Category.assoc]
  rw [projectionOver_fac, map_comp_genericOver, hμ, map_mul, ← map_comp_genericOver,
    ← map_comp_genericOver, CategoryTheory.Hom.mul_def,
    squareComparison, tensorHom_comp_tensorHom_assoc, projectionOver_fac, lift_map_assoc]

omit [IsDedekindDomain R] [IsFractionRing R K] in
/-- The inverse of the ambient group restricts to the closure. -/
theorem exists_closureInv :
    ∃ w : closureOver G j ⟶ closureOver G j,
      w ≫ inclusionOver G j = inclusionOver G j ≫ ι[G.X] := by
  refine exists_over_factor_of_schematic_precomp (inclusionOver G j)
    (projectionOver G j) _ ((Over.map (Spec.algebraMap R K)).map ι[H.X] ≫ projectionOver G j) ?_
  have hι : ι[H.X] ≫ j.hom.hom =
      (𝟙 H.X ≫ j.hom.hom)⁻¹ := by
    rw [GrpObj.inv_eq_inv, GrpObj.inv_comp]
  rw [projectionOver_fac_assoc, Category.assoc, projectionOver_fac, map_comp_genericOver, hι,
    map_inv, ← map_comp_genericOver, CategoryTheory.Hom.inv_def, CategoryTheory.Functor.map_id,
    Category.id_comp]

/-- The restricted unit. -/
def closureOne : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ closureOver G j :=
  Classical.choose (exists_closureOne G j)

omit [IsClosedImmersion j.hom.hom.left] [IsDedekindDomain R] in
theorem closureOne_fac : closureOne G j ≫ inclusionOver G j = η[G.X] :=
  Classical.choose_spec (exists_closureOne G j)

/-- The restricted multiplication. -/
def closureMul : closureOver G j ⊗ closureOver G j ⟶ closureOver G j :=
  Classical.choose (exists_closureMul G j)

theorem closureMul_fac : closureMul G j ≫ inclusionOver G j =
    (inclusionOver G j ⊗ₘ inclusionOver G j) ≫ μ[G.X] :=
  Classical.choose_spec (exists_closureMul G j)

/-- The restricted inverse. -/
def closureInv : closureOver G j ⟶ closureOver G j :=
  Classical.choose (exists_closureInv G j)

omit [IsDedekindDomain R] [IsFractionRing R K] in
theorem closureInv_fac : closureInv G j ≫ inclusionOver G j = inclusionOver G j ≫ ι[G.X] :=
  Classical.choose_spec (exists_closureInv G j)

instance closureGrpObj : GrpObj (closureOver G j) :=
  Langlands.CategoryTheory.GroupObjectDescent.grpObjOfMono (inclusionOver G j)
    (closureOne G j) (closureMul G j) (closureInv G j)
    (closureOne_fac G j) (closureMul_fac G j) (closureInv_fac G j)

instance isMonHom_inclusionOver : IsMonHom (inclusionOver G j) :=
  Langlands.CategoryTheory.GroupObjectDescent.isMonHom_grpObjOfMono (inclusionOver G j)
    (closureOne G j) (closureMul G j) (closureInv G j)
    (closureOne_fac G j) (closureMul_fac G j) (closureInv_fac G j)

/-- The closure as an actual group scheme over `Spec R`. -/
abbrev closureGroup : GroupScheme (Spec (CommRingCat.of R)) := { X := closureOver G j }

/-- The closed inclusion of the closure group scheme into the ambient group. -/
def closureInclusion : closureGroup G j ⟶ G := Grp.homMk (inclusionOver G j)

theorem closureInclusion_hom_hom : (closureInclusion G j).hom.hom = inclusionOver G j := rfl

/-- The generic group mapped into the generic fibre of the closure: the pullback-adjunction
transpose of the projection onto the closure. -/
def genericToClosureOver :
    H.X ⟶ ((baseChange (Spec.algebraMap R K)).obj (closureGroup G j)).X :=
  (baseChangePointsEquiv (Spec.algebraMap R K) (closureGroup G j) H.X).symm (projectionOver G j)

theorem baseChangePointsEquiv_genericToClosureOver :
    baseChangePointsEquiv (Spec.algebraMap R K) (closureGroup G j) H.X
      (genericToClosureOver G j) = projectionOver G j :=
  MulEquiv.apply_symm_apply _ _

/-- Composing with the base-changed inclusion recovers `j`. -/
theorem genericToClosureOver_comp :
    genericToClosureOver G j ≫
        ((baseChange (Spec.algebraMap R K)).map (closureInclusion G j)).hom.hom =
      j.hom.hom := by
  apply (baseChangePointsEquiv (Spec.algebraMap R K) G H.X).injective
  rw [baseChangePointsEquiv_comp, baseChangePointsEquiv_genericToClosureOver,
    closureInclusion_hom_hom, projectionOver_fac, baseChangePointsEquiv_generic]

instance mono_baseChange_closureInclusion :
    Mono ((baseChange (Spec.algebraMap R K)).map (closureInclusion G j)).hom.hom := by
  change Mono ((Over.pullback (Spec.algebraMap R K)).map (inclusionOver G j))
  infer_instance

instance isMonHom_genericToClosureOver : IsMonHom (genericToClosureOver G j) := by
  have : IsMonHom (genericToClosureOver G j ≫
      ((baseChange (Spec.algebraMap R K)).map (closureInclusion G j)).hom.hom) := by
    rw [genericToClosureOver_comp]
    infer_instance
  exact isMonHom_of_comp_mono _
    ((baseChange (Spec.algebraMap R K)).map (closureInclusion G j)).hom.hom

theorem genericToClosureOver_left_fst :
    (genericToClosureOver G j).left ≫
        pullback.fst (closureOver G j).hom (Spec.algebraMap R K) =
      (projectionOver G j).left := by
  have h := congrArg Over.Hom.left (baseChangePointsEquiv_genericToClosureOver G j)
  rw [baseChangePointsEquiv_left] at h
  exact h

instance isClosedImmersion_genericToClosureOver :
    IsClosedImmersion (genericToClosureOver G j).left := by
  have h : (genericToClosureOver G j).left ≫
      ((baseChange (Spec.algebraMap R K)).map (closureInclusion G j)).hom.hom.left =
        j.hom.hom.left := by
    rw [← Over.comp_left, genericToClosureOver_comp]
  have : IsClosedImmersion ((genericToClosureOver G j).left ≫
      ((baseChange (Spec.algebraMap R K)).map (closureInclusion G j)).hom.hom.left) := by
    rw [h]
    infer_instance
  exact IsClosedImmersion.of_comp _
    ((baseChange (Spec.algebraMap R K)).map (closureInclusion G j)).hom.hom.left

instance isSchemeTheoreticallyDominant_genericToClosureOver :
    IsSchemeTheoreticallyDominant (genericToClosureOver G j).left := by
  have hsq : IsPullback (𝟙 H.X.left) (genericToClosureOver G j).left (projectionOver G j).left
      (pullback.fst (closureOver G j).hom (Spec.algebraMap R K)) :=
    IsPullback.of_horiz_isIso_mono ⟨by rw [Category.id_comp, genericToClosureOver_left_fst]⟩
  exact IsSchemeTheoreticallyDominant.of_isPullback hsq

instance isIso_genericToClosureOver_left : IsIso (genericToClosureOver G j).left :=
  IsClosedImmersion.isIso_iff_ker_eq_bot.mpr (genericToClosureOver G j).left.ker_eq_bot

instance isIso_genericToClosureOver : IsIso (genericToClosureOver G j) := by
  have : IsIso ((Over.forget _).map (genericToClosureOver G j)) :=
    inferInstanceAs (IsIso (genericToClosureOver G j).left)
  exact isIso_of_reflects_iso (genericToClosureOver G j) (Over.forget _)

/-- The generic group is identified with the generic fibre of the closure. -/
def genericToClosureIso : H ≅ (baseChange (Spec.algebraMap R K)).obj (closureGroup G j) :=
  Grp.mkIso (asIso (genericToClosureOver G j))
    (IsMonHom.one_hom (genericToClosureOver G j)) (IsMonHom.mul_hom (genericToClosureOver G j))

theorem genericToClosureIso_hom_hom_hom :
    (genericToClosureIso G j).hom.hom.hom = genericToClosureOver G j := rfl


/-- The generic identification intertwines the closure inclusion with the given subgroup. -/
theorem genericToClosureIso_hom_comp :
    (genericToClosureIso G j).hom ≫
      (baseChange (Spec.algebraMap R K)).map (closureInclusion G j) = j := by
  apply Grp.hom_ext
  exact genericToClosureOver_comp G j

omit [IsDedekindDomain R] [IsFractionRing R K] [IsClosedImmersion j.hom.hom.left] in
/-- The inclusion cuts out exactly the kernel ideal of the original generic map. -/
theorem inclusionOver_ker :
    (inclusionOver G j).left.ker = (genericOver G j).left.ker :=
  Scheme.IdealSheafData.ker_subschemeι _

end Group

end Langlands.GroupScheme.GenericSubgroupClosure
