import Langlands.Shimura.Unitary.UnitaryGroupScheme
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Morphisms.Affine

noncomputable section
universe u
open CategoryTheory Opposite AlgebraicGeometry Algebra
open scoped CategoryTheory.MonObj

namespace Langlands.Shimura.AlgebraInvolution.SchemeModel

variable {R A : Type u} [CommRing R] [Ring A] [Algebra R A]
  {κ : Type u} [Fintype κ] (b : Module.Basis κ R A) (σ : AlgebraInvolution R A)

/-- The actual similitude structure morphism is locally of finite presentation. -/
instance groupScheme_locallyOfFinitePresentation :
    LocallyOfFinitePresentation (groupScheme b σ).X.hom := by
  change LocallyOfFinitePresentation (Spec.map
    (CommRingCat.ofHom (algebraMap R (σ.similitudeCoordinateRing b))))
  rw [LocallyOfFinitePresentation.SpecMap_iff]
  change (algebraMap R (σ.similitudeCoordinateRing b)).FinitePresentation
  rw [RingHom.finitePresentation_algebraMap]
  infer_instance

/-- The unitary structure morphism is locally of finite type. -/
instance unitaryGroupScheme_locallyOfFiniteType :
    LocallyOfFiniteType (unitaryGroupScheme b σ).X.hom := by
  rw [← (unitaryInclusion b σ).hom.hom.w]
  infer_instance

/-- Over a Noetherian ring the unitary structure morphism is locally of finite presentation. -/
instance unitaryGroupScheme_locallyOfFinitePresentation [IsNoetherianRing R] :
    LocallyOfFinitePresentation (unitaryGroupScheme b σ).X.hom := by
  infer_instance

/-- Base change of the actual similitude group scheme to an arbitrary scheme over the base. -/
abbrev baseChangedGroupScheme {S : Scheme.{u}} (f : S ⟶ Spec (CommRingCat.of R)) :
    GroupScheme S :=
  (GroupScheme.baseChange f).obj (groupScheme b σ)

/-- Base change of the actual unitary group scheme. -/
abbrev baseChangedUnitaryGroupScheme {S : Scheme.{u}} (f : S ⟶ Spec (CommRingCat.of R)) :
    GroupScheme S :=
  (GroupScheme.baseChange f).obj (unitaryGroupScheme b σ)

variable {S : Scheme.{u}} (f : S ⟶ Spec (CommRingCat.of R))

set_option backward.isDefEq.respectTransparency.types false in
/-- The similitude pullback has affine structure morphism. -/
instance baseChangedGroupScheme_isAffineHom :
    IsAffineHom (baseChangedGroupScheme b σ f).X.hom := by
  change IsAffineHom (Limits.pullback.snd (groupScheme b σ).X.hom f)
  exact MorphismProperty.pullback_snd _ _ inferInstance

/-- The similitude pullback retains local finite presentation. -/
instance baseChangedGroupScheme_locallyOfFinitePresentation :
    LocallyOfFinitePresentation (baseChangedGroupScheme b σ f).X.hom := by
  change LocallyOfFinitePresentation (Limits.pullback.snd (groupScheme b σ).X.hom f)
  infer_instance

set_option backward.isDefEq.respectTransparency.types false in
/-- The unitary pullback has affine structure morphism. -/
instance baseChangedUnitaryGroupScheme_isAffineHom :
    IsAffineHom (baseChangedUnitaryGroupScheme b σ f).X.hom := by
  change IsAffineHom (Limits.pullback.snd (unitaryGroupScheme b σ).X.hom f)
  exact MorphismProperty.pullback_snd _ _ inferInstance

/-- The unitary pullback retains local finite type over any base ring. -/
instance baseChangedUnitaryGroupScheme_locallyOfFiniteType :
    LocallyOfFiniteType (baseChangedUnitaryGroupScheme b σ f).X.hom := by
  change LocallyOfFiniteType (Limits.pullback.snd (unitaryGroupScheme b σ).X.hom f)
  infer_instance

/-- With Noetherian original coefficient ring, every unitary pullback is locally finitely presented. -/
instance baseChangedUnitaryGroupScheme_locallyOfFinitePresentation [IsNoetherianRing R] :
    LocallyOfFinitePresentation (baseChangedUnitaryGroupScheme b σ f).X.hom := by
  change LocallyOfFinitePresentation (Limits.pullback.snd (unitaryGroupScheme b σ).X.hom f)
  infer_instance

/-- The affine similitude pullback is separated. -/
instance baseChangedGroupScheme_isSeparated :
    IsSeparated (baseChangedGroupScheme b σ f).X.hom :=
  IsSeparated.of_isAffineHom _

/-- The affine unitary pullback is separated. -/
instance baseChangedUnitaryGroupScheme_isSeparated :
    IsSeparated (baseChangedUnitaryGroupScheme b σ f).X.hom :=
  IsSeparated.of_isAffineHom _

/-- A locally Noetherian new base gives a locally Noetherian similitude scheme. -/
instance baseChangedGroupScheme_isLocallyNoetherian [IsLocallyNoetherian S] :
    IsLocallyNoetherian (baseChangedGroupScheme b σ f).X.left :=
  LocallyOfFiniteType.isLocallyNoetherian (baseChangedGroupScheme b σ f).X.hom

/-- A locally Noetherian new base gives a locally Noetherian unitary scheme. -/
instance baseChangedUnitaryGroupScheme_isLocallyNoetherian [IsLocallyNoetherian S] :
    IsLocallyNoetherian (baseChangedUnitaryGroupScheme b σ f).X.left :=
  LocallyOfFiniteType.isLocallyNoetherian (baseChangedUnitaryGroupScheme b σ f).X.hom

/-- A Noetherian new base gives a Noetherian similitude scheme. -/
instance baseChangedGroupScheme_isNoetherian [IsNoetherian S] :
    IsNoetherian (baseChangedGroupScheme b σ f).X.left where
  toCompactSpace := QuasiCompact.compactSpace_of_compactSpace
    (baseChangedGroupScheme b σ f).X.hom

/-- A Noetherian new base gives a Noetherian unitary scheme. -/
instance baseChangedUnitaryGroupScheme_isNoetherian [IsNoetherian S] :
    IsNoetherian (baseChangedUnitaryGroupScheme b σ f).X.left where
  toCompactSpace := QuasiCompact.compactSpace_of_compactSpace
    (baseChangedUnitaryGroupScheme b σ f).X.hom

/-- Points of the pullback are the original similitudes with the composed scalar structure. -/
def baseChangedPointsEquiv (T : Over S) :
    (T ⟶ (baseChangedGroupScheme b σ f).X) ≃*
      (σ.baseChange ((algΓ (CommRingCat.of R)).obj ((Over.map f).obj T)).unop).similitudes :=
  (GroupScheme.baseChangePointsEquiv f (groupScheme b σ) T).trans
    (pointsEquiv b σ ((Over.map f).obj T))

/-- Restriction of pullback points is coefficient change on relative global sections. -/
theorem baseChangedPointsEquiv_naturality {T T' : Over S} (a : T' ⟶ T)
    (x : T ⟶ (baseChangedGroupScheme b σ f).X) :
    baseChangedPointsEquiv b σ f T' (a ≫ x) =
      σ.baseChangeMap ((algΓ (CommRingCat.of R)).map ((Over.map f).map a)).unop
        (baseChangedPointsEquiv b σ f T x) := by
  change pointsEquiv b σ _ (GroupScheme.baseChangePointsEquiv f _ _ (a ≫ x)) = _
  rw [GroupScheme.baseChangePointsEquiv_naturality, pointsEquiv_naturality]
  rfl

/-- The multiplier of the pullback, valued in the multiplicative group over the new base. -/
def baseChangedMultiplier : baseChangedGroupScheme b σ f ⟶ (GroupScheme.Gm S).toGrp :=
  (GroupScheme.baseChange f).map (multiplier b σ) ≫ (GroupScheme.Gm.baseChangeIso f).hom

/-- The pullback multiplier is the original scalar multiplier on every test scheme. -/
theorem baseChangedMultiplier_points (T : Over S)
    (x : T ⟶ (baseChangedGroupScheme b σ f).X) :
    GroupScheme.Gm.pointsEquiv S T (x ≫ (baseChangedMultiplier b σ f).hom.hom) =
      (σ.baseChange ((algΓ (CommRingCat.of R)).obj ((Over.map f).obj T)).unop).multiplier
        (baseChangedPointsEquiv b σ f T x) := by
  change GroupScheme.Gm.pointsEquiv S T
    (x ≫ ((GroupScheme.baseChange f).map (multiplier b σ)).hom.hom ≫
      (GroupScheme.Gm.baseChangeIso f).hom.hom.hom) = _
  rw [← Category.assoc, GroupScheme.Gm.pointsEquiv_baseChangeIso_hom,
    GroupScheme.Gm.baseChangeUnitsEquiv_apply, GroupScheme.baseChangePointsEquiv_comp,
    multiplier_points]
  rfl

/-- Points of the unitary pullback are the original unitary elements. -/
def baseChangedUnitaryPointsEquiv (T : Over S) :
    (T ⟶ (baseChangedUnitaryGroupScheme b σ f).X) ≃*
      (σ.baseChange ((algΓ (CommRingCat.of R)).obj ((Over.map f).obj T)).unop).unitary :=
  (GroupScheme.baseChangePointsEquiv f (unitaryGroupScheme b σ) T).trans
    (unitaryPointsEquiv b σ ((Over.map f).obj T))

/-- Restriction of unitary pullback points is the original tensor coefficient map. -/
theorem baseChangedUnitaryPointsEquiv_naturality {T T' : Over S} (a : T' ⟶ T)
    (x : T ⟶ (baseChangedUnitaryGroupScheme b σ f).X) :
    (baseChangedUnitaryPointsEquiv b σ f T' (a ≫ x)).val =
      Units.map (changeCoefficients (A := A)
        ((algΓ (CommRingCat.of R)).map ((Over.map f).map a)).unop.hom).toMonoidHom
        (baseChangedUnitaryPointsEquiv b σ f T x).val := by
  change (unitaryPointsEquiv b σ _ (GroupScheme.baseChangePointsEquiv f _ _ (a ≫ x))).val = _
  rw [GroupScheme.baseChangePointsEquiv_naturality, unitaryPointsEquiv_naturality]
  rfl

/-- The actual base-changed inclusion of the unitary group. -/
def baseChangedUnitaryInclusion :
    baseChangedUnitaryGroupScheme b σ f ⟶ baseChangedGroupScheme b σ f :=
  (GroupScheme.baseChange f).map (unitaryInclusion b σ)

/-- Inclusion of pullback points has multiplier one and preserves the algebra unit. -/
theorem baseChangedUnitaryInclusion_points (T : Over S)
    (x : T ⟶ (baseChangedUnitaryGroupScheme b σ f).X) :
    (σ.baseChange ((algΓ (CommRingCat.of R)).obj ((Over.map f).obj T)).unop).unitaryInclusion
        (baseChangedUnitaryPointsEquiv b σ f T x) =
      baseChangedPointsEquiv b σ f T (x ≫ (baseChangedUnitaryInclusion b σ f).hom.hom) := by
  change _ = pointsEquiv b σ _ (GroupScheme.baseChangePointsEquiv f _ _
    (x ≫ ((GroupScheme.baseChange f).map (unitaryInclusion b σ)).hom.hom))
  rw [GroupScheme.baseChangePointsEquiv_comp]
  exact unitaryInclusion_points b σ _ _

end Langlands.Shimura.AlgebraInvolution.SchemeModel

namespace Langlands.Shimura.CentralSimpleUnitaryData

variable {E K A : Type} [Field E] [NumberField E] [NumberField.IsTotallyReal E]
  [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
  [Algebra E K] [IsQuadraticExtension E K] [Ring A] [Algebra K A] [Algebra E A]
  [IsScalarTower E K A] [Algebra ℚ A] [IsScalarTower ℚ E A] [IsScalarTower ℚ K A]
  {n : ℕ} (D : CentralSimpleUnitaryData E K A n)

/-- The rational similitude group pulled back to an arbitrary rational base scheme. -/
abbrev rationalBaseChange {S : Scheme} (f : S ⟶ Spec (CommRingCat.of ℚ)) : GroupScheme S :=
  AlgebraInvolution.SchemeModel.baseChangedGroupScheme D.rationalBasis
    D.toSecondKindInvolution.rationalInvolution f

/-- The rational unitary group pulled back to an arbitrary rational base scheme. -/
abbrev rationalUnitaryBaseChange {S : Scheme} (f : S ⟶ Spec (CommRingCat.of ℚ)) : GroupScheme S :=
  AlgebraInvolution.SchemeModel.baseChangedUnitaryGroupScheme D.rationalBasis
    D.toSecondKindInvolution.rationalInvolution f

omit [IsScalarTower E K A] in
/-- Both rational pullbacks have affine, separated, quasi-compact and locally finitely
presented structure maps, so in particular are of finite presentation. -/
theorem rationalBaseChanges_geometry {S : Scheme} (f : S ⟶ Spec (CommRingCat.of ℚ)) :
    IsAffineHom (D.rationalBaseChange f).X.hom ∧
    IsSeparated (D.rationalBaseChange f).X.hom ∧
    QuasiCompact (D.rationalBaseChange f).X.hom ∧
    LocallyOfFinitePresentation (D.rationalBaseChange f).X.hom ∧
    IsAffineHom (D.rationalUnitaryBaseChange f).X.hom ∧
    IsSeparated (D.rationalUnitaryBaseChange f).X.hom ∧
    QuasiCompact (D.rationalUnitaryBaseChange f).X.hom ∧
    LocallyOfFinitePresentation (D.rationalUnitaryBaseChange f).X.hom :=
  ⟨inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance⟩

end Langlands.Shimura.CentralSimpleUnitaryData
