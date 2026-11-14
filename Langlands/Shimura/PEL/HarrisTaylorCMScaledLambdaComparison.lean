import Langlands.Cohomology.RightDerivedAdditive
import Langlands.Shimura.PEL.HarrisTaylorCMGeometricLevelCosets
import Langlands.Shimura.PEL.HarrisTaylorCMScaledGaloisCohomology
import Langlands.Shimura.PEL.HarrisTaylorCMLevelTransportLaws
import Langlands.Shimura.PEL.HarrisTaylorCMScaledDescent
import Langlands.Shimura.PEL.HarrisTaylorCMGeometricGaloisCohomology
import Langlands.Shimura.PEL.HarrisCoefficientPrimeValuation

/-! # The `λ`-adic cohomology over scaled levels and at the levels

The functor `cmHarrisScaledLambdaCohomology` of the scaled level `X` has at `X` the same
`λ`-adic cohomology `K_λ ⊗ lim_k H^d(X̄_U, W_k)` as `cmHarrisLambdaCohomology` at the level `U` of
`X`: at every torsion stage the two Galois actions on `H^d(X̄_U, W_k)` coincide. This module builds
these identifications `ψ_X` and computes the maps `T(f) = ψ_Y⁻¹ ≫ F(f) ≫ ψ_X` they induce for
morphisms of scaled levels `f : X ⟶ Y` of the same level: raising the exponent from `n` to `n'`
acts by `ℓ ^ (n' - n)`, shifting both exponents does not change `T`, and a self-morphism by an
element of the level acts trivially. See `HarrisTaylorCMScaledLambdaComparison.md`.
-/

noncomputable section

universe u v wS wR wX wZ uK uO uL uV

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped TensorProduct

set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

/-! ## Additivity of right derived functors -/

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [Abelian C] [HasInjectiveResolutions C]

/-- Taking injective resolutions is additive: the descents of `f + g` and of `f` plus `g` lift
the same morphism, so they are homotopic. -/
instance injectiveResolutions_additive : (injectiveResolutions C).Additive where
  map_add {X Y f g} := by
    change (HomotopyCategory.quotient _ _).map (InjectiveResolution.desc (f + g) _ _) =
      (HomotopyCategory.quotient _ _).map (InjectiveResolution.desc f _ _) +
        (HomotopyCategory.quotient _ _).map (InjectiveResolution.desc g _ _)
    rw [← Functor.map_add]
    apply HomotopyCategory.eq_of_homotopy
    apply InjectiveResolution.descHomotopy (f + g)
    · exact InjectiveResolution.desc_commutes _ _ _
    · rw [Preadditive.comp_add, InjectiveResolution.desc_commutes,
        InjectiveResolution.desc_commutes, Functor.map_add, Preadditive.add_comp]

variable {D : Type*} [Category D] [Abelian D]

/-- The right derived functor of an additive functor, with values in the homotopy category, is
additive. -/
instance Functor.rightDerivedToHomotopyCategory_additive (F : C ⥤ D) [F.Additive] :
    F.rightDerivedToHomotopyCategory.Additive := by
  unfold Functor.rightDerivedToHomotopyCategory
  infer_instance

end CategoryTheory

/-! ## Cohomological pullback with coefficients -/

namespace Langlands.Geometry.EtaleDerivedSections

/-- Small étale cohomology with module coefficients is additive. -/
instance cohomology_additive (X : Scheme.{u}) (R : Type u) [CommRing R] (n : ℕ) :
    (cohomology X R n).Additive := by
  unfold cohomology
  infer_instance

end Langlands.Geometry.EtaleDerivedSections

namespace Langlands.Geometry.EtaleDerivedGlobalPullback

open EtaleInverseImage EtaleDerivedSections

variable {X Z : Scheme.{u}} (R : Type u) [CommRing R]
  [HasDerivedCategory.{wX} (ModuleSheaf X R)]
  [HasDerivedCategory.{wZ} (ModuleSheaf Z R)]
  [HasDerivedCategory.{wR} (ModuleCat.{u} R)]

/-- Cohomological pullback with coefficients along `f`, with coefficient map
`(inverseImageCongr e) ≫ α` for an equality `e : f = f'`, is the pullback along `f'` with
coefficient map `α`. -/
theorem cohomologyPullbackWithCoefficients_congr {f f' : Z ⟶ X} (e : f = f') (q : ℕ)
    {F : ModuleSheaf X R} {G : ModuleSheaf Z R} (α : (inverseImage f' R).obj F ⟶ G) :
    cohomologyPullbackWithCoefficients f R q ((inverseImageCongr R e).hom.app F ≫ α) =
      cohomologyPullbackWithCoefficients f' R q α := by
  subst e
  simp only [inverseImageCongr_refl, Iso.refl_hom, NatTrans.id_app, Category.id_comp]

/-- Along the identity, cohomological pullback with coefficient map `inverseImageId ≫ β` is the
cohomology of `β`. -/
theorem cohomologyPullbackWithCoefficients_id (q : ℕ) {F G : ModuleSheaf X R} (β : F ⟶ G) :
    cohomologyPullbackWithCoefficients (𝟙 X) R q ((inverseImageId R X).hom.app F ≫ β) =
      (cohomology X R q).map β := by
  rw [cohomologyPullbackWithCoefficients, Functor.map_comp, cohomologyPullback_id_assoc]

/-- Cohomological pullback with coefficients is additive in the coefficient map. -/
theorem cohomologyPullbackWithCoefficients_nsmul (f : Z ⟶ X) (q : ℕ) {F : ModuleSheaf X R}
    {G : ModuleSheaf Z R} (n : ℕ) (α : (inverseImage f R).obj F ⟶ G) :
    cohomologyPullbackWithCoefficients f R q (n • α) =
      n • cohomologyPullbackWithCoefficients f R q α := by
  rw [cohomologyPullbackWithCoefficients, cohomologyPullbackWithCoefficients,
    Functor.map_nsmul, Preadditive.comp_nsmul]

end Langlands.Geometry.EtaleDerivedGlobalPullback

namespace Langlands.Geometry.EtaleInverseImage

variable {X : Scheme.{u}} (R : Type u) [CommRing R]

/-- Along an étale self-map `φ` equal to the identity, the comparison of inverse image with
restriction, followed by the restriction comparisons for `φ = 𝟙`, is the inverse-image comparison
for `φ = 𝟙`. -/
@[reassoc]
theorem inverseImageIsoRestriction_restrictionCongr_id (φ : X ⟶ X) [Etale φ] (e : φ = 𝟙 X)
    (M : EtaleDerivedSections.ModuleSheaf X R) :
    (inverseImageIsoRestriction φ R).hom.app M ≫
        (EtalePullback.restrictionCongr R e).hom.app M ≫
          (EtalePullback.restrictionId (ModuleCat.{u} R)).hom.app M =
      (inverseImageCongr R e).hom.app M ≫ (inverseImageId R X).hom.app M := by
  have h1 := congrArg (fun t => t.app M) (inverseImageIsoRestriction_congr R e)
  have h2 := congrArg (fun t => t.app M) (inverseImageIsoRestriction_id R X)
  simp only [NatTrans.comp_app] at h1 h2
  rw [← Category.assoc, ← h1, Category.assoc, h2]

end Langlands.Geometry.EtaleInverseImage

/-! ## Extension of scalars and limits of multiples of identities -/

namespace Langlands.Shimura.LatticeGaloisRepresentation

variable {K : Type uK} [Field K] {O : Type uO} [CommRing O] {L : Type uL} [Field L]
  [Algebra O L]

/-- Extension of scalars of Galois actions is additive. -/
instance baseChangeActionFunctor_additive :
    (baseChangeActionFunctor.{uK, uO, uL, uV} (K := K) (O := O) (L := L)).Additive where
  map_add {V V' f g} := by
    apply Action.Hom.ext
    apply ModuleCat.hom_ext
    change (f + g).hom.hom.baseChange L = f.hom.hom.baseChange L + g.hom.hom.baseChange L
    rw [Action.add_hom, ModuleCat.hom_add, LinearMap.baseChange_add]

end Langlands.Shimura.LatticeGaloisRepresentation

namespace CategoryTheory.Limits

/-- The limit of `n` times the identity of a diagram is `n` times the identity of its limit. -/
theorem lim_map_nsmul_id {J : Type*} [Category J] {C : Type*} [Category C] [Preadditive C]
    [HasLimitsOfShape J C] (F : J ⥤ C) (n : ℕ) :
    lim.map (n • 𝟙 F) = n • 𝟙 (lim.obj F) := by
  apply limit.hom_ext
  intro j
  rw [limit.map_π, NatTrans.app_nsmul, NatTrans.id_app, Preadditive.comp_nsmul,
    Preadditive.nsmul_comp, Category.comp_id, Category.id_comp]

end CategoryTheory.Limits

/-! ## The comparison at the scaled levels -/

namespace Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel

open NumberField _root_.Algebra Langlands.AbelianScheme HarrisPolarizedWeilLevel
open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules
open Langlands.Shimura.Coefficients Langlands.Geometry
open EtaleInverseImage EtaleGeometricDiagram EtaleDerivedGlobalPullback
open Langlands.Global AdelicFunctoriality
open scoped CategoryTheory.Prod

variable {E F A : Type}
  [Field E] [NumberField E] [IsTotallyReal E]
  [Field F] [NumberField F] [IsTotallyComplex F] [IsCMField F]
  [Algebra E F] [IsQuadraticExtension E F]
  [Ring A] [Algebra E A] [Algebra F A] [IsScalarTower E F A]
  [Algebra ℚ A] [IsScalarTower ℚ E A] [IsScalarTower ℚ F A]
  {n : ℕ} (D : CentralSimpleUnitaryData E F A n)
  {L : Type} [Field L] [NumberField L] [IsCMField L]
  [IsQuadraticExtension ℚ L] [Algebra L F]
  {τ₀ : L →+* ℂ}
  (C : HarrisSignatureCharts D.toSecondKindInvolution n
    (harrisCMSection E (algebraMap L F) τ₀))
  (preservation : pullbackTensorComparisonIsIsoStatement.{0})
  (composition : PullbackTensorCompositionStatement.{0})
  (unitCoherence : PullbackTensorUnitCoherenceStatement.{0})
  (associativity : ExplicitPullbackTensorAssociativityStatement.{0})
  (comparison : TensorMonoidalLeftUnitorComparisonStatement.{0})
  (symmetry : PullbackTensorSymmetryStatement.{0})
  (stability : PicardZeroPullbackStatement.{0})
  (square : MumfordBundlePicardZeroStatement.{0})
  (universality : PicardZeroUniversalBaseChangeStatement.{0})
  (dualityNaturality : DualAbelianBaseChangeNaturalityStatement.{0})
  (polarizationStability : PolarizationBaseChangeStatement.{0})
  (compatibility : RelativeFiniteWeilTransitionStatement.{0})
  (h : Global.RationalProfiniteIntegerAdeleComparison)
  (htor : TorsionFiniteEtaleStatement.{0})

open Langlands.AlgebraicGeometry

variable (q : CMRepresentabilityStatement D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality dualityNaturality
  polarizationStability compatibility h htor)

local notation "Galois" => (AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F)
local notation "schemes" => cmSchemeTower D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q
local notation "overTower" => representedCMOverTower D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor
  (chosenCMLevelRepresentation D C preservation composition unitCoherence associativity
    comparison symmetry stability square universality dualityNaturality polarizationStability
    compatibility h htor q)
local notation "geometricSchemes" => cmGeometricSchemeTower D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q
local notation "projection" => cmGeometricProjection D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q
local notation "galoisMap" => cmGeometricGaloisMap D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q

variable [Module.Finite ℚ A]
  {K : Type} [Field K] [NumberField K] (p : Global.FinitePlace ℚ)
  {W : Type} [AddCommGroup W] [Module K W] [Module.Finite K W]
  (ρ : (D.rationalInvolution.baseChange K).AlgebraicRepresentation W)

local notation "Rcoeff" => HarrisCoefficientIntegers K p

variable (existence : RelativeDualSchemeExistenceStatement.{0})
  (geometry : RelativeDualSchemeGeometryStatement.{0})
  (hRigid : ∀ U : SmallCMLevel D, CMGeometricCoarseRigidity D C preservation composition
    unitCoherence associativity comparison symmetry stability square universality
    compatibility h htor U.obj)

local notation "ℓ" => harrisCoefficientPrime p
local notation "hℓ" => harrisCoefficientPrime_ne_zero p
local notation "system" U:max => cmHarrisCoefficientSystem D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q U ρ p ℓ hℓ existence geometry
  (hRigid U)
local notation "geometricSystem" U:max => cmHarrisGeometricCoefficientSystem D C preservation
  composition unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q U ρ p ℓ hℓ
  existence geometry (hRigid U)
local notation "Ccoeff" U:max => cmGeometricGaloisInverseImageIso D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q U Rcoeff
local notation "transportMap" => cmHarrisTransportSheafMap D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q existence geometry hRigid p ρ
local notation "stageMap" => cmHarrisStageTransportMap D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q existence geometry hRigid p ρ
local notation "geometricGaloisSchemes" => cmScaledGeometricGaloisSchemes D C preservation
  composition unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q p ρ
local notation "galoisCoefficients" => cmHarrisScaledGeometricGaloisCoefficientDiagram D C
  preservation composition unitCoherence associativity comparison symmetry stability square
  universality dualityNaturality polarizationStability compatibility h htor q p ρ existence
  geometry hRigid

/-! ### Transitions of the scaled geometric coefficient diagram -/

/-- The arrow `((f, κ), σ)` of the index category of scaled levels, stages and Galois elements. -/
abbrev cmScaledGaloisArrow {X Y : CMScaledLevel D ρ p} (f : X ⟶ Y) {k k' : ℕᵒᵖ} (κ : k ⟶ k')
    (σ : Galois) :
    ((((op Y, k), SingleObj.star Galois)) : CMScaledGaloisIndex D p ρ) ⟶
      ((op X, k'), SingleObj.star Galois) :=
  ⟨⟨f.op, κ⟩, σ⟩

/-- For a morphism of scaled levels with the same level `U` whose geometric tower map is the
identity, the scheme map of the arrow `((f, κ), σ)` is the raw Galois map `g_σ`. -/
theorem cmScaledGeometricGaloisSchemes_map_sameLevel (U : SmallCMLevel D) {s s' : ℕ}
    (f : (⟨U, s⟩ : CMScaledLevel D ρ p) ⟶ ⟨U, s'⟩) {k k' : ℕᵒᵖ} (κ : k ⟶ k') (σ : Galois)
    (hgeom : (geometricSchemes).map (CMScaledLevel.Hom.hom f) = 𝟙 _) :
    ((geometricGaloisSchemes).map (cmScaledGaloisArrow D p ρ f κ σ)).unop =
      (galoisMap σ).app U := by
  change (galoisMap σ).app U ≫ (geometricSchemes).map (CMScaledLevel.Hom.hom f) = _
  rw [hgeom, Category.comp_id]

set_option linter.unusedVariables false in
/-- The transition of the scaled geometric coefficient diagram along an arrow `a`, unfolded: the
square comparison of inverse images, followed by the inverse image along the geometric
projection of the comparison of inverse image with restriction and of the transport map. -/
theorem cmHarrisScaledGeometricGaloisCoefficientDiagram_map_eq
    {i j : CMScaledGaloisIndex D p ρ} (a : i ⟶ j)
    [hE : Etale ((schemes).map (CMScaledLevel.Hom.hom a.1.1.unop))] :
    (galoisCoefficients).map a =
      squareInverseImageMap Rcoeff ((projection).app i.1.1.unop.level)
          ((projection).app j.1.1.unop.level)
          ((schemes).map (CMScaledLevel.Hom.hom a.1.1.unop))
          ((galoisMap a.2).app j.1.1.unop.level ≫
            (geometricSchemes).map (CMScaledLevel.Hom.hom a.1.1.unop))
          (diagramProjection_square (cmScaledGeometricGaloisProjection D C preservation
            composition unitCoherence associativity comparison symmetry stability square
            universality dualityNaturality polarizationStability compatibility h htor q p ρ) a)
          ((system i.1.1.unop.level).obj i.1.2) ≫
        (inverseImage ((projection).app j.1.1.unop.level) Rcoeff).map
          ((inverseImageIsoRestriction ((schemes).map (CMScaledLevel.Hom.hom a.1.1.unop))
              Rcoeff).hom.app ((system i.1.1.unop.level).obj i.1.2) ≫
            transportMap a.1.1.unop (leOfHom a.1.2.unop)
              ((schemes).map (CMScaledLevel.Hom.hom a.1.1.unop)) rfl) :=
  rfl

/-- The transition of the scaled geometric coefficient diagram along `((f, κ), σ)` for a
morphism `f : ⟨U, s⟩ ⟶ ⟨U, s'⟩` of scaled levels with the same level `U` whose tower maps are
identities and whose transport maps are `c` times the stage transitions: `c` times the
identification of inverse images along equal maps, followed by the Galois comparison of `σ` and
the inverse image of the stage transition. -/
theorem cmHarrisScaledGeometricGaloisCoefficientDiagram_map_sameLevel (U : SmallCMLevel D)
    {s s' : ℕ} (f : (⟨U, s⟩ : CMScaledLevel D ρ p) ⟶ ⟨U, s'⟩) {k k' : ℕᵒᵖ} (κ : k ⟶ k')
    (σ : Galois) (c : ℕ)
    (hT : ∀ (hk : k'.unop ≤ k.unop) (φ : (schemes).obj U ⟶ (schemes).obj U)
      (hφ : φ = (schemes).map (CMScaledLevel.Hom.hom f)) (_ : Etale φ) (e : φ = 𝟙 _),
        transportMap f hk φ hφ = c • stageMap U hk φ e)
    (hsch : (schemes).map (CMScaledLevel.Hom.hom f) = 𝟙 _)
    (hgeom : (geometricSchemes).map (CMScaledLevel.Hom.hom f) = 𝟙 _) :
    (galoisCoefficients).map (cmScaledGaloisArrow D p ρ f κ σ) =
      c • ((inverseImageCongr Rcoeff (cmScaledGeometricGaloisSchemes_map_sameLevel D C
          preservation composition unitCoherence associativity comparison symmetry stability
          square universality dualityNaturality polarizationStability compatibility h htor q p
          ρ U f κ σ hgeom)).hom.app _ ≫
        ((Ccoeff U) σ).hom.app ((system U).obj k) ≫
          (inverseImage ((projection).app U) Rcoeff).map ((system U).map κ)) := by
  have hE : Etale ((schemes).map (CMScaledLevel.Hom.hom f)) :=
    cmScaledSchemeDiagram_etale D C preservation composition unitCoherence associativity
      comparison symmetry stability square universality dualityNaturality
      polarizationStability compatibility h htor q existence geometry hRigid p ρ
      ((f.op, κ) : ((op (⟨U, s'⟩ : CMScaledLevel D ρ p), k) : (CMScaledLevel D ρ p)ᵒᵖ × ℕᵒᵖ) ⟶
          (op ⟨U, s⟩, k'))
  have hT' := hT (leOfHom κ.unop) ((schemes).map (CMScaledLevel.Hom.hom f)) rfl hE hsch
  have hs : (galoisMap σ).app U ≫ (geometricSchemes).map (CMScaledLevel.Hom.hom f) =
      (galoisMap σ).app U := by
    rw [hgeom, Category.comp_id]
  have hσ : (galoisMap σ).app U ≫ (projection).app U = (projection).app U :=
    cmGeometricGaloisMap_app_projection D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality dualityNaturality
      polarizationStability compatibility h htor q σ U
  have he' : ((galoisMap σ).app U ≫ (geometricSchemes).map (CMScaledLevel.Hom.hom f)) ≫
      (projection).app U = (projection).app U := by
    rw [hgeom, Category.comp_id, hσ]
  have hκ : (homOfLE (leOfHom κ.unop)).op = κ := rfl
  refine (cmHarrisScaledGeometricGaloisCoefficientDiagram_map_eq D C preservation composition
    unitCoherence associativity comparison symmetry stability square universality
    dualityNaturality polarizationStability compatibility h htor q p ρ existence geometry hRigid
    (cmScaledGaloisArrow D p ρ f κ σ) (hE := hE)).trans ?_
  dsimp only [cmScaledGaloisArrow, Quiver.Hom.unop_op]
  rw [hT', Preadditive.comp_nsmul, CategoryTheory.Functor.map_nsmul, Preadditive.comp_nsmul]
  congr 1
  rw [cmHarrisStageTransportMap, hκ, inverseImageIsoRestriction_restrictionCongr_id_assoc,
    ← Category.assoc ((inverseImageCongr Rcoeff hsch).hom.app _),
    CategoryTheory.Functor.map_comp, ← Category.assoc,
    squareInverseImageMap_base_id Rcoeff _ _ _ _ _ hsch he',
    ← projectionInverseImageIso_congr_top Rcoeff ((projection).app U) hs he' hσ,
    Category.assoc]
  rfl

/-! ### Galois actions and level maps on the stage cohomology -/

variable [∀ U : SmallCMLevel D, HasDerivedCategory.{wS}
    (EtaleDerivedSections.ModuleSheaf ((cmGeometricSchemeTower D C preservation composition
      unitCoherence associativity comparison symmetry stability square universality
      dualityNaturality polarizationStability compatibility h htor q).obj U)
        (HarrisCoefficientIntegers K p))]
  [HasDerivedCategory.{wR} (ModuleCat.{0} (HarrisCoefficientIntegers K p))]

local notation "scaledCohomologyAction" => cmHarrisScaledGaloisCohomologyAction D C
  preservation composition unitCoherence associativity comparison symmetry stability square
  universality dualityNaturality polarizationStability compatibility h htor q p ρ existence
  geometry hRigid
local notation "fixedCohomologyAction" U:max => cmHarrisGeometricGaloisCohomologyAction D C
  preservation composition unitCoherence associativity comparison symmetry stability square
  universality dualityNaturality polarizationStability compatibility h htor q U ρ p ℓ hℓ
  existence geometry (hRigid U)
local notation "stageCohomology" U:max degree:max k:max =>
  (EtaleDerivedSections.cohomology ((cmGeometricSchemeTower D C preservation composition
    unitCoherence associativity comparison symmetry stability square universality
    dualityNaturality polarizationStability compatibility h htor q).obj U)
    (HarrisCoefficientIntegers K p) degree).obj ((geometricSystem U).obj k)

/-- The Galois action at `(X, k)` is cohomological pullback along the scheme map of the arrow
`(𝟙, σ)` with the coefficient transition of that arrow. -/
theorem cmHarrisScaledGaloisCohomologyAction_obj_ρ (degree : ℕ)
    (x : (CMScaledLevel D ρ p)ᵒᵖ × ℕᵒᵖ) (σ : Galois) :
    (((scaledCohomologyAction) degree).obj x).ρ σ =
      cohomologyPullbackWithCoefficients
        ((geometricGaloisSchemes).map (𝟙 x ×ₘ (σ : SingleObj.star Galois ⟶ _))).unop Rcoeff
          degree ((galoisCoefficients).map (𝟙 x ×ₘ (σ : SingleObj.star Galois ⟶ _))) :=
  CoefficientDiagram.cohomologyAction_obj_ρ (galoisCoefficients) degree x σ

/-- The map of a morphism `a` of scaled levels and stages is cohomological pullback along the
scheme map of the arrow `(a, 1)` with the coefficient transition of that arrow. -/
theorem cmHarrisScaledGaloisCohomologyAction_map_hom (degree : ℕ)
    {x y : (CMScaledLevel D ρ p)ᵒᵖ × ℕᵒᵖ} (a : x ⟶ y) :
    (((scaledCohomologyAction) degree).map a).hom =
      cohomologyPullbackWithCoefficients
        ((geometricGaloisSchemes).map (a ×ₘ ((1 : Galois) : SingleObj.star Galois ⟶ _))).unop
          Rcoeff degree
          ((galoisCoefficients).map (a ×ₘ ((1 : Galois) : SingleObj.star Galois ⟶ _))) :=
  CoefficientDiagram.cohomologyAction_map_hom (galoisCoefficients) degree a

/-- At each stage `k`, the Galois action on `H^d(X̄_U, W_k)` over the scaled level `X` is the
Galois action at the level `U` of `X`. -/
theorem cmHarrisScaledGaloisCohomologyAction_obj_ρ_eq (degree : ℕ) (X : CMScaledLevel D ρ p)
    (k : ℕᵒᵖ) (σ : Galois) :
    @Eq (stageCohomology X.level degree k ⟶ stageCohomology X.level degree k)
      ((((scaledCohomologyAction) degree).obj (op X, k)).ρ σ)
      ((((fixedCohomologyAction X.level) degree).obj k).ρ σ) := by
  have hD : (galoisCoefficients).map (𝟙 (op X, k) ×ₘ (σ : SingleObj.star Galois ⟶ _)) =
      (inverseImageCongr Rcoeff (cmScaledGeometricGaloisSchemes_map_sameLevel D C
          preservation composition unitCoherence associativity comparison symmetry stability
          square universality dualityNaturality polarizationStability compatibility h htor q p
          ρ X.level (𝟙 X) (𝟙 k) σ (CategoryTheory.Functor.map_id _ _))).hom.app _ ≫
        ((Ccoeff X.level) σ).hom.app ((system X.level).obj k) := by
    have hD₀ := cmHarrisScaledGeometricGaloisCoefficientDiagram_map_sameLevel D C preservation
      composition unitCoherence associativity comparison symmetry stability square
      universality dualityNaturality polarizationStability compatibility h htor q p ρ
      existence geometry hRigid X.level (𝟙 X) (𝟙 k) σ 1
      (fun hk φ hφ hE e => by
        rw [one_smul]
        exact cmHarrisTransportSheafMap_id_le D C preservation composition unitCoherence
          associativity comparison symmetry stability square universality dualityNaturality
          polarizationStability compatibility h htor q existence geometry hRigid p ρ X hk φ hφ e)
      (CategoryTheory.Functor.map_id _ _) (CategoryTheory.Functor.map_id _ _)
    rw [one_smul, CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id,
      Category.comp_id] at hD₀
    exact hD₀
  rw [cmHarrisScaledGaloisCohomologyAction_obj_ρ, hD]
  refine (cohomologyPullbackWithCoefficients_congr Rcoeff _ degree _).trans ?_
  rw [cmHarrisGeometricGaloisCohomologyAction_obj_ρ,
    cmHarrisGeometricCoefficientGaloisIso_hom_app]

/-- For a morphism `f : ⟨U, s⟩ ⟶ ⟨U, s'⟩` of scaled levels with the same level whose tower maps
are identities and whose transport maps are `c` times the stage transitions, the map of
`(f, κ)` on `H^d(X̄_U, W_k)` is `c` times the cohomology of the stage transition `κ`. -/
theorem cmHarrisScaledGaloisCohomologyAction_map_sameLevel (degree : ℕ) (U : SmallCMLevel D)
    {s s' : ℕ} (f : (⟨U, s⟩ : CMScaledLevel D ρ p) ⟶ ⟨U, s'⟩) {k k' : ℕᵒᵖ} (κ : k ⟶ k')
    (c : ℕ)
    (hT : ∀ (hk : k'.unop ≤ k.unop) (φ : (schemes).obj U ⟶ (schemes).obj U)
      (hφ : φ = (schemes).map (CMScaledLevel.Hom.hom f)) (_ : Etale φ) (e : φ = 𝟙 _),
        transportMap f hk φ hφ = c • stageMap U hk φ e)
    (hsch : (schemes).map (CMScaledLevel.Hom.hom f) = 𝟙 _)
    (hgeom : (geometricSchemes).map (CMScaledLevel.Hom.hom f) = 𝟙 _) :
    @Eq (stageCohomology U degree k ⟶ stageCohomology U degree k')
      (((scaledCohomologyAction) degree).map
        ((f.op ×ₘ κ) : ((op (⟨U, s'⟩ : CMScaledLevel D ρ p), k) :
          (CMScaledLevel D ρ p)ᵒᵖ × ℕᵒᵖ) ⟶ (op ⟨U, s⟩, k'))).hom
      (c • (EtaleDerivedSections.cohomology ((geometricSchemes).obj U) Rcoeff degree).map
        ((geometricSystem U).map κ)) := by
  have hD : (galoisCoefficients).map
      ((f.op ×ₘ κ) ×ₘ ((1 : Galois) : SingleObj.star Galois ⟶ _)) =
      c • ((inverseImageCongr Rcoeff (cmScaledGeometricGaloisSchemes_map_sameLevel D C
          preservation composition unitCoherence associativity comparison symmetry stability
          square universality dualityNaturality polarizationStability compatibility h htor q p
          ρ U f κ 1 hgeom)).hom.app _ ≫
        ((Ccoeff U) 1).hom.app ((system U).obj k) ≫
          (inverseImage ((projection).app U) Rcoeff).map ((system U).map κ)) :=
    cmHarrisScaledGeometricGaloisCoefficientDiagram_map_sameLevel D C preservation composition
      unitCoherence associativity comparison symmetry stability square universality
      dualityNaturality polarizationStability compatibility h htor q p ρ existence geometry
      hRigid U f κ 1 c hT hsch hgeom
  rw [cmHarrisScaledGaloisCohomologyAction_map_hom, hD, cohomologyPullbackWithCoefficients_nsmul]
  congr 1
  refine (cohomologyPullbackWithCoefficients_congr Rcoeff _ degree _).trans ?_
  rw [cmGeometricGaloisInverseImageIso_one, Category.assoc]
  refine (cohomologyPullbackWithCoefficients_congr Rcoeff _ degree _).trans ?_
  exact cohomologyPullbackWithCoefficients_id Rcoeff degree _


/-! ### The identifications at each stage and in the limit -/

/-- At the scaled level `X` and stage `k`, the cohomology `H^d(X̄_U, W_k)` with the Galois action
over scaled levels is the cohomology with the Galois action at the level `U` of `X`: the identity
of `H^d(X̄_U, W_k)` is equivariant. -/
def cmHarrisScaledStageIso (degree : ℕ) (X : CMScaledLevel D ρ p) (k : ℕᵒᵖ) :
    ((scaledCohomologyAction) degree).obj (op X, k) ≅
      ((fixedCohomologyAction X.level) degree).obj k :=
  Action.mkIso (Iso.refl (stageCohomology X.level degree k)) fun σ =>
    (Category.comp_id (X := stageCohomology X.level degree k)
        (Y := stageCohomology X.level degree k) _).trans
      ((cmHarrisScaledGaloisCohomologyAction_obj_ρ_eq D C preservation composition
          unitCoherence associativity comparison symmetry stability square universality
          dualityNaturality polarizationStability compatibility h htor q p ρ existence geometry
          hRigid degree X k σ).trans
        (Category.id_comp (X := stageCohomology X.level degree k)
          (Y := stageCohomology X.level degree k) _).symm)

/-- The identifications at the stages are natural in the stage: the scaled-level and level
inverse systems of Galois actions agree at each scaled level. -/
def cmHarrisScaledStageNatIso (degree : ℕ) (X : CMScaledLevel D ρ p) :
    (Functor.curry.obj ((scaledCohomologyAction) degree)).obj (op X) ≅
      (fixedCohomologyAction X.level) degree :=
  NatIso.ofComponents
    (fun k => cmHarrisScaledStageIso D C preservation composition unitCoherence associativity
      comparison symmetry stability square universality dualityNaturality polarizationStability
      compatibility h htor q p ρ existence geometry hRigid degree X k)
    (fun {k k'} κ => by
      apply Action.Hom.ext
      have h1 := cmHarrisScaledGaloisCohomologyAction_map_sameLevel D C preservation
        composition unitCoherence associativity comparison symmetry stability square
        universality dualityNaturality polarizationStability compatibility h htor q p ρ
        existence geometry hRigid degree X.level (𝟙 X) κ 1
        (fun hk φ hφ hE e => by
          rw [one_smul]
          exact cmHarrisTransportSheafMap_id_le D C preservation composition unitCoherence
            associativity comparison symmetry stability square universality
            dualityNaturality polarizationStability compatibility h htor q existence geometry
            hRigid p ρ X hk φ hφ e)
        (CategoryTheory.Functor.map_id _ _) (CategoryTheory.Functor.map_id _ _)
      rw [one_smul] at h1
      have h2 := cmHarrisGeometricGaloisCohomologyAction_map_hom D C preservation composition
        unitCoherence associativity comparison symmetry stability square universality
        dualityNaturality polarizationStability compatibility h htor q X.level ρ p ℓ hℓ
        existence geometry (hRigid X.level) degree κ
      rw [Action.comp_hom, Action.comp_hom]
      exact (Category.comp_id (X := stageCohomology X.level degree k)
          (Y := stageCohomology X.level degree k') _).trans
        (h1.trans (h2.symm.trans (Category.id_comp (X := stageCohomology X.level degree k)
          (Y := stageCohomology X.level degree k') _).symm)))



/-- The underlying map of a component of the identification is the identity. -/
theorem cmHarrisScaledStageNatIso_hom_app_hom (degree : ℕ) (X : CMScaledLevel D ρ p)
    (k : ℕᵒᵖ) :
    @Eq (stageCohomology X.level degree k ⟶ stageCohomology X.level degree k)
      ((cmHarrisScaledStageNatIso D C preservation composition unitCoherence associativity
        comparison symmetry stability square universality dualityNaturality
        polarizationStability compatibility h htor q p ρ existence geometry hRigid degree
        X).hom.app k).hom (𝟙 _) :=
  rfl

/-- The underlying map of a component of the inverse identification is the identity. -/
theorem cmHarrisScaledStageNatIso_inv_app_hom (degree : ℕ) (X : CMScaledLevel D ρ p)
    (k : ℕᵒᵖ) :
    @Eq (stageCohomology X.level degree k ⟶ stageCohomology X.level degree k)
      ((cmHarrisScaledStageNatIso D C preservation composition unitCoherence associativity
        comparison symmetry stability square universality dualityNaturality
        polarizationStability compatibility h htor q p ρ existence geometry hRigid degree
        X).inv.app k).hom (𝟙 _) :=
  rfl

local notation "stageNatIso" => cmHarrisScaledStageNatIso D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q p ρ existence geometry hRigid

/-- The map of a morphism `f : X ⟶ Y` of scaled levels, read through the identifications at `X`
and `Y`, has at the stage `k` the underlying map of `f` on `H^d(X̄, W_k)`. -/
theorem cmHarrisScaledStageNatIso_conj_app_hom (degree : ℕ) {X Y : CMScaledLevel D ρ p}
    (f : X ⟶ Y) (k : ℕᵒᵖ) :
    @Eq (stageCohomology Y.level degree k ⟶ stageCohomology X.level degree k)
      (((stageNatIso degree Y).inv ≫
          (Functor.curry.obj ((scaledCohomologyAction) degree)).map f.op ≫
            (stageNatIso degree X).hom).app k).hom
      (((scaledCohomologyAction) degree).map
        ((f.op ×ₘ 𝟙 k) : ((op Y, k) : (CMScaledLevel D ρ p)ᵒᵖ × ℕᵒᵖ) ⟶ (op X, k))).hom := by
  rw [NatTrans.comp_app, NatTrans.comp_app, Action.comp_hom, Action.comp_hom]
  exact (Category.id_comp (X := stageCohomology Y.level degree k)
      (Y := stageCohomology X.level degree k) _).trans
    (Category.comp_id (X := stageCohomology Y.level degree k)
      (Y := stageCohomology X.level degree k) _)

/-- For a morphism `f : ⟨U, s⟩ ⟶ ⟨U, s'⟩` of scaled levels with the same level whose tower maps
are identities and whose transport maps are `c` times the stage transitions, the map of `f`
read through the identifications is `c` times the identity. -/
theorem cmHarrisScaledStageNatIso_conj_sameLevel (degree : ℕ) (U : SmallCMLevel D)
    {s s' : ℕ} (f : (⟨U, s⟩ : CMScaledLevel D ρ p) ⟶ ⟨U, s'⟩) (c : ℕ)
    (hT : ∀ {a b : ℕ} (hk : a ≤ b) (φ : (schemes).obj U ⟶ (schemes).obj U)
      (hφ : φ = (schemes).map (CMScaledLevel.Hom.hom f)) (_ : Etale φ) (e : φ = 𝟙 _),
        transportMap f hk φ hφ = c • stageMap U hk φ e)
    (hsch : (schemes).map (CMScaledLevel.Hom.hom f) = 𝟙 _)
    (hgeom : (geometricSchemes).map (CMScaledLevel.Hom.hom f) = 𝟙 _) :
    (stageNatIso degree ⟨U, s'⟩).inv ≫
        (Functor.curry.obj ((scaledCohomologyAction) degree)).map f.op ≫
          (stageNatIso degree ⟨U, s⟩).hom =
      c • 𝟙 ((fixedCohomologyAction U) degree) := by
  apply NatTrans.ext
  funext k
  apply Action.Hom.ext
  refine (cmHarrisScaledStageNatIso_conj_app_hom D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality dualityNaturality
    polarizationStability compatibility h htor q p ρ existence geometry hRigid degree f
    k).trans ?_
  rw [NatTrans.app_nsmul, NatTrans.id_app, Action.nsmul_hom, Action.id_hom]
  refine (cmHarrisScaledGaloisCohomologyAction_map_sameLevel D C preservation composition
    unitCoherence associativity comparison symmetry stability square universality
    dualityNaturality polarizationStability compatibility h htor q p ρ existence geometry hRigid
    degree U f (𝟙 k) c (fun hk φ hφ hE e => hT hk φ hφ hE e) hsch hgeom).trans ?_
  rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]
  rfl


/-- The `λ`-adic cohomology over the scaled level `X` is the `λ`-adic cohomology at the level
`U` of `X`: the extension of scalars of the limit of the identifications at the stages. -/
def cmHarrisScaledLambdaComparison (l : FinitePlacesAbove K p) (degree : ℕ)
    (X : CMScaledLevel D ρ p) :
    (cmHarrisScaledLambdaCohomology D C preservation composition unitCoherence associativity
        comparison symmetry stability square universality dualityNaturality
        polarizationStability compatibility h htor q p ρ existence geometry hRigid l
        degree).obj (op X) ≅
      cmHarrisLambdaCohomology D C preservation composition unitCoherence associativity
        comparison symmetry stability square universality dualityNaturality
        polarizationStability compatibility h htor q X.level ρ p existence geometry
        (hRigid X.level) l degree :=
  letI := harrisCoefficientComponentAlgebra K p l
  (LatticeGaloisRepresentation.baseChangeActionFunctor (L := FiniteCompletion K l.1)).mapIso
    (lim.mapIso (stageNatIso degree X))

/-! ### The transport maps of the identifications -/

variable (l : FinitePlacesAbove K p) (degree : ℕ)

attribute [local instance] harrisCoefficientComponentAlgebra

local notation "scaledLambda" => cmHarrisScaledLambdaCohomology D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q p ρ existence geometry hRigid
  l degree
local notation "lambdaAt" => fun U : SmallCMLevel D => cmHarrisLambdaCohomology D C preservation
  composition unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q U ρ p existence geometry
  (hRigid U) l degree
local notation "lambdaComparison" => cmHarrisScaledLambdaComparison D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q p ρ existence geometry hRigid
  l degree
local notation "baseChange" =>
  LatticeGaloisRepresentation.baseChangeActionFunctor (L := FiniteCompletion K l.1)

/-- The map of a morphism `f : X ⟶ Y` of scaled levels on the `λ`-adic cohomology is the extension
of scalars of the limit of its maps at the stages. -/
theorem cmHarrisScaledLambdaCohomology_map {X Y : CMScaledLevel D ρ p} (f : X ⟶ Y) :
    (scaledLambda).map f.op =
      (baseChange).map (lim.map ((Functor.curry.obj ((scaledCohomologyAction) degree)).map f.op)) :=
  rfl

/-- The identification at `X` is the extension of scalars of the limit of the identifications at
the stages. -/
theorem cmHarrisScaledLambdaComparison_hom (X : CMScaledLevel D ρ p) :
    (lambdaComparison X).hom = (baseChange).map (lim.map (stageNatIso degree X).hom) :=
  rfl

/-- The inverse identification at `X` is the extension of scalars of the limit of the inverse
identifications at the stages. -/
theorem cmHarrisScaledLambdaComparison_inv (X : CMScaledLevel D ρ p) :
    (lambdaComparison X).inv = (baseChange).map (lim.map (stageNatIso degree X).inv) :=
  rfl

/-- The map `ψ_Y⁻¹ ≫ F(f) ≫ ψ_X` of a morphism `f : X ⟶ Y` of scaled levels is the extension of
scalars of the limit of the maps of `f` at the stages, read through the identifications. -/
theorem cmScaledTransport_cmHarrisScaledLambdaComparison {X Y : CMScaledLevel D ρ p}
    (f : X ⟶ Y) :
    cmScaledTransport D ρ p (scaledLambda) (lambdaAt) (lambdaComparison) f =
      (baseChange).map (lim.map ((stageNatIso degree Y).inv ≫
        (Functor.curry.obj ((scaledCohomologyAction) degree)).map f.op ≫
          (stageNatIso degree X).hom)) := by
  rw [cmScaledTransport, cmHarrisScaledLambdaComparison_hom, cmHarrisScaledLambdaComparison_inv,
    cmHarrisScaledLambdaCohomology_map, CategoryTheory.Functor.map_comp,
    CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp,
    CategoryTheory.Functor.map_comp]

/-- If the maps at the stages read through the identifications are `c` times the identity, so is
the map `ψ_Y⁻¹ ≫ F(f) ≫ ψ_X`. -/
theorem cmScaledTransport_cmHarrisScaledLambdaComparison_of_conj (U : SmallCMLevel D)
    {s s' : ℕ} (f : (⟨U, s⟩ : CMScaledLevel D ρ p) ⟶ ⟨U, s'⟩) (c : ℕ)
    (hc : (stageNatIso degree ⟨U, s'⟩).inv ≫
        (Functor.curry.obj ((scaledCohomologyAction) degree)).map f.op ≫
          (stageNatIso degree ⟨U, s⟩).hom =
      c • 𝟙 ((fixedCohomologyAction U) degree)) :
    cmScaledTransport D ρ p (scaledLambda) (lambdaAt) (lambdaComparison) f =
      ((c : ℕ) : FiniteCompletion K l.1) • 𝟙 ((lambdaAt) U) := by
  rw [cmScaledTransport_cmHarrisScaledLambdaComparison, hc, lim_map_nsmul_id,
    CategoryTheory.Functor.map_nsmul, CategoryTheory.Functor.map_id, Nat.cast_smul_eq_nsmul]
  rfl

/-- Raising the exponent of a level from `n` to `n'` acts on the `λ`-adic cohomology, read
through the identifications, by `ℓ ^ (n' - n)`. -/
theorem cmHarrisScaledLambdaComparison_raise :
    CMScaledTransportRaise D ρ p (FiniteCompletion K l.1) (scaledLambda) (lambdaAt)
      (lambdaComparison) := by
  intro U s s' hs
  rw [cmScaledTransport_cmHarrisScaledLambdaComparison_of_conj D C preservation composition
    unitCoherence associativity comparison symmetry stability square universality
    dualityNaturality polarizationStability compatibility h htor q p ρ existence geometry
    hRigid l degree U (CMScaledLevel.raise D ρ p U hs) (ℓ ^ (s' - s))
    (cmHarrisScaledStageNatIso_conj_sameLevel D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality dualityNaturality
      polarizationStability compatibility h htor q p ρ existence geometry hRigid degree U
      (CMScaledLevel.raise D ρ p U hs) (ℓ ^ (s' - s))
      (fun hk φ hφ hE e => cmHarrisTransportSheafMap_raise D C preservation composition
        unitCoherence associativity comparison symmetry stability square universality
        dualityNaturality polarizationStability compatibility h htor q existence geometry
        hRigid p ρ U hs hk φ hφ e)
      (CategoryTheory.Functor.map_id _ _) (CategoryTheory.Functor.map_id _ _)),
    Nat.cast_pow]

/-- A self-morphism of a scaled level by an element of the level acts trivially on the `λ`-adic
cohomology, read through the identifications. -/
theorem cmHarrisScaledLambdaComparison_levelTrivial :
    CMScaledTransportLevelTrivial D ρ p (scaledLambda) (lambdaAt) (lambdaComparison) := by
  intro Y f hf
  have hsch := cmSchemeTower_map_eq_id_of_mem D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality dualityNaturality
    polarizationStability compatibility h htor q (CMScaledLevel.Hom.hom f) hf
  have hgeom := cmGeometricSchemeTower_map_eq_id_of_mem D C preservation composition
    unitCoherence associativity comparison symmetry stability square universality
    dualityNaturality polarizationStability compatibility h htor q (CMScaledLevel.Hom.hom f) hf
  have h1 := cmScaledTransport_cmHarrisScaledLambdaComparison_of_conj D C preservation
    composition unitCoherence associativity comparison symmetry stability square universality
    dualityNaturality polarizationStability compatibility h htor q p ρ existence geometry
    hRigid l degree Y.level (s := Y.scale) (s' := Y.scale) f 1
    (cmHarrisScaledStageNatIso_conj_sameLevel D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality dualityNaturality
      polarizationStability compatibility h htor q p ρ existence geometry hRigid degree Y.level
      (s := Y.scale) (s' := Y.scale) f 1
      (fun hk φ hφ hE e => by
        rw [one_smul]
        exact cmHarrisTransportSheafMap_eq_of_mem D C preservation composition unitCoherence
          associativity comparison symmetry stability square universality dualityNaturality
          polarizationStability compatibility h htor q existence geometry hRigid p ρ Y f hf hk
          φ hφ e)
      hsch hgeom)
  rw [Nat.cast_one, one_smul] at h1
  exact h1

/-- Shifting both exponents of a morphism of scaled levels does not change its action on the
`λ`-adic cohomology, read through the identifications. -/
theorem cmHarrisScaledLambdaComparison_shift :
    CMScaledTransportShift D ρ p (scaledLambda) (lambdaAt) (lambdaComparison) := by
  intro X Y f k₀
  have hℓΛ : ((ℓ : ℕ) : FiniteCompletion K l.1) ≠ 0 :=
    harrisCoefficientPrime_ne_zero_completion p l
  have hraise := cmHarrisScaledLambdaComparison_raise D C preservation composition
    unitCoherence associativity comparison symmetry stability square universality
    dualityNaturality polarizationStability compatibility h htor q p ρ existence geometry
    hRigid l degree
  have hfac : CMScaledLevel.raise D ρ p X.level (Nat.le_add_left X.scale k₀) ≫
      CMScaledLevel.Hom.shift D ρ p f k₀ =
        f ≫ CMScaledLevel.raise D ρ p Y.level (Nat.le_add_left Y.scale k₀) := by
    apply CMScaledLevel.Hom.ext
    exact (Category.id_comp _).trans (Category.comp_id _).symm
  have h1 := congrArg (cmScaledTransport D ρ p (scaledLambda) (lambdaAt) (lambdaComparison)) hfac
  rw [cmScaledTransport_comp, cmScaledTransport_comp,
    hraise X.level (Nat.le_add_left X.scale k₀), hraise Y.level (Nat.le_add_left Y.scale k₀),
    Linear.comp_smul,
    Linear.smul_comp, Category.comp_id, Category.id_comp, Nat.add_sub_cancel,
    Nat.add_sub_cancel] at h1
  exact smul_right_injective _ (pow_ne_zero _ hℓΛ) h1

end Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel
