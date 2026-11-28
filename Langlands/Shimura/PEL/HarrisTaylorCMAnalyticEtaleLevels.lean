import Langlands.Shimura.PEL.HarrisTaylorCMAnalyticTower
import Langlands.Shimura.PEL.HarrisTaylorCMTransporterEtale
import Langlands.Geometry.Analytic.SchemeAnalytificationEtaleSite

/-! # Étale analytic transition objects of the CM tower -/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel

open NumberField _root_.Algebra Langlands.AbelianScheme HarrisPolarizedWeilLevel
open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules
open Langlands.AlgebraicGeometry.FiniteEtale Langlands.GroupScheme

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
  (K : Type) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra F K]

open Langlands.Analytic.SchemeAnalytification
open Langlands.Analytic.SaturatedAtlasPresentation

local notation "fieldOver" => cmFieldOverTower D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality dualityNaturality
  polarizationStability compatibility h htor q K

local notation "schemes" => cmSchemeTower D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q
local notation "fieldSchemes" => cmFieldSchemeTower D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q K
local notation "separatedTower" => cmFieldSeparatedTower D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q K
local notation "anTower" => cmFieldAnalyticTower D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q K

omit [IsUltrametricDist K] [CompleteSpace K] in
/-- An étale represented transporter stays étale after the actual field pullback. -/
theorem cmFieldSchemeTower_map_etale {U V : SmallCMLevel D} (a : V ⟶ U)
    (ha : Etale ((schemes).map a)) : Etale ((fieldSchemes).map a) :=
  MorphismProperty.of_isPullback (P := @Etale)
    (cmFieldSchemeTower_map_isPullback D C preservation composition unitCoherence associativity
      comparison symmetry stability square universality dualityNaturality polarizationStability
      compatibility h htor q K a) ha

omit [IsUltrametricDist K] [CompleteSpace K] in
/-- A surjective represented transporter stays surjective after field pullback. -/
theorem cmFieldSchemeTower_map_surjective {U V : SmallCMLevel D} (a : V ⟶ U)
    (ha : Surjective ((schemes).map a)) : Surjective ((fieldSchemes).map a) :=
  MorphismProperty.of_isPullback (P := @Surjective)
    (cmFieldSchemeTower_map_isPullback D C preservation composition unitCoherence associativity
      comparison symmetry stability square universality dualityNaturality polarizationStability
      compatibility h htor q K a) ha

variable (hEt : ∀ {U V : SmallCMLevel D} (a : V ⟶ U),
  Etale ((cmSchemeTower D C preservation composition unitCoherence associativity comparison
    symmetry stability square universality dualityNaturality polarizationStability compatibility
    h htor q).map a))

/-- At a coarse level, the slice of transporter arrows maps to the category of
separated algebraic étale morphisms of the locally base-changed tower. -/
def cmFieldSeparatedEtaleLevels (U : SmallCMLevel D) :
    Over U ⥤ SeparatedAlgebraicEtale K ((separatedTower).obj U) where
  obj V := MorphismProperty.Over.mk ⊤ ((separatedTower).map V.hom)
    (cmFieldSchemeTower_map_etale D C preservation composition unitCoherence associativity
      comparison symmetry stability square universality dualityNaturality polarizationStability
      compatibility h htor q K V.hom (hEt V.hom))
  map {V W} a := MorphismProperty.Over.homMk ((separatedTower).map a.left) (by
    change (separatedTower).map a.left ≫ (separatedTower).map W.hom =
      (separatedTower).map V.hom
    exact ((separatedTower).map_comp a.left W.hom).symm.trans
      ((separatedTower).congr_map (Over.w a)))
  map_id V := MorphismProperty.Over.Hom.ext ((separatedTower).map_id V.left)
  map_comp a b := MorphismProperty.Over.Hom.ext ((separatedTower).map_comp a.left b.left)

variable (hSmall : StrongEtaleSmallIndexComparisonStatement.{0})

/-- The analytical étale objects and maps of the level slice. In particular, the
objects over the two ends of a Hecke span are given by its original two legs. -/
def cmFieldAnalyticEtaleLevels (U : SmallCMLevel D) : Over U ⥤ EtaleSite ((anTower).obj U) :=
  cmFieldSeparatedEtaleLevels D C preservation composition unitCoherence associativity
    comparison symmetry stability square universality dualityNaturality polarizationStability
    compatibility h htor q K hEt U ⋙
      separatedEtaleAnalytification K ((separatedTower).obj U) hSmall

/-- The same level slice inside the underlying quasi-étale category. -/
def cmFieldAnalyticQuasiEtaleLevels (U : SmallCMLevel D) : Over U ⥤ QuasiEtaleSite ((anTower).obj U) :=
  cmFieldAnalyticEtaleLevels D C preservation composition unitCoherence associativity
    comparison symmetry stability square universality dualityNaturality polarizationStability
    compatibility h htor q K hEt hSmall U ⋙ EtaleSite.toQuasiEtaleSite ((anTower).obj U)

local notation "levels" => cmFieldAnalyticEtaleLevels D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality dualityNaturality
  polarizationStability compatibility h htor q K hEt hSmall

/-- The étale object has exactly the original fine analytification and transporter. -/
@[simp]
theorem cmFieldAnalyticEtaleLevels_obj_hom (U : SmallCMLevel D) (V : Over U) :
    (((levels) U).obj V).hom = (anTower).map V.hom := rfl

/-- The étale transporters analytify to surjections when the represented transporters
are surjective. -/
theorem cmFieldAnalyticEtaleLevels_obj_surjective (U : SmallCMLevel D) (V : Over U)
    (ha : Surjective ((schemes).map V.hom)) :
    Function.Surjective (localizedSpaceFunctor.map (((levels) U).obj V).hom) := by
  let Y := (separatedTower).obj V.left
  let Z := (separatedTower).obj U
  let : LocallyOfFiniteType Y.obj.hom := Y.property.1
  let : IsSeparated Y.obj.hom := Y.property.2
  let : LocallyOfFiniteType Z.obj.hom := Z.property.1
  let : IsSeparated Z.obj.hom := Z.property.2
  let a := (separatedTower).map V.hom
  change Function.Surjective (localizedSpaceFunctor.map
    (Localized.map K Y.obj.hom Z.obj.hom a.hom.left (Over.w a.hom))).hom
  rw [Localized.underlying_map]
  apply Set.range_eq_univ.mp
  have hf : Surjective a.hom.left :=
    cmFieldSchemeTower_map_surjective D C preservation composition unitCoherence associativity
      comparison symmetry stability square universality dualityNaturality polarizationStability
      compatibility h htor q K V.hom ha
  exact (range_analytification K Y.obj.hom Z.obj.hom a.hom.left (Over.w a.hom)).trans
    (by rw [hf.surj.range_eq, Set.preimage_univ])

end Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel
