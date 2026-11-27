import Langlands.Shimura.PEL.HarrisTaylorCMNormalQuotientPremiseStatements
import Langlands.Shimura.PEL.HarrisTaylorCMSublevelConnectedCover
import Langlands.AlgebraicGeometry.LocallyNoetherianComponentSchemes
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap

/-! # Proof of étale-local lifting of normalized CM classes to smaller small levels -/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.AlgebraicGeometry

open _root_.AlgebraicGeometry

/-- Every connected component of a locally Noetherian coproduct of schemes lies in one
summand: its inclusion factors through the inclusion of that summand. -/
theorem exists_componentι_factor_sigmaι {J : Type} (Z : J → Scheme.{0})
    [IsLocallyNoetherian (∐ Z)] (e : _root_.ConnectedComponents (∐ Z : Scheme.{0})) :
    ∃ (d : J) (g : componentScheme (∐ Z) e ⟶ Z d), g ≫ Sigma.ι Z d = componentι (∐ Z) e := by
  obtain ⟨z, rfl⟩ := _root_.ConnectedComponents.surjective_coe e
  let d := ((sigmaMk Z).symm z).1
  have hR : IsClopen ((sigmaMk Z).symm ⁻¹' Set.range (Sigma.mk d)) :=
    isClopen_range_sigmaMk.preimage (sigmaMk Z).symm.continuous
  have hz : z ∈ (sigmaMk Z).symm ⁻¹' Set.range (Sigma.mk d) := ⟨((sigmaMk Z).symm z).2, rfl⟩
  have hsub := hR.connectedComponent_subset hz
  have hrange : Set.range (componentι (∐ Z) (_root_.ConnectedComponents.mk z)) ⊆
      Set.range (Sigma.ι Z d) := by
    rw [Scheme.Opens.range_ι, componentOpen_mk]
    intro w hw
    obtain ⟨w', hw'⟩ := hsub hw
    refine ⟨w', ?_⟩
    rw [← sigmaMk_mk, hw', Homeomorph.apply_symm_apply]
  exact ⟨d, IsOpenImmersion.lift _ _ hrange, IsOpenImmersion.lift_fac _ _ _⟩

end Langlands.AlgebraicGeometry

namespace Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel

open NumberField _root_.Algebra Langlands.AbelianScheme HarrisPolarizedWeilLevel
open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules
open Langlands.AlgebraicGeometry.FiniteEtale Langlands.GroupScheme
open Langlands.AlgebraicGeometry

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

local notation "Bases" => AdmissibleCMBaseCategory D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
local notation "DisBases" => ComponentwiseAdmissibleCMBaseCategory D C preservation
  composition unitCoherence associativity comparison symmetry stability square universality
local notation "component" => componentCMBase D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality
local notation "componentHom" => componentCMBaseHomTo D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
local notation "tower" => unpointedClassTower D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality compatibility h htor
local notation "pull" => unpointedClassTowerPullback D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor
local notation "dispull" => disconnectedClassTowerPullback D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor

/-- Étale-local lifting of normalized CM classes along an inclusion of small levels. -/
theorem cmSublevelEtaleLift :
    CMSublevelEtaleLiftStatement D C preservation composition unitCoherence associativity
      comparison symmetry stability square universality dualityNaturality polarizationStability
      compatibility h htor := by
  intro U' U hle S c
  let c' : ∀ d : _root_.ConnectedComponents S.obj.left, (tower (component S d)).obj U.obj := c
  have key := fun d : _root_.ConnectedComponents S.obj.left =>
    unpointedClassTower_exists_sublevel_etaleCover D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality dualityNaturality
      polarizationStability compatibility h htor (component S d) hle (c' d)
  choose T f hEt hSurj w hw using key
  let Z : _root_.ConnectedComponents S.obj.left → Scheme.{0} := fun d => (T d).obj.left
  have hZ : IsLocallyNoetherian (∐ Z) :=
    (isLocallyNoetherian_iff_openCover (sigmaOpenCover Z)).mpr (fun d => by
      change IsLocallyNoetherian (T d).obj.left
      infer_instance)
  let S₁obj : Over (Spec (.of F)) := Over.mk (Sigma.desc fun d => (T d).obj.hom)
  have : IsLocallyNoetherian S₁obj.left := hZ
  let S₁ : DisBases := ⟨S₁obj, componentwiseAdmissibleCMBase_of_relativeDual D C preservation
    composition unitCoherence associativity comparison symmetry stability square universality
    relativeDualSchemeExistence relativeDualSchemeGeometry S₁obj⟩
  let pl : (∐ Z) ⟶ S.obj.left := Sigma.desc fun d => (f d).hom.left ≫ componentι S.obj.left d
  have hpl : ∀ d, Sigma.ι Z d ≫ pl = (f d).hom.left ≫ componentι S.obj.left d := fun d =>
    Sigma.ι_comp_desc _ d
  let p : S₁ ⟶ S := ObjectProperty.homMk (Over.homMk pl (by
    change pl ≫ S.obj.hom = Sigma.desc fun d => (T d).obj.hom
    apply Sigma.hom_ext
    intro d
    rw [← Category.assoc, hpl, Sigma.ι_comp_desc, Category.assoc]
    exact Over.w (f d).hom))
  have hpleft : p.hom.left = pl := rfl
  have hEtale : Etale p.hom.left := by
    rw [hpleft]
    apply IsZariskiLocalAtSource.sigmaDesc
    intro d
    have := hEt d
    change Etale ((f d).hom.left ≫ componentι S.obj.left d)
    infer_instance
  have hSurjective : Surjective p.hom.left := by
    rw [hpleft]
    apply Surjective.sigmaDesc_of_union_range_eq_univ
    apply Set.eq_univ_of_forall
    intro x
    let d := _root_.ConnectedComponents.mk x
    let xx : componentScheme S.obj.left d := ⟨x, rfl⟩
    obtain ⟨y, hy⟩ := (hSurj d).surj xx
    refine Set.mem_iUnion.mpr ⟨d, y, ?_⟩
    rw [Scheme.Hom.comp_apply]
    change componentι S.obj.left d ((f d).hom.left y) = componentι S.obj.left d xx
    rw [hy]
  have hfac := fun e : _root_.ConnectedComponents S₁.obj.left =>
    exists_componentι_factor_sigmaι Z e
  choose d g hg using hfac
  let G : ∀ e, component S₁ e ⟶ T (d e) := fun e =>
    ObjectProperty.homMk (Over.homMk (g e) (by
      change g e ≫ (T (d e)).obj.hom =
        componentι (∐ Z) e ≫ Sigma.desc fun d => (T d).obj.hom
      rw [← hg e, Category.assoc, Sigma.ι_comp_desc]))
  have he : ∀ e, componentMap p.hom.left e = d e := by
    intro e
    obtain ⟨z, hz⟩ := _root_.ConnectedComponents.surjective_coe e
    let zz : componentScheme S₁.obj.left e := ⟨z, hz⟩
    let y : componentScheme S.obj.left (d e) := (g e ≫ (f (d e)).hom.left) zz
    have h1 : p.hom.left z = componentι S.obj.left (d e) y := by
      have hzz : z = (g e ≫ Sigma.ι Z (d e)) zz := by
        rw [hg e]
        rfl
      have key : (g e ≫ Sigma.ι Z (d e)) ≫ pl =
          (g e ≫ (f (d e)).hom.left) ≫ componentι S.obj.left (d e) := by
        rw [Category.assoc, hpl, Category.assoc]
      calc p.hom.left z = pl ((g e ≫ Sigma.ι Z (d e)) zz) := congrArg (fun q => pl q) hzz
        _ = ((g e ≫ Sigma.ι Z (d e)) ≫ pl) zz := (Scheme.Hom.comp_apply _ _ _).symm
        _ = ((g e ≫ (f (d e)).hom.left) ≫ componentι S.obj.left (d e)) zz := by rw [key]
        _ = componentι S.obj.left (d e) y := Scheme.Hom.comp_apply _ _ _
    calc componentMap p.hom.left e =
        componentMap p.hom.left (_root_.ConnectedComponents.mk z) := congrArg _ hz.symm
      _ = _root_.ConnectedComponents.mk (p.hom.left z) := componentMap_mk _ z
      _ = d e := by
        rw [h1]
        exact y.2
  have hcomp : ∀ e, componentHom p e (d e) (he e) = G e ≫ f (d e) := by
    intro e
    apply ObjectProperty.hom_ext
    apply Over.OverMorphism.ext
    change componentHomTo p.hom.left e (d e) (he e) = g e ≫ (f (d e)).hom.left
    symm
    apply componentHomTo_unique
    rw [hpleft, ← hg e, Category.assoc, Category.assoc, hpl]
  let c₁ : ∀ e : _root_.ConnectedComponents S₁.obj.left,
      (tower (component S₁ e)).obj U'.obj := fun e => (pull (G e)).app U'.obj (w (d e))
  refine ⟨S₁, p, c₁, hEtale, hSurjective, ?_⟩
  funext e
  change (tower (component S₁ e)).map (CompactOpenLevel.inclusion hle) (c₁ e) =
    ((dispull p).app U.obj c') e
  rw [disconnectedClassTowerPullback_app_eq D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality dualityNaturality
    polarizationStability compatibility h htor p U.obj c' e (d e) (he e), hcomp e,
    ← unpointedClassTowerPullback_comp]
  change _ = (pull (G e)).app U.obj ((pull (f (d e))).app U.obj (c' (d e)))
  rw [← hw (d e)]
  exact ((pull (G e)).naturality_apply (CompactOpenLevel.inclusion hle) (w (d e))).symm

end Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel
