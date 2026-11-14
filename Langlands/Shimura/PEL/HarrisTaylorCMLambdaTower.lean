import Langlands.Shimura.PEL.HarrisTaylorCMScaledLambdaComparison
import Langlands.Shimura.PEL.HarrisTaylorCMSmallLevelGaloisIsotypic

/-! # The `λ`-adic cohomology of the CM tower with coefficients `W`: level change, the
finite-adelic action, isotypic parts and their Galois representations

The Library's `λ`-adic cohomology `H^d(S_U ×_F F̄, W)_λ` with Harris's coefficient systems,
as a level-trivial presheaf on small CM levels (descended from scaled levels by inverting `ℓ`),
the tower cohomology `H^d(S, W)_λ = colim_U H^d(S_U ×_F F̄, W)_λ` as a smooth representation of
`GG(A_f)` with the commuting action of `Gal(F̄/F)`, the level Hecke modules, the fixed-vector
comparison as a proposition (Harris–Taylor 2001, III.2), the isotypic parts and multiplicity
spaces (Harris 1999, §5, printed p. 312; Kottwitz 1992, §1, printed p. 655), and their Galois
representations with Euler polynomials (Harris 1999, (5.6), printed p. 313). See
`HarrisTaylorCMLambdaTower.md`.
-/

noncomputable section

universe wS wR uM uV

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

set_option autoImplicit false
set_option quotPrecheck false

namespace Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel

open NumberField _root_.Algebra Langlands.AbelianScheme HarrisPolarizedWeilLevel
open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules
open Langlands.Shimura.Coefficients Langlands.Geometry
open Langlands.Global AdelicFunctoriality
open Langlands.Shimura.CompactOpenLevel Langlands.Shimura.RestrictedLevelColimit
open Langlands.Shimura.SmallLevelGaloisTower
open Langlands.Shimura.IsotypicGaloisAction
open Langlands.Shimura.ContinuousIsotypicGaloisRepresentation
open Langlands.GaloisRepresentation (Objects ClosureEmbedding HasEulerPolynomialAt)
open Langlands.Shimura.DecompositionGroupAction (IsUnramifiedAt geometricFrobenius)

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

variable [Module.Finite ℚ A]
  {K : Type} [Field K] [NumberField K] (p : Global.FinitePlace ℚ)
  {W : Type} [AddCommGroup W] [Module K W] [Module.Finite K W]
  (ρ : (D.rationalInvolution.baseChange K).AlgebraicRepresentation W)
  (existence : RelativeDualSchemeExistenceStatement.{0})
  (geometry : RelativeDualSchemeGeometryStatement.{0})
  (hRigid : ∀ U : SmallCMLevel D, CMGeometricCoarseRigidity D C preservation composition
    unitCoherence associativity comparison symmetry stability square universality
    compatibility h htor U.obj)

variable [∀ U : SmallCMLevel D, HasDerivedCategory.{wS}
    (EtaleDerivedSections.ModuleSheaf ((cmGeometricSchemeTower D C preservation composition
      unitCoherence associativity comparison symmetry stability square universality
      dualityNaturality polarizationStability compatibility h htor q).obj U)
        (HarrisCoefficientIntegers K p))]
  [HasDerivedCategory.{wR} (ModuleCat.{0} (HarrisCoefficientIntegers K p))]

variable (l : FinitePlacesAbove K p) (degree : ℕ)

set_option hygiene false in
local notation "scaledLambda" => cmHarrisScaledLambdaCohomology D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q p ρ existence geometry hRigid
  l degree

set_option hygiene false in
local notation "levelLambda" => fun U : SmallCMLevel D => cmHarrisLambdaCohomology D C
  preservation composition unitCoherence associativity comparison symmetry stability square
  universality dualityNaturality polarizationStability compatibility h htor q U ρ p existence
  geometry (hRigid U) l degree

/-! ## The comparison isomorphisms and their laws -/

set_option hygiene false in
local notation "psiCmp" =>
  cmHarrisScaledLambdaComparison D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q p ρ existence geometry hRigid
  l degree

set_option hygiene false in
local notation "raiseCmp" =>
  cmHarrisScaledLambdaComparison_raise D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q p ρ existence geometry hRigid
  l degree

set_option hygiene false in
local notation "shiftCmp" =>
  cmHarrisScaledLambdaComparison_shift D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q p ρ existence geometry hRigid
  l degree

set_option hygiene false in
local notation "trivCmp" =>
  cmHarrisScaledLambdaComparison_levelTrivial D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q p ρ existence geometry hRigid
  l degree

/-! ## Level change -/

/-- The `λ`-adic cohomology `U ↦ H^d(S_U ×_F F̄, W)_λ` as a presheaf on the transporters of small
CM levels, with values in `K_λ`-linear actions of `Gal(F̄/F)`. -/
def cmHarrisLambdaLevelCohomology :
    (SmallCMLevel D)ᵒᵖ ⥤
      Action (ModuleCat.{0} (FiniteCompletion K l.1)) (Field.absoluteGaloisGroup F) :=
  cmScaledDescent D ρ p (harrisCoefficientPrime_ne_zero_completion p l) (raiseCmp)
    (shiftCmp)

set_option hygiene false in
local notation "Hlev" => cmHarrisLambdaLevelCohomology D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q p ρ existence geometry hRigid
  l degree

/-- Its value at `U` is the Library's `λ`-adic cohomology `H^d(S_U ×_F F̄, W)_λ` at level `U`. -/
theorem cmHarrisLambdaLevelCohomology_obj (U : SmallCMLevel D) :
    (Hlev).obj (op U) = (levelLambda) U := rfl

/-- The map of a transporter `b : V ⟶ U` is `(ℓ ^ e_b)⁻¹ • ψ_⟨U, e_b⟩⁻¹ ≫ G(f_b) ≫ ψ_⟨V, 0⟩`,
for the least admissible exponent `e_b`, the scaled `λ`-adic cohomology `G` and the comparison
isomorphisms `ψ` (`cmHarrisScaledLambdaComparison`). -/
theorem cmHarrisLambdaLevelCohomology_map {V U : SmallCMLevel D} (b : V ⟶ U) :
    (Hlev).map b.op =
      cmScaledDescentMap D ρ p (FiniteCompletion K l.1) (scaledLambda) (levelLambda)
        (psiCmp) b :=
  rfl

/-- Elements of a level act trivially on the cohomology at that level. -/
theorem isLevelTrivial_cmHarrisLambdaLevelCohomology : IsLevelTrivial (Hlev) :=
  isLevelTrivial_cmScaledDescent D ρ p _ (raiseCmp) (shiftCmp) (trivCmp)

set_option hygiene false in
local notation "hHlev" => isLevelTrivial_cmHarrisLambdaLevelCohomology D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q p ρ existence geometry hRigid
  l degree

/-! ## The tower cohomology and the finite-adelic action -/

/-- `H^d(S, W)_λ = colim_U H^d(S_U ×_F F̄, W)_λ` as a smooth representation of `GG(A_f)` over
`K_λ`, with the commuting action of `Gal(F̄/F)`. -/
def cmHarrisLambdaTowerCohomology :
    Action (SmoothRep.{0, 0, 0} (FiniteCompletion K l.1) D.rationalInvolution.FiniteAdelicPoints)
      (Field.absoluteGaloisGroup F) :=
  towerAction (Hlev) (hHlev)

set_option hygiene false in
local notation "Htow" => cmHarrisLambdaTowerCohomology D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q p ρ existence geometry hRigid
  l degree

set_option hygiene false in
local notation "ιlev" => ι ((Hlev) ⋙ Action.forget (ModuleCat.{0} (FiniteCompletion K l.1))
  (Field.absoluteGaloisGroup F))

/-- `γ ∈ Gal(F̄/F)` acts on a class from level `U` by its action at level `U`. -/
theorem cmHarrisLambdaTowerCohomology_ρ_ι_apply (γ : Field.absoluteGaloisGroup F)
    (U : SmallCMLevel D) (x : ((Hlev).obj (op U)).V) :
    ((Htow).ρ γ).hom.hom ((ιlev U).hom x) = (ιlev U).hom ((((Hlev).obj (op U)).ρ γ).hom x) :=
  towerAction_ρ_ι_apply (Hlev) (hHlev) γ U x

/-- `g ∈ GG(A_f)` sends a class from level `U` to the class at the conjugate level through the
map of the transporter with element `op g⁻¹`. -/
theorem cmHarrisLambdaTowerCohomology_representation_ι_apply
    (g : D.rationalInvolution.FiniteAdelicPoints) (U : SmallCMLevel D)
    (x : ((Hlev).obj (op U)).V) :
    (Htow).V.obj.ρ g ((ιlev U).hom x) =
      (ιlev (restrictedConj D.rationalInvolution.LevelSufficientlySmall (MulOpposite.op g⁻¹)
          U)).hom
        (((Hlev).map (restrictedConjArrow D.rationalInvolution.LevelSufficientlySmall
          (MulOpposite.op g⁻¹) U).op).hom.hom x) :=
  towerAction_representation_ι_apply (Hlev) (hHlev) g U x

/-- The actions of `GG(A_f)` and of `Gal(F̄/F)` on `H^d(S, W)_λ` commute. -/
theorem cmHarrisLambdaTowerCohomology_comm (γ : Field.absoluteGaloisGroup F)
    (g : D.rationalInvolution.FiniteAdelicPoints) (z : (Htow).V) :
    ((Htow).ρ γ).hom.hom ((Htow).V.obj.ρ g z) = (Htow).V.obj.ρ g (((Htow).ρ γ).hom.hom z) :=
  towerAction_comm (Hlev) (hHlev) γ g z

/-! ## Fixed vectors and the level Hecke algebra -/

/-- The fixed-vector comparison for `H^d(S, W)_λ` (Harris–Taylor 2001, III.2): for every small
level `U`, the map `H^d(S_U ×_F F̄, W)_λ → H^d(S, W)_λ` is injective with image the vectors fixed
by the ordinary level of `U`. -/
def CMHarrisLambdaTowerFixedVectorComparison : Prop :=
  TowerFixedVectorComparison (Hlev)

set_option hygiene false in
local notation "hfixP" => CMHarrisLambdaTowerFixedVectorComparison D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q p ρ existence geometry hRigid
  l degree

/-- The `Gal(F̄/F)`-equivariant map from `H^d(S_U ×_F F̄, W)_λ` to the vectors of `H^d(S, W)_λ`
fixed by the ordinary level of `U`. -/
def cmHarrisLambdaTowerFixedLeg (U : SmallCMLevel D) :
    (Hlev).obj (op U) ⟶
      (Langlands.Shimura.LevelHecke.fixedVectorsActionFunctor (FiniteCompletion K l.1)
        (Field.absoluteGaloisGroup F) (inverseOpposite U.obj).subgroup).obj (Htow) :=
  towerFixedLeg (Hlev) (hHlev) U

/-- Under the fixed-vector comparison, `H^d(S_U ×_F F̄, W)_λ` is isomorphic, compatibly with
`Gal(F̄/F)`, to the vectors of `H^d(S, W)_λ` fixed by the ordinary level of `U`. -/
def cmHarrisLambdaTowerFixedLegIso (hfix : hfixP) (U : SmallCMLevel D) :
    (Hlev).obj (op U) ≅
      (Langlands.Shimura.LevelHecke.fixedVectorsActionFunctor (FiniteCompletion K l.1)
        (Field.absoluteGaloisGroup F) (inverseOpposite U.obj).subgroup).obj (Htow) :=
  towerFixedLegIso (Hlev) (hHlev) hfix U

/-- The vectors of `H^d(S, W)_λ` fixed by the ordinary level of `U`, as a module over the level
Hecke algebra of that level over `K_λ`, with the commuting action of `Gal(F̄/F)`. -/
abbrev cmHarrisLambdaTowerHeckeModule (U : SmallCMLevel D) :
    Action (ModuleCat.{0} (Langlands.Shimura.LevelHecke.LevelHeckeAlgebra (FiniteCompletion K l.1)
      (inverseOpposite U.obj).subgroup)) (Field.absoluteGaloisGroup F) :=
  towerHeckeModule (Hlev) (hHlev) U

/-- Each element of `Gal(F̄/F)` commutes with the level Hecke algebra. -/
theorem cmHarrisLambdaTowerHeckeModule_ρ_smul (U : SmallCMLevel D)
    (γ : Field.absoluteGaloisGroup F)
    (a : Langlands.Shimura.LevelHecke.LevelHeckeAlgebra (FiniteCompletion K l.1)
      (inverseOpposite U.obj).subgroup)
    (x : (cmHarrisLambdaTowerHeckeModule D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q p ρ existence geometry hRigid
      l degree U).V) :
    ((cmHarrisLambdaTowerHeckeModule D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q p ρ existence geometry hRigid
      l degree U).ρ γ).hom (a • x) =
      a • ((cmHarrisLambdaTowerHeckeModule D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q p ρ existence geometry hRigid
      l degree U).ρ γ).hom x :=
  towerHeckeModule_ρ_smul (Hlev) (hHlev) U γ a x

/-! ## Isotypic parts and multiplicity spaces -/

section Isotypic

variable (M : Type uM) [Field M] [Algebra (FiniteCompletion K l.1) M]
  {V : Type uV} [AddCommGroup V] [Module M V]
  (τ : Representation M D.rationalInvolution.FiniteAdelicPoints V)

/-- `H^d(S, W)_λ ⊗_{K_λ} M`, a smooth representation of `GG(A_f)` over `M` with the commuting
action of `Gal(F̄/F)`. -/
abbrev cmHarrisLambdaTowerExtendScalars :=
  towerExtendScalars M (Hlev) (hHlev)

set_option hygiene false in
local notation "towerM" => cmHarrisLambdaTowerExtendScalars D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q p ρ existence geometry hRigid
  l degree M

/-- The `τ`-isotypic part `H^d(S, W)_λ[τ]` of `H^d(S, W)_λ ⊗_{K_λ} M`, with the restricted
actions of `GG(A_f)` and `Gal(F̄/F)`. -/
abbrev cmHarrisLambdaTowerIsotypic :=
  towerIsotypic M (Hlev) (hHlev) τ

/-- The vectors `H^d(S_U, W)[τ]` of the `τ`-isotypic part fixed by the ordinary level of `U`,
with the action of `Gal(F̄/F)`. -/
abbrev cmHarrisLambdaTowerIsotypicFixedVectors (U : SmallCMLevel D) :=
  towerIsotypicFixedVectors M (Hlev) (hHlev) τ U

/-- The multiplicity space `Hom_{GG(A_f)}(τ, H^d(S, W)_λ ⊗_{K_λ} M)`, with `Gal(F̄/F)` acting by
composition. -/
abbrev cmHarrisLambdaTowerMultiplicity :=
  towerMultiplicity M (Hlev) (hHlev) τ

/-- The Hecke multiplicity space `Hom_{H(U)}(τ^U, (H^d(S, W)_λ ⊗_{K_λ} M)^U)` at the ordinary
level of `U`, for its level Hecke algebra `H(U)` over `M`, with `Gal(F̄/F)` acting by
composition. -/
abbrev cmHarrisLambdaTowerHeckeMultiplicity (U : SmallCMLevel D) :=
  towerHeckeMultiplicity M (Hlev) (hHlev) τ U

/-- The evaluation map `V ⊗ Hom_{GG(A_f)}(τ, H^d(S, W)_λ ⊗ M) → (H^d(S, W)_λ ⊗ M)[τ]` is
surjective. -/
theorem cmHarrisLambdaTowerIsotypicEvaluation_surjective :
    Function.Surjective (isotypicEvaluation τ (towerM).V) :=
  towerIsotypicEvaluation_surjective M (Hlev) (hHlev) τ

/-- The evaluation map is equivariant for `Gal(F̄/F)`, acting on the multiplicity space by
composition and on the isotypic part by restriction. -/
theorem cmHarrisLambdaTowerIsotypicEvaluation_galois (γ : Field.absoluteGaloisGroup F) :
    isotypicEvaluation τ (towerM).V ∘ₗ
        LinearMap.lTensor V (multiplicityRepresentation τ _ (towerM) γ) =
      isotypicGaloisRepresentation τ _ (towerM) γ ∘ₗ isotypicEvaluation τ (towerM).V :=
  towerIsotypicEvaluation_galois M (Hlev) (hHlev) τ γ

/-- Under the fixed-vector comparison, the vectors of `H^d(S, W)_λ ⊗_{K_λ} M` fixed by the
ordinary level of `U` are isomorphic, compatibly with `Gal(F̄/F)`, to
`H^d(S_U ×_F F̄, W)_λ ⊗_{K_λ} M`. -/
def cmHarrisLambdaTowerExtendScalarsFixedVectorsIso (hfix : hfixP) (U : SmallCMLevel D) :
    LatticeGaloisRepresentation.baseChangeAction (L := M) ((levelLambda) U) ≅
      (Langlands.Shimura.LevelHecke.fixedVectorsActionFunctor M (Field.absoluteGaloisGroup F)
        (inverseOpposite U.obj).subgroup).obj (towerM) :=
  towerExtendScalarsFixedVectorsIso M (hH := hHlev) hfix U

end Isotypic

/-! ## Galois representations -/

section Objects

variable (M : Type uM) [Field M] [Algebra (FiniteCompletion K l.1) M] [TopologicalSpace M]
  [IsTopologicalRing M] (hKM : Continuous (algebraMap (FiniteCompletion K l.1) M))
  (hfix : hfixP) (U : SmallCMLevel D)
  (hfin : CMHarrisLambdaCohomologyFiniteDimensional D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality dualityNaturality
    polarizationStability compatibility h htor q U ρ p existence geometry (hRigid U) l degree)
  (hcont : CMHarrisLambdaCohomologyContinuous D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality dualityNaturality
    polarizationStability compatibility h htor q U ρ p existence geometry (hRigid U) l degree)
  {V : Type uV} [AddCommGroup V] [Module M V]
  (τ : Representation M D.rationalInvolution.FiniteAdelicPoints V)

set_option hygiene false in
local notation "towerM" => cmHarrisLambdaTowerExtendScalars D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q p ρ existence geometry hRigid
  l degree M

set_option hygiene false in
local notation "unramifiedU" v' => CMHarrisLambdaCohomologyUnramifiedAt D C preservation
  composition unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q U ρ p existence geometry
  (hRigid U) l degree v'

/-- The vectors `H^d(S_U, W)[τ]` of the `τ`-isotypic part fixed by the ordinary level of `U`, as
a continuous finite-dimensional Galois representation of `F` over `M`, when
`H^d(S_U ×_F F̄, W)_λ` is finite-dimensional with continuous Galois action and the fixed-vector
comparison holds. -/
def cmHarrisLambdaIsotypicFixedVectorsObjects : Objects F M :=
  haveI : Module.Finite (FiniteCompletion K l.1) ((Hlev).obj (op U)).V := hfin
  towerIsotypicFixedVectorsObjects M (hHlev) hKM hfix U hcont τ

/-- At a finite place `v` of `F` where `H^d(S_U ×_F F̄, W)_λ` is unramified, the Euler polynomial
of `H^d(S_U, W)[τ]` is the reversed characteristic polynomial of a geometric Frobenius at `v`
(Harris 1999, formula (5.6)). -/
theorem hasEulerPolynomialAt_cmHarrisLambdaIsotypicFixedVectorsObjects
    {v : Global.FinitePlace F}
    (ι : ClosureEmbedding (NumberField.FinitePlace.embedding (K := F) v))
    (hu : unramifiedU v) :
    haveI : Module.Finite (FiniteCompletion K l.1) ((Hlev).obj (op U)).V := hfin
    haveI := finite_towerExtendScalarsFixedVectors M (H := Hlev) (hH := hHlev) hfix U
    HasEulerPolynomialAt (cmHarrisLambdaIsotypicFixedVectorsObjects D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q p ρ existence geometry hRigid
        l degree M hKM hfix U hfin hcont τ) v
      (geometricFrobenius (ModuleCat.{uM} M) v
        (cmHarrisLambdaTowerIsotypicFixedVectors D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q p ρ existence geometry hRigid
          l degree M τ U) ι).hom.charpoly.reverse :=
  haveI : Module.Finite (FiniteCompletion K l.1) ((Hlev).obj (op U)).V := hfin
  hasEulerPolynomialAt_towerIsotypicFixedVectorsObjects M (hHlev) hKM hfix U hcont τ ι hu

/-- The multiplicity space `Hom_{GG(A_f)}(τ, H^d(S, W)_λ ⊗ M)`, when finite-dimensional, as a
continuous Galois representation of `F` over `M`, for `τ` spanned by the translates of its
vectors fixed by the ordinary level of `U`. -/
def cmHarrisLambdaMultiplicityObjects
    (hgen : Submodule.span M (⋃ g : D.rationalInvolution.FiniteAdelicPoints,
      τ g '' (fixedVectors τ (inverseOpposite U.obj).subgroup : Set V)) = ⊤)
    [Module.Finite M (τ.IntertwiningMap (towerM).V.representation)] :
    Objects F M :=
  towerMultiplicityObjects M (hHlev) hKM hfix U hcont τ hgen

/-- At a finite place `v` of `F` where `H^d(S_U ×_F F̄, W)_λ` is unramified, the Euler polynomial
of the multiplicity space is the reversed characteristic polynomial of a geometric Frobenius at
`v` (Harris 1999, formula (5.6)). -/
theorem hasEulerPolynomialAt_cmHarrisLambdaMultiplicityObjects
    {v : Global.FinitePlace F}
    (ι : ClosureEmbedding (NumberField.FinitePlace.embedding (K := F) v))
    (hgen : Submodule.span M (⋃ g : D.rationalInvolution.FiniteAdelicPoints,
      τ g '' (fixedVectors τ (inverseOpposite U.obj).subgroup : Set V)) = ⊤)
    [Module.Finite M (τ.IntertwiningMap (towerM).V.representation)]
    (hu : unramifiedU v) :
    HasEulerPolynomialAt (cmHarrisLambdaMultiplicityObjects D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q p ρ existence geometry hRigid
        l degree M hKM hfix U hcont τ hgen) v
      (geometricFrobenius (ModuleCat.{max uV uM} M) v
        (cmHarrisLambdaTowerMultiplicity D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q p ρ existence geometry hRigid
          l degree M τ) ι).hom.charpoly.reverse :=
  hasEulerPolynomialAt_towerMultiplicityObjects M (hHlev) hKM hfix U hcont τ ι hgen hu

/-- The Hecke multiplicity space `Hom_{H(U)}(τ^U, (H^d(S, W)_λ ⊗ M)^U)` at the ordinary level of
`U`, when finite-dimensional, as a continuous Galois representation of `F` over `M`. -/
def cmHarrisLambdaHeckeMultiplicityObjects
    [Module.Finite M (fixedVectors τ (inverseOpposite U.obj).subgroup →ₗ[
      Langlands.Shimura.LevelHecke.LevelHeckeAlgebra M (inverseOpposite U.obj).subgroup]
        fixedVectors (towerM).V.representation (inverseOpposite U.obj).subgroup)] :
    Objects F M :=
  towerHeckeMultiplicityObjects M (hHlev) hKM hfix U hcont τ

/-- At a finite place `v` of `F` where `H^d(S_U ×_F F̄, W)_λ` is unramified, the Euler polynomial
of the Hecke multiplicity space is the reversed characteristic polynomial of a geometric
Frobenius at `v` (Harris 1999, formula (5.6)). -/
theorem hasEulerPolynomialAt_cmHarrisLambdaHeckeMultiplicityObjects
    {v : Global.FinitePlace F}
    (ι : ClosureEmbedding (NumberField.FinitePlace.embedding (K := F) v))
    [Module.Finite M (fixedVectors τ (inverseOpposite U.obj).subgroup →ₗ[
      Langlands.Shimura.LevelHecke.LevelHeckeAlgebra M (inverseOpposite U.obj).subgroup]
        fixedVectors (towerM).V.representation (inverseOpposite U.obj).subgroup)]
    (hu : unramifiedU v) :
    HasEulerPolynomialAt (cmHarrisLambdaHeckeMultiplicityObjects D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q p ρ existence geometry hRigid
        l degree M hKM hfix U hcont τ) v
      (geometricFrobenius (ModuleCat.{max uV uM} M) v
        (cmHarrisLambdaTowerHeckeMultiplicity D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q p ρ existence geometry hRigid
          l degree M τ U) ι).hom.charpoly.reverse :=
  hasEulerPolynomialAt_towerHeckeMultiplicityObjects M (hHlev) hKM hfix U hcont τ ι hu

end Objects

end Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel
