import Langlands.Shimura.Coefficients.HarrisReduction
import Langlands.Shimura.Unitary.HarrisLevels

/-! # Full Harris coefficient diagrams on the actual CM-compatible level spaces -/

noncomputable section

universe u v w z

namespace Langlands.Shimura

open CategoryTheory Opposite Langlands.Global

attribute [local instance] Langlands.Analytic.NormContinuousAffinoidAction.topCatSelfForget

namespace Coefficients

variable {A : Type u} [Ring A] [Algebra ℚ A] [Module.Finite ℚ A]
variable {L : Type u} [Field L] [NumberField L]
variable {W : Type u} [AddCommGroup W] [Module L W] [Module.Finite L W]
variable {σ : AlgebraInvolution ℚ A} (ρ : (σ.baseChange L).AlgebraicRepresentation W)
variable (p : FinitePlace ℚ) (U : CompactOpenLevel σ.FiniteAdelicPoints)

/-- The full coefficient reductions, equivariant for their actual image quotient groups. -/
def harrisCoefficientDiagram (m : ℕ) :
    EquivariantDiagram (harrisCongruenceGroups ρ p U m)
      (ModuleCat.{u} (HarrisCoefficientIntegers L p)) :=
  congruenceCoefficientDiagram (harrisCoefficientScalarIdeal L p m)
    (harrisLatticeAction ρ p U)

/-- Forgetting the finite quotient action retains the full original torsion system. -/
@[simp] theorem harrisCoefficientDiagram_obj (m : ℕ) :
    (harrisCoefficientDiagram ρ p U m).obj =
      harrisTorsionSystem ρ p U m ⋙
        Action.forget (ModuleCat.{u} (HarrisCoefficientIntegers L p)) U.subgroup := rfl

/-- The diagram action is the actual faithful finite action with integral scalars retained. -/
theorem harrisCoefficientDiagram_action (m n : ℕ)
    (g : HarrisCongruenceGroup ρ p U m n) (x : (harrisTorsionAction ρ p U m n).V) :
    ((harrisCoefficientDiagram ρ p U m).ρ (op n) g).hom x =
      ((harrisFiniteCoefficientAction ρ p U m n).ρ g).hom x := by
  induction g using QuotientGroup.induction_on with
  | H g => rfl

/-- Its transitions remain the actual surjective full-lattice reduction maps. -/
theorem harrisCoefficientDiagram_transition_surjective (m : ℕ)
    {i j : ℕᵒᵖ} (f : i ⟶ j) :
    Function.Surjective ((harrisCoefficientDiagram ρ p U m).transition f).hom :=
  congruenceCoefficientDiagram_transition_surjective
    (harrisCoefficientScalarIdeal L p m) (harrisLatticeAction ρ p U) f

variable (m : ℕ) (hm : m ≠ 0)

/-- The full coefficient kernels give actual compact open adelic levels. -/
def harrisCongruenceLevels :
    ℕᵒᵖ ⥤ CompactOpenLevel σ.FiniteAdelicPoints :=
  congruenceLevelTower U (harrisCoefficientScalarIdeal L p m)
    (harrisLatticeAction ρ p U) (harrisCongruenceKernel_isOpen ρ p U m hm)

/-- Each level is the ambient image of the full coefficient kernel. -/
@[simp] theorem harrisCongruenceLevels_obj_subgroup (n : ℕᵒᵖ) :
    ((harrisCongruenceLevels ρ p U m hm).obj n).subgroup =
      LevelSpace.sublevelSubgroup U.subgroup (harrisCongruenceKernel ρ p U m n.unop) :=
  rfl

/-- For elements of the original level, membership tests all coefficient places above `p`. -/
theorem mem_harrisCongruenceLevels (n : ℕᵒᵖ) (g : U.subgroup) :
    (g : σ.FiniteAdelicPoints) ∈ ((harrisCongruenceLevels ρ p U m hm).obj n).subgroup ↔
      ∀ l : Langlands.Global.AdelicFunctoriality.FinitePlacesAbove L p,
        g ∈ congruenceKernel (coefficientScalarIdeal l.1 m)
          (algebraicCompactCoefficientLattice ρ p l.1 U).action n.unop := by
  rw [harrisCongruenceLevels_obj_subgroup]
  change (g : σ.FiniteAdelicPoints) ∈
    (harrisCongruenceKernel ρ p U m n.unop).map U.subgroup.subtype ↔ _
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨k, hk, he⟩
    have hkg : k = g := Subtype.ext he
    exact (mem_harrisCongruenceKernel ρ p U m n.unop g).mp (hkg ▸ hk)
  · intro hg
    exact ⟨g, (mem_harrisCongruenceKernel ρ p U m n.unop g).mpr hg, rfl⟩

/-- The canonical inclusion from a coefficient level into the original compact open level. -/
def harrisCongruenceLevelInclusion (n : ℕᵒᵖ) :
    (harrisCongruenceLevels ρ p U m hm).obj n ⟶ U :=
  U.sublevelInclusion (harrisCongruenceKernel ρ p U m n.unop)
    (harrisCongruenceKernel_isOpen ρ p U m hm n.unop)

end Coefficients

namespace CentralSimpleUnitaryData

open Langlands.Shimura.Coefficients NumberField _root_.Algebra

variable {E : Type v} {K : Type w} {A : Type u}
    [Field E] [NumberField E] [IsTotallyReal E]
    [Field K] [NumberField K] [IsTotallyComplex K]
    [Algebra E K] [IsQuadraticExtension E K]
    [Ring A] [Algebra E A] [Algebra K A] [IsScalarTower E K A]
    [Algebra ℚ A] [IsScalarTower ℚ E A] [IsScalarTower ℚ K A]
    {n : ℕ} (D : CentralSimpleUnitaryData E K A n)

omit [NumberField E] [IsScalarTower E K A] [IsScalarTower ℚ E A] in
include D in
/-- The central-simple data supply the rational finiteness used by coefficient constructors. -/
theorem coefficientRationalFinite : Module.Finite ℚ A := by
  let : FiniteDimensional K A := D.finite
  exact FiniteDimensional.trans ℚ K A

variable [Module.Finite ℚ A]

variable (h : HasHarrisSignature D.toSecondKindInvolution n)
variable {F : Type z} [Field F] [NumberField F] [IsCMField F]
    [IsQuadraticExtension ℚ F] (ιF : F →+* K) (τ₀ : F →+* ℂ)
variable {L : Type u} [Field L] [NumberField L]
variable {W : Type u} [AddCommGroup W] [Module L W] [Module.Finite L W]
variable (ρ : (D.toSecondKindInvolution.rationalInvolution.baseChange L).AlgebraicRepresentation W)
variable (p : Langlands.Global.FinitePlace ℚ)
    (U : CompactOpenLevel D.toSecondKindInvolution.rationalInvolution.FiniteAdelicPoints)
variable (m : ℕ) (hm : m ≠ 0)

/-- The actual Harris CM-compatible congruence spaces over the full coefficient image groups. -/
def harrisCoefficientCongruenceSpaces :
    EquivariantDiagram (harrisCongruenceGroups ρ p U m) TopCat.{max u v} :=
  congruenceLevelSpaces
    (X := (HarrisSignatureCharts.ofSignature h
      (isCMSection_harrisCMSection E ιF τ₀)).Domain)
    U (harrisCoefficientScalarIdeal L p m) (harrisLatticeAction ρ p U)
    (harrisCongruenceKernel_isOpen ρ p U m hm)
    D.toSecondKindInvolution.rationalInvolution.finiteAdelicDiagonal

/-- These spaces are precisely the existing Harris tower at the constructed coefficient levels. -/
@[simp] theorem harrisCoefficientCongruenceSpaces_obj :
    (D.harrisCoefficientCongruenceSpaces h ιF τ₀ ρ p U m hm).obj =
      harrisCongruenceLevels ρ p U m hm ⋙ harrisUnitaryLevelTower D h ιF τ₀ := rfl

omit [IsScalarTower E K A] [IsScalarTower ℚ K A] in
include hm in
/-- Every residual group is the actual finite image of the original full-lattice action. -/
theorem harrisCoefficientCongruenceSpaces_group_finite (k : ℕᵒᵖ) :
    Finite ((harrisCongruenceGroups ρ p U m).obj k) :=
  harrisCongruenceGroup_finite ρ p U m hm k.unop

omit [IsScalarTower E K A] [IsScalarTower ℚ K A] in
include hm in
/-- Every coefficient object paired with this space diagram is finite. -/
theorem harrisCoefficientCongruenceSpaces_coefficient_finite (k : ℕᵒᵖ) :
    Finite ((harrisCoefficientDiagram ρ p U m).obj.obj k) :=
  harrisTorsionAction_finite ρ p U m hm k.unop

omit [IsScalarTower ℚ K A] in
/-- A space transition retains the same domain point and finite adelic representative. -/
@[simp] theorem harrisCoefficientCongruenceSpaces_map_mk {i j : ℕᵒᵖ} (f : i ⟶ j)
    (x : (HarrisSignatureCharts.ofSignature h
      (isCMSection_harrisCMSection E ιF τ₀)).Domain ×
        D.toSecondKindInvolution.rationalInvolution.FiniteAdelicPoints) :
    (D.harrisCoefficientCongruenceSpaces h ιF τ₀ ρ p U m hm).obj.map f
        (LevelSpace.mk ((harrisCongruenceLevels ρ p U m hm).obj i).subgroup x) =
      LevelSpace.mk ((harrisCongruenceLevels ρ p U m hm).obj j).subgroup x :=
  congruenceLevelSpaces_map_mk _ _ _ _ _ f x

omit [IsScalarTower ℚ K A] in
/-- The residual group acts by inverse right translation in the actual finite adelic factor. -/
@[simp] theorem harrisCoefficientCongruenceSpaces_action_mk (k : ℕ) (g : U.subgroup)
    (x : (HarrisSignatureCharts.ofSignature h
      (isCMSection_harrisCMSection E ιF τ₀)).Domain ×
        D.toSecondKindInvolution.rationalInvolution.FiniteAdelicPoints) :
    End.asHom ((D.harrisCoefficientCongruenceSpaces h ιF τ₀ ρ p U m hm).ρ
        (op k) (QuotientGroup.mk g))
        (LevelSpace.mk ((harrisCongruenceLevels ρ p U m hm).obj (op k)).subgroup x) =
      LevelSpace.mk ((harrisCongruenceLevels ρ p U m hm).obj (op k)).subgroup
        (x.1, x.2 * (g : D.toSecondKindInvolution.rationalInvolution.FiniteAdelicPoints)⁻¹) :=
  rfl

/-- The natural forgetful projection to the original CM-compatible Harris level. -/
def harrisCoefficientCongruenceProjection :
    (D.harrisCoefficientCongruenceSpaces h ιF τ₀ ρ p U m hm).obj ⟶
      (Functor.const ℕᵒᵖ).obj ((harrisUnitaryLevelTower D h ιF τ₀).obj U) :=
  congruenceLevelProjection
    (X := (HarrisSignatureCharts.ofSignature h
      (isCMSection_harrisCMSection E ιF τ₀)).Domain)
    U (harrisCoefficientScalarIdeal L p m) (harrisLatticeAction ρ p U)
    (harrisCongruenceKernel_isOpen ρ p U m hm)
    D.toSecondKindInvolution.rationalInvolution.finiteAdelicDiagonal

/-- Every component of this natural projection is surjective. -/
theorem harrisCoefficientCongruenceProjection_surjective (k : ℕᵒᵖ) :
    Function.Surjective
      ((D.harrisCoefficientCongruenceProjection h ιF τ₀ ρ p U m hm).app k) :=
  congruenceLevelProjection_surjective _ _ _ _ _ k

/-- Projection to the original level is invariant under the full coefficient quotient group. -/
@[reassoc] theorem harrisCoefficientCongruenceProjection_invariant (k : ℕᵒᵖ)
    (g : (harrisCongruenceGroups ρ p U m).obj k) :
    End.asHom ((D.harrisCoefficientCongruenceSpaces h ιF τ₀ ρ p U m hm).ρ k g) ≫
        (D.harrisCoefficientCongruenceProjection h ιF τ₀ ρ p U m hm).app k =
      (D.harrisCoefficientCongruenceProjection h ιF τ₀ ρ p U m hm).app k :=
  congruenceLevelProjection_invariant _ _ _ _ _ k g

/-- The same spaces form a diagram with jointly continuous action by the original level group. -/
def harrisCoefficientContinuousLevelSpaces :
    ℕᵒᵖ ⥤ ContAction TopCat.{max u v} U.subgroup :=
  congruenceContinuousLevelSpaces
    (X := (HarrisSignatureCharts.ofSignature h
      (isCMSection_harrisCMSection E ιF τ₀)).Domain)
    U (harrisCoefficientScalarIdeal L p m) (harrisLatticeAction ρ p U)
    (harrisCongruenceKernel_isOpen ρ p U m hm)
    D.toSecondKindInvolution.rationalInvolution.finiteAdelicDiagonal

omit [IsScalarTower ℚ K A] in
/-- Retaining joint continuity leaves the actual double-quotient spaces unchanged. -/
@[simp] theorem harrisCoefficientContinuousLevelSpaces_obj (k : ℕᵒᵖ) :
    ((D.harrisCoefficientContinuousLevelSpaces h ιF τ₀ ρ p U m hm).obj k).obj.V =
      (D.harrisCoefficientCongruenceSpaces h ιF τ₀ ρ p U m hm).obj.obj k := rfl

end CentralSimpleUnitaryData

end Langlands.Shimura
