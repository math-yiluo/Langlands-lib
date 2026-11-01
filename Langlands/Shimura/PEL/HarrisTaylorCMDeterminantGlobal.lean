import Langlands.AbelianScheme.AffineLieBasisCover
import Langlands.AlgebraicGeometry.ClosedLocusFromDirectedCover
import Langlands.Shimura.PEL.HarrisTaylorCMDeterminantIdeal
import Langlands.Shimura.PEL.HarrisTaylorCMDeterminantLocality

/-! # The global closed normalized Harris determinant locus in a supplied family -/

noncomputable section

open CategoryTheory _root_.AlgebraicGeometry
open Langlands.AbelianScheme

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.Shimura.CentralSimpleUnitaryData

open NumberField _root_.Algebra

variable {E F A : Type}
    [Field E] [NumberField E] [IsTotallyReal E]
    [Field F] [NumberField F] [IsTotallyComplex F]
    [Algebra E F] [IsQuadraticExtension E F]
    [Ring A] [Algebra E A] [Algebra F A] [IsScalarTower E F A]
    [Algebra ℚ A] [IsScalarTower ℚ E A] [IsScalarTower ℚ F A]
    {n : ℕ} (D : CentralSimpleUnitaryData E F A n)
    {L : Type} [Field L] [NumberField L] [IsCMField L]
    [IsQuadraticExtension ℚ L] [Algebra L F]
    {τ₀ : L →+* ℂ}
    (C : HarrisSignatureCharts D.toSecondKindInvolution n
      (harrisCMSection E (algebraMap L F) τ₀))
    {S : Scheme.{0}} (p : S ⟶ Spec (.of F))
    (B : AbelianScheme S) (i : A →ₐ[ℚ] End0 B)

/-- The local pulled-back representative and the composite map have the same determinant property. -/
theorem harrisTaylorCMDeterminantPullbackCondition_baseChange_iff
    {T T' : Scheme.{0}} (b : T ⟶ S) (g : T' ⟶ T) :
    D.HarrisTaylorCMDeterminantPullbackCondition C (b ≫ p)
        ((baseChange b).obj B) ((rationalBaseChangeEnd b B).comp i) g ↔
      D.HarrisTaylorCMDeterminantPullbackCondition C p B i (g ≫ b) := by
  unfold HarrisTaylorCMDeterminantPullbackCondition
  change D.HarrisTaylorCMDeterminantClassCondition C (g ≫ (b ≫ p))
      (RationalAlgebraAction.pullbackClass g
        (RationalAlgebraAction.pullbackClass b
          (RationalAlgebraAction.classOf (RationalAlgebraAction.of B i)))) ↔ _
  rw [Category.assoc, RationalAlgebraAction.pullbackClass_comp]

local notation "𝒰" => affineLieBasisCover B

/-- The actual local determinant loci on the constructed affine Lie-basis cover. -/
def harrisTaylorCMDeterminantCoverData :
    Langlands.AlgebraicGeometry.ClosedLocusFromDirectedCover.Data
      (fun {_} g => D.HarrisTaylorCMDeterminantPullbackCondition C p B i g) 𝒰 where
  Z V := D.harrisTaylorCMDeterminantLocus C ((𝒰).f V ≫ p)
    ((baseChange ((𝒰).f V)).obj B) ((rationalBaseChangeEnd ((𝒰).f V) B).comp i)
    (affineLieBasisTrivialization B V)
  ι V := D.harrisTaylorCMDeterminantLocusι C ((𝒰).f V ≫ p)
    ((baseChange ((𝒰).f V)).obj B) ((rationalBaseChangeEnd ((𝒰).f V) B).comp i)
    (affineLieBasisTrivialization B V)
  closed V := inferInstance
  chart_iff V {_} g := by
    rw [D.harrisTaylorCMDeterminantLocus_factors_iff C ((𝒰).f V ≫ p)
      ((baseChange ((𝒰).f V)).obj B) ((rationalBaseChangeEnd ((𝒰).f V) B).comp i)
      (affineLieBasisTrivialization B V) g]
    exact (D.harrisTaylorCMDeterminantPullbackCondition_iff C ((𝒰).f V ≫ p)
      ((baseChange ((𝒰).f V)).obj B) ((rationalBaseChangeEnd ((𝒰).f V) B).comp i) g).symm.trans
        (D.harrisTaylorCMDeterminantPullbackCondition_baseChange_iff C p B i ((𝒰).f V) g)

/-- The global determinant locus, constructed without a global free Lie chart or affine base. -/
def harrisTaylorCMGlobalDeterminantLocus : Scheme.{0} :=
  (D.harrisTaylorCMDeterminantCoverData C p B i).scheme
    (fun {_ _} f g h => D.harrisTaylorCMDeterminantPullbackCondition_comp C p B i f g h)

/-- The actual global closed inclusion in the supplied family base. -/
def harrisTaylorCMGlobalDeterminantLocusι :
    D.harrisTaylorCMGlobalDeterminantLocus C p B i ⟶ S :=
  (D.harrisTaylorCMDeterminantCoverData C p B i).inclusion
    (fun {_ _} f g h => D.harrisTaylorCMDeterminantPullbackCondition_comp C p B i f g h)

instance : IsClosedImmersion (D.harrisTaylorCMGlobalDeterminantLocusι C p B i) := by
  dsimp only [harrisTaylorCMGlobalDeterminantLocusι]
  infer_instance

/-- Factorization of every actual test map is equivalent to the exact normalized determinant. -/
theorem harrisTaylorCMGlobalDeterminantLocus_factors_iff
    {T : Scheme.{0}} (g : T ⟶ S) :
    (∃ k : T ⟶ D.harrisTaylorCMGlobalDeterminantLocus C p B i,
      k ≫ D.harrisTaylorCMGlobalDeterminantLocusι C p B i = g) ↔
      D.HarrisTaylorCMRationalLieDeterminantCondition C (g ≫ p)
        ((baseChange g).obj B) ((rationalBaseChangeEnd g B).comp i) := by
  apply Iff.trans
    ((D.harrisTaylorCMDeterminantCoverData C p B i).factors_iff
      (fun {_ _} f g h => D.harrisTaylorCMDeterminantPullbackCondition_comp C p B i f g h)
      (fun {_} g h =>
        D.harrisTaylorCMDeterminantPullbackCondition_of_openCover C p B i g
          ((𝒰).pullback₁ g) h) g)
  exact D.harrisTaylorCMDeterminantPullbackCondition_iff C p B i g

/-- The determinant factorization is unique as an actual scheme morphism. -/
theorem harrisTaylorCMGlobalDeterminantLocus_unique_factors_iff
    {T : Scheme.{0}} (g : T ⟶ S) :
    (∃! k : T ⟶ D.harrisTaylorCMGlobalDeterminantLocus C p B i,
      k ≫ D.harrisTaylorCMGlobalDeterminantLocusι C p B i = g) ↔
      D.HarrisTaylorCMRationalLieDeterminantCondition C (g ≫ p)
        ((baseChange g).obj B) ((rationalBaseChangeEnd g B).comp i) := by
  constructor
  · intro h
    exact (D.harrisTaylorCMGlobalDeterminantLocus_factors_iff C p B i g).mp h.exists
  · intro h
    obtain ⟨k, hk⟩ :=
      (D.harrisTaylorCMGlobalDeterminantLocus_factors_iff C p B i g).mpr h
    refine ⟨k, hk, ?_⟩
    intro k' hk'
    exact (cancel_mono (D.harrisTaylorCMGlobalDeterminantLocusι C p B i)).mp
      (hk'.trans hk.symm)

/-- The actual universal determinant family satisfies the unchanged all-family condition. -/
theorem harrisTaylorCMGlobalDeterminantLocus_condition :
    D.HarrisTaylorCMRationalLieDeterminantCondition C
      (D.harrisTaylorCMGlobalDeterminantLocusι C p B i ≫ p)
      ((baseChange (D.harrisTaylorCMGlobalDeterminantLocusι C p B i)).obj B)
      ((rationalBaseChangeEnd (D.harrisTaylorCMGlobalDeterminantLocusι C p B i) B).comp i) :=
  (D.harrisTaylorCMGlobalDeterminantLocus_factors_iff C p B i
    (D.harrisTaylorCMGlobalDeterminantLocusι C p B i)).mp ⟨𝟙 _, Category.id_comp _⟩

end Langlands.Shimura.CentralSimpleUnitaryData
