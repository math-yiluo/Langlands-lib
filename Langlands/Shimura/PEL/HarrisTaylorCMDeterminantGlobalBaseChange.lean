import Langlands.Shimura.PEL.HarrisTaylorCMDeterminantGlobal

/-! # Arbitrary base change of the global normalized Harris determinant locus -/

noncomputable section

open CategoryTheory CategoryTheory.Limits _root_.AlgebraicGeometry
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

local notation "Z" => D.harrisTaylorCMGlobalDeterminantLocus C p B i
local notation "ι" => D.harrisTaylorCMGlobalDeterminantLocusι C p B i
local notation "P" => D.HarrisTaylorCMDeterminantPullbackCondition C p B i

/-- The actual universal inclusion has the class-based determinant property. -/
theorem harrisTaylorCMGlobalDeterminantLocus_pullbackCondition : P ι :=
  (D.harrisTaylorCMDeterminantPullbackCondition_iff C p B i ι).mpr
    (D.harrisTaylorCMGlobalDeterminantLocus_condition C p B i)

/-- The uniquely determined actual lift of a test map satisfying the full determinant. -/
def harrisTaylorCMGlobalDeterminantLift {T : Scheme.{0}} (g : T ⟶ S) (hg : P g) :
    T ⟶ Z :=
  ((D.harrisTaylorCMGlobalDeterminantLocus_factors_iff C p B i g).mpr
    ((D.harrisTaylorCMDeterminantPullbackCondition_iff C p B i g).mp hg)).choose

@[reassoc (attr := simp)]
theorem harrisTaylorCMGlobalDeterminantLift_ι {T : Scheme.{0}}
    (g : T ⟶ S) (hg : P g) :
    D.harrisTaylorCMGlobalDeterminantLift C p B i g hg ≫ ι = g :=
  ((D.harrisTaylorCMGlobalDeterminantLocus_factors_iff C p B i g).mpr
    ((D.harrisTaylorCMDeterminantPullbackCondition_iff C p B i g).mp hg)).choose_spec

/-- Uniqueness refers to actual morphisms of schemes, with no restriction on the test scheme. -/
theorem harrisTaylorCMGlobalDeterminantLift_unique {T : Scheme.{0}}
    (g : T ⟶ S) (hg : P g) (k : T ⟶ Z) (hk : k ≫ ι = g) :
    k = D.harrisTaylorCMGlobalDeterminantLift C p B i g hg := by
  apply (cancel_mono ι).mp
  rw [hk, D.harrisTaylorCMGlobalDeterminantLift_ι C p B i g hg]

/-- Lifts commute with every actual precomposition of the test map. -/
theorem harrisTaylorCMGlobalDeterminantLift_comp {T T' : Scheme.{0}}
    (f : T' ⟶ T) (g : T ⟶ S) (hg : P g) :
    D.harrisTaylorCMGlobalDeterminantLift C p B i (f ≫ g)
        (D.harrisTaylorCMDeterminantPullbackCondition_comp C p B i f g hg) =
      f ≫ D.harrisTaylorCMGlobalDeterminantLift C p B i g hg := by
  symm
  apply D.harrisTaylorCMGlobalDeterminantLift_unique C p B i
  rw [Category.assoc, D.harrisTaylorCMGlobalDeterminantLift_ι C p B i g hg]

variable {T : Scheme.{0}} (b : T ⟶ S)

local notation "Bₜ" => Functor.obj (baseChange b) B
local notation "iₜ" => AlgHom.comp (rationalBaseChangeEnd b B) i
local notation "Zₜ" => D.harrisTaylorCMGlobalDeterminantLocus C (b ≫ p) Bₜ iₜ
local notation "ιₜ" => D.harrisTaylorCMGlobalDeterminantLocusι C (b ≫ p) Bₜ iₜ
local notation "Pₜ" => D.HarrisTaylorCMDeterminantPullbackCondition C (b ≫ p) Bₜ iₜ

/-- The determinant inclusion for the actual pulled-back family maps to the original locus. -/
def harrisTaylorCMGlobalDeterminantBaseChangeMap : Zₜ ⟶ Z :=
  D.harrisTaylorCMGlobalDeterminantLift C p B i (ιₜ ≫ b)
    ((D.harrisTaylorCMDeterminantPullbackCondition_baseChange_iff C p B i b ιₜ).mp
      (D.harrisTaylorCMGlobalDeterminantLocus_pullbackCondition C (b ≫ p) Bₜ iₜ))

@[reassoc (attr := simp)]
theorem harrisTaylorCMGlobalDeterminantBaseChangeMap_ι :
    D.harrisTaylorCMGlobalDeterminantBaseChangeMap C p B i b ≫ ι = ιₜ ≫ b := by
  exact D.harrisTaylorCMGlobalDeterminantLift_ι C p B i _ _

/-- The determinant locus of the actual pulled-back family is the actual base change. -/
theorem harrisTaylorCMGlobalDeterminantBaseChange_isPullback :
    IsPullback ιₜ (D.harrisTaylorCMGlobalDeterminantBaseChangeMap C p B i b) b ι := by
  have prop (s : PullbackCone b ι) : Pₜ s.fst := by
    apply (D.harrisTaylorCMDeterminantPullbackCondition_baseChange_iff C p B i b s.fst).mpr
    rw [s.condition]
    exact D.harrisTaylorCMDeterminantPullbackCondition_comp C p B i s.snd ι
      (D.harrisTaylorCMGlobalDeterminantLocus_pullbackCondition C p B i)
  let lift (s : PullbackCone b ι) : s.pt ⟶ Zₜ :=
    D.harrisTaylorCMGlobalDeterminantLift C (b ≫ p) Bₜ iₜ s.fst (prop s)
  have lift_fst (s : PullbackCone b ι) : lift s ≫ ιₜ = s.fst :=
    D.harrisTaylorCMGlobalDeterminantLift_ι C (b ≫ p) Bₜ iₜ s.fst (prop s)
  have lift_snd (s : PullbackCone b ι) :
      lift s ≫ D.harrisTaylorCMGlobalDeterminantBaseChangeMap C p B i b = s.snd := by
    apply (cancel_mono ι).mp
    rw [Category.assoc, D.harrisTaylorCMGlobalDeterminantBaseChangeMap_ι,
      ← Category.assoc, lift_fst, s.condition]
  refine IsPullback.of_isLimit'
    ⟨(D.harrisTaylorCMGlobalDeterminantBaseChangeMap_ι C p B i b).symm⟩
    (PullbackCone.IsLimit.mk _ lift lift_fst lift_snd ?_)
  intro s k hk _
  apply (cancel_mono ιₜ).mp
  exact (show k ≫ ιₜ = s.fst from hk).trans (lift_fst s).symm

/-- Canonical comparison with the categorical pullback of the original closed inclusion. -/
def harrisTaylorCMGlobalDeterminantBaseChangeIso : Zₜ ≅ pullback b ι :=
  (D.harrisTaylorCMGlobalDeterminantBaseChange_isPullback C p B i b).isoPullback

@[reassoc (attr := simp)]
theorem harrisTaylorCMGlobalDeterminantBaseChangeIso_hom_fst :
    (D.harrisTaylorCMGlobalDeterminantBaseChangeIso C p B i b).hom ≫
      pullback.fst b ι = ιₜ :=
  (D.harrisTaylorCMGlobalDeterminantBaseChange_isPullback C p B i b).isoPullback_hom_fst

@[reassoc (attr := simp)]
theorem harrisTaylorCMGlobalDeterminantBaseChangeIso_hom_snd :
    (D.harrisTaylorCMGlobalDeterminantBaseChangeIso C p B i b).hom ≫
      pullback.snd b ι = D.harrisTaylorCMGlobalDeterminantBaseChangeMap C p B i b :=
  (D.harrisTaylorCMGlobalDeterminantBaseChange_isPullback C p B i b).isoPullback_hom_snd

end Langlands.Shimura.CentralSimpleUnitaryData
