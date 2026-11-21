import Langlands.Global.AdelicConstantTermComposition
import Langlands.Global.AdelicStandardConstantTermIntegral
import Langlands.Analysis.FundamentalDomainConstantTermL2

/-! # Folded and quotient constant terms agree on invariant functions

The Library constant term `StandardParabolicFamily.constantTerm` integrates over `U(F) \ U(𝔸)` at
chosen representatives. The folded constant term `FibreAverage.foldConstantTerm` integrates over a
Borel fundamental domain after folding into a fundamental domain of `Λ₀ = P₀(F)`. On measurable
left `Λ₀`-invariant functions the two agree at every point. -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory NumberField Set
open scoped ENNReal

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Langlands.Global.FoldConstantTermBridge

section Representatives

variable {H : Type*} [Group H] [MeasurableSpace H]

end Representatives

section Fold

open Langlands.Analysis.FibreAverage

variable {H : Type*} [Group H] [MeasurableSpace H] [MeasurableMul₂ H] [MeasurableInv H]
  {V : Type*} [Group V] [MeasurableSpace V] [MeasurableMul₂ V] [MeasurableInv V]

/-- On a left `Λ`-invariant function the folded constant term is the plain normalized fibre
average. -/
theorem foldConstantTerm_of_invariant (Λ : Subgroup H) (D : Set H)
    (hD : ∀ x : H, ∃! l : Λ, (l : H) * x ∈ D) (j : V →* H) (ν : Measure V) (C : Set V)
    {f : H → ℂ} (hf : ∀ (l : Λ) (x : H), f ((l : H) * x) = f x) (g : H) :
    foldConstantTerm Λ D hD j ν C f g = ((ν C).toReal)⁻¹ • ∫ v in C, f (j v * g) ∂ν := by
  unfold foldConstantTerm
  congr 2
  funext v
  exact hf _ _

end Fold

section Adelic

open scoped CategoryTheory.MonObj
open Langlands.GroupScheme AdelicSubgroupPoints ConstantTermComposition

variable {F : Type u} [Field F] [NumberField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]

/-- Equal subgroup functors give equal averages. -/
theorem average_congr {U U' : SubgroupFunctor G} (h : U = U')
    [IsClosed (adelicPoints F G U : Set (AdelicGroupPoints F G))]
    [IsClosed (adelicPoints F G U' : Set (AdelicGroupPoints F G))]
    (φ : AdelicGroupPoints F G → ℂ) (g : AdelicGroupPoints F G) :
    ConstantTermComposition.average U φ g = ConstantTermComposition.average U' φ g := by
  subst h
  rfl

variable {U : SubgroupFunctor G} [hU : IsClosed (adelicPoints F G U : Set (AdelicGroupPoints F G))]

local instance bridgeLocallyCompact : LocallyCompactSpace (adelicPoints F G U) :=
  hU.locallyCompactSpace

local instance bridgeBorel : BorelSpace (RationalQuotient F G U) :=
  rationalQuotientBorelSpace F G U

/-- The representative average along `U` of a measurable `U(F)`-invariant function, unfolded to
the chosen Borel fundamental domain `C` of `U(F)` in `U(𝔸)`. -/
theorem average_eq_setIntegral {φ : AdelicGroupPoints F G → ℂ} (hφ : Measurable φ)
    (hinv : IsRationalInvariant F G U φ) (g : AdelicGroupPoints F G) :
    ConstantTermComposition.average U φ g =
      ((Measure.haar : Measure (adelicPoints F G U))
          (ConstantTermAverage.rationalFundamentalDomain F G U)).toReal⁻¹ •
        ∫ v in ConstantTermAverage.rationalFundamentalDomain F G U,
          φ ((v : AdelicGroupPoints F G) * g) ∂(Measure.haar : Measure (adelicPoints F G U)) := by
  have hm : Measurable fun v : adelicPoints F G U => φ ((v : AdelicGroupPoints F G) * g) :=
    hφ.comp (continuous_subtype_val.measurable.mul_const g)
  unfold ConstantTermComposition.average
  rw [normalizedRationalQuotientHaarMeasure, integral_smul_measure,
    Langlands.Global.EisensteinConstantTerm.haar_fundamentalDomain_eq, quotientMassNormalizer,
    ENNReal.toReal_inv]
  congr 1
  exact Langlands.Global.RankinSelbergGlobal.Unfolding.integral_out_eq (rationalSubgroup F G U) hm
    (fun c x => by
      change φ (((c : adelicPoints F G U) : AdelicGroupPoints F G) * x * g) = φ (x * g)
      rw [mul_assoc]
      exact hinv _ c.2 _) _ _

end Adelic

end Langlands.Global.FoldConstantTermBridge

namespace Langlands.Global.StandardParabolicFamily

open scoped CategoryTheory.MonObj
open Langlands.GroupScheme AdelicSubgroupPoints ConstantTermComposition
open Langlands.Analysis.FibreAverage Langlands.Global.FoldConstantTermBridge

variable {F : Type u} [Field F] [NumberField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  (𝓕 : StandardParabolicFamily F G)

local notation "Idx" => StandardIndex F G 𝓕.i 𝓕.ν
local notation "Λ₀" => StandardConstantTerm.minimalParabolicImage F G 𝓕.i 𝓕.ν

/-- **Bridge.** On a measurable left `P₀(F)`-invariant function, the Library constant term along
`P_Q` equals the folded constant term along `U_Q` used for the weighted `L²` operators. -/
theorem constantTerm_eq_foldConstantTerm (Q : Idx) {φ : AdelicGroupPoints F G → ℂ}
    (hφ : Measurable φ) (hinv : ∀ l ∈ Λ₀, ∀ x, φ (l * x) = φ x) (g : AdelicGroupPoints F G) :
    haveI hcl := StandardConstantTerm.isClosed_adelicPoints_standardUnipotent F G 𝓕.i 𝓕.ν Q.1
    haveI : LocallyCompactSpace (adelicPoints F G (standardUnipotent 𝓕.i 𝓕.ν Q.1)) :=
      hcl.locallyCompactSpace
    𝓕.constantTerm Q φ g =
      foldConstantTerm Λ₀
        (LeftCosetSpace.fundamentalDomain Λ₀
          (StandardConstantTerm.isDiscrete_minimalParabolicImage F G 𝓕.i 𝓕.ν))
        (LeftCosetSpace.fundamentalDomain_unique _
          (StandardConstantTerm.isDiscrete_minimalParabolicImage F G 𝓕.i 𝓕.ν))
        (adelicPoints F G (standardUnipotent 𝓕.i 𝓕.ν Q.1)).subtype Measure.haar
        (ConstantTermAverage.rationalFundamentalDomain F G (standardUnipotent 𝓕.i 𝓕.ν Q.1)) φ g := by
  let : IsClosed (adelicPoints F G (SubgroupFunctor.range (𝓕.iU Q ≫ 𝓕.p Q)) :
      Set (AdelicGroupPoints F G)) := isClosed_adelicPoints_range F G (𝓕.iU Q ≫ 𝓕.p Q)
  let hcl := StandardConstantTerm.isClosed_adelicPoints_standardUnipotent F G 𝓕.i 𝓕.ν Q.1
  let : LocallyCompactSpace (adelicPoints F G (standardUnipotent 𝓕.i 𝓕.ν Q.1)) :=
    hcl.locallyCompactSpace
  have hinvU : IsRationalInvariant F G (standardUnipotent 𝓕.i 𝓕.ν Q.1) φ := fun c hc x =>
    hinv _ (StandardConstantTerm.rationalSubgroup_standardUnipotent_le F G 𝓕.i 𝓕.ν
      (hG := 𝓕.connectedReductive) (hi := 𝓕.maximalSplit) (hν := 𝓕.generic) Q.1 Q.2 c hc) x
  have h1 : 𝓕.constantTerm Q φ g =
      ConstantTermComposition.average (SubgroupFunctor.range (𝓕.iU Q ≫ 𝓕.p Q)) φ g := rfl
  have h2 := average_congr (𝓕.range_radical_eq_standardUnipotent Q) φ g
  have h3 := average_eq_setIntegral hφ hinvU g
  have h4 := foldConstantTerm_of_invariant Λ₀
    (LeftCosetSpace.fundamentalDomain Λ₀
      (StandardConstantTerm.isDiscrete_minimalParabolicImage F G 𝓕.i 𝓕.ν))
    (LeftCosetSpace.fundamentalDomain_unique _
      (StandardConstantTerm.isDiscrete_minimalParabolicImage F G 𝓕.i 𝓕.ν))
    (adelicPoints F G (standardUnipotent 𝓕.i 𝓕.ν Q.1)).subtype Measure.haar
    (ConstantTermAverage.rationalFundamentalDomain F G (standardUnipotent 𝓕.i 𝓕.ν Q.1))
    (fun l x => hinv l l.2 x) g
  rw [h1, h2, h3, h4]
  rfl

end Langlands.Global.StandardParabolicFamily

namespace Langlands.Global

open scoped CategoryTheory.MonObj
open Langlands.GroupScheme AdelicSubgroupPoints Langlands.Analysis.FibreAverage

/-- **Statement form.** For a compatible standard parabolic family, a standard index `Q` and a
measurable function `φ` on `G(𝔸)` invariant under left translation by the image `Λ₀` of `P₀(F)`,
the Library constant term `𝓕.constantTerm Q φ` equals at every point the folded constant term
along `U_Q(𝔸)` for the Borel fundamental domains of `Λ₀` in `G(𝔸)` and of `U_Q(F)` in `U_Q(𝔸)`. -/
def FoldConstantTermBridgeStatement : Prop :=
  ∀ {F : Type u} [Field F] [NumberField F] {G : GroupScheme (Spec (CommRingCat.of F))}
    [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
    (𝓕 : StandardParabolicFamily F G) (Q : StandardIndex F G 𝓕.i 𝓕.ν)
    {φ : AdelicGroupPoints F G → ℂ}, Measurable φ →
    (∀ l ∈ StandardConstantTerm.minimalParabolicImage F G 𝓕.i 𝓕.ν, ∀ x, φ (l * x) = φ x) →
    ∀ g : AdelicGroupPoints F G,
      haveI hcl := StandardConstantTerm.isClosed_adelicPoints_standardUnipotent F G 𝓕.i 𝓕.ν Q.1
      haveI : LocallyCompactSpace (adelicPoints F G (standardUnipotent 𝓕.i 𝓕.ν Q.1)) :=
        hcl.locallyCompactSpace
      𝓕.constantTerm Q φ g =
        foldConstantTerm (StandardConstantTerm.minimalParabolicImage F G 𝓕.i 𝓕.ν)
          (LeftCosetSpace.fundamentalDomain (StandardConstantTerm.minimalParabolicImage F G 𝓕.i 𝓕.ν)
            (StandardConstantTerm.isDiscrete_minimalParabolicImage F G 𝓕.i 𝓕.ν))
          (LeftCosetSpace.fundamentalDomain_unique _
            (StandardConstantTerm.isDiscrete_minimalParabolicImage F G 𝓕.i 𝓕.ν))
          (adelicPoints F G (standardUnipotent 𝓕.i 𝓕.ν Q.1)).subtype Measure.haar
          (ConstantTermAverage.rationalFundamentalDomain F G (standardUnipotent 𝓕.i 𝓕.ν Q.1)) φ g

/-- Proof of `FoldConstantTermBridgeStatement`. -/
theorem foldConstantTermBridge : FoldConstantTermBridgeStatement.{u} :=
  fun 𝓕 Q _ hφ hinv g => 𝓕.constantTerm_eq_foldConstantTerm Q hφ hinv g

end Langlands.Global
