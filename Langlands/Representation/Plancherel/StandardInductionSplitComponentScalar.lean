import Langlands.Representation.Plancherel.StandardInductionCanonicalScalar
import Langlands.Representation.Plancherel.SplitComponentLatticeBridge

/-! # Canonical scalar orbit presentations from an actual split component -/

noncomputable section

open CategoryTheory AlgebraicGeometry MeasureTheory MeasureTheory.Measure
open Langlands.AlgebraicGeometry.PointTopology
open scoped NNReal CategoryTheory.MonObj

namespace Langlands.Plancherel

open Aubert.General Induction UnramifiedOperatorFamily StandardIntertwining

universe u uG uV

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  (L : GroupScheme (Spec (CommRingCat.of F)))
  [IsAffine L.X.left] [LocallyOfFiniteType L.X.hom]

local instance standardInductionSplitComponentScalarTopologicalSpace : TopologicalSpace (GroupScheme.rationalPoints L) :=
  rationalPointTopology F L.X

local instance standardInductionSplitComponentScalarNonarchimedeanGroup : NonarchimedeanGroup (GroupScheme.rationalPoints L) :=
  rationalPoints_nonarchimedeanGroup L

variable (hL : GroupScheme.IsConnectedReductive L)
  {T : CommGroupScheme (Spec (CommRingCat.of F))} [IsAffine T.X.left]
  (s : T.toGrp ⟶ L) (hs : GroupScheme.IsSplitComponent s)
  (hinj : Function.Injective (GroupScheme.characterRestrict s))

section Stabilizer

variable {H : Type uG} [Group H] [TopologicalSpace H]
  (e : GroupScheme.rationalPoints L ≃ₜ* H)
  (A : Langlands.SmoothRep.{0, uG, uV} ℂ H)
  (hAirr : A.IsIrreducible) (hAadm : A.IsAdmissible)

include hL s hs hinj hAirr hAadm

/-- An actual split component and injective rational-character restriction
supply the finite full self-twist stabilizer after literal group transport. -/
theorem finite_pullback_rationalSmoothRepUnramifiedTwistStabilizer :
    Finite (smoothRepUnramifiedTwistStabilizer
      (fun ψ => (rationalNormCharacters L ψ).toMul) (SmoothRep.pullback e A)) := by
  let B : IrreducibleAdmissibleRep.{0, u, uV}
      (k := ℂ) (G := GroupScheme.rationalPoints L) :=
    ⟨SmoothRep.pullback e A,
      (isIrreducible_comp_continuousMulEquiv_iff A.representation e).mpr hAirr,
      isAdmissible_comp_continuousMulEquiv A.representation e hAadm⟩
  exact finite_rationalSmoothRepUnramifiedTwistStabilizer s
    hs.isCentralSplitTorus.isCentral
    (RenardCartan.finiteIndex_splitValuationImage_of_injective hL s hs hinj) B

end Stabilizer

section StandardComposite

variable (hp : Continuous (rationalValuationImageProjection L))
  {G : Type uG} [Group G] [TopologicalSpace G]
  [LocallyCompactSpace G] [NonarchimedeanGroup G] [T2Space G]
  {P₀ P₁ M U₀ U₁ : Subgroup G}
  (h₀ : IsSemidirectDecomposition P₀ M U₀) (hU₀ : IsClosed (U₀ : Set G))
  (hδ₀ : IsUnimodularModulus U₀ hU₀)
  (h₁ : IsSemidirectDecomposition P₁ M U₁) (hU₁ : IsClosed (U₁ : Set G))
  (hδ₁ : IsUnimodularModulus U₁ hU₁)
  (K : OpenSubgroup G) (hK : IsCompact (K : Set G))
  (hP₀ : IsClosed (P₀ : Set G)) (hP₁ : IsClosed (P₁ : Set G))
  (hP₀K : ∀ g : G, ∃ p : P₀, ∃ k : K, g = (p : G) * (k : G))
  (hP₁K : ∀ g : G, ∃ p : P₁, ∃ k : K, g = (p : G) * (k : G))
  (hr₀ : Continuous h₀.projection) (hr₁ : Continuous h₁.projection)
  (e : GroupScheme.rationalPoints L ≃ₜ* M)
  (hν : ∀ ψ, Continuous (rationalNormCharacters L ψ).toMul)
  (A : Langlands.SmoothRep.{0, uG, uV} ℂ M)
  (hAirr : A.IsIrreducible) (hAadm : A.IsAdmissible)
  [MeasurableSpace U₀] [BorelSpace U₀]
  [MeasurableSpace U₁] [BorelSpace U₁]
  [MeasurableSpace (U₀.subgroupOf U₁)] [BorelSpace (U₀.subgroupOf U₁)]
  [MeasurableSpace (U₁.subgroupOf U₀)] [BorelSpace (U₁.subgroupOf U₀)]
  [MeasurableSpace (QuotientSpace (U := U₀) U₁)]
  [BorelSpace (QuotientSpace (U := U₀) U₁)]
  [MeasurableSpace (QuotientSpace (U := U₁) U₀)]
  [BorelSpace (QuotientSpace (U := U₁) U₀)]
  (q₁₀ : Measure (QuotientSpace (U := U₀) U₁))
  (q₀₁ : Measure (QuotientSpace (U := U₁) U₀))
  (μU₀ : Measure U₀) (μU₁ : Measure U₁)
  (μI₁₀ : Measure (U₀.subgroupOf U₁))
  (μI₀₁ : Measure (U₁.subgroupOf U₀))
  [IsHaarMeasure μU₀] [μU₀.Regular] [IsMulRightInvariant μU₀]
  [IsHaarMeasure μU₁] [μU₁.Regular] [IsMulRightInvariant μU₁]
  [IsHaarMeasure μI₁₀] [μI₁₀.Regular] [IsMulRightInvariant μI₁₀]
  [IsHaarMeasure μI₀₁] [μI₀₁.Regular] [IsMulRightInvariant μI₀₁]
  (hq₁₀ : QuotientIntegration.IsCompatible (U₀.subgroupOf U₁) μU₁ μI₁₀ q₁₀)
  (hq₀₁ : QuotientIntegration.IsCompatible (U₁.subgroupOf U₀) μU₀ μI₀₁ q₀₁)
  (hM : IsClosed (M : Set G))
  (hsq₁₀ : SquaredModulusCompatibility h₀ hU₀ h₁ hU₁)
  (hsq₀₁ : SquaredModulusCompatibility h₁ hU₁ h₀ hU₀)

local notation "νL" => (fun ψ => Additive.toMul (rationalNormCharacters L ψ))
local notation "νM" => (fun ψ => MonoidHom.comp
  (Additive.toMul (rationalNormCharacters L ψ)) e.symm.toMulEquiv.toMonoidHom)
local notation "χM" => unramifiedCharactersHomeomorph e νL
local notation "Ω₁₀" => standardIntertwiningFullDomainRegion h₀ hU₀ U₁ e νL q₁₀ A
local notation "Ω₀₁" => standardIntertwiningFullDomainRegion h₁ hU₁ U₀ e νL q₀₁ A
local notation "J₁₀" => standardInductionIntertwinerFamily
  h₀ hU₀ U₁ e νL q₁₀ h₁ hU₁ μU₁ μI₁₀ hq₁₀ hM hsq₁₀ A
local notation "J₀₁" => standardInductionIntertwinerFamily
  h₁ hU₁ U₀ e νL q₀₁ h₀ hU₀ μU₀ μI₀₁ hq₀₁ hM hsq₀₁ A

variable
  (p : RationalOperatorContinuationData
    (standardIntertwiningFullDomainRegion h₀ hU₀ U₁ e
      (fun ψ => (rationalNormCharacters L ψ).toMul) q₁₀ A)
    (fun χ => compactIntertwiningOperator h₀ hU₀ hδ₀ K hP₀ hK hP₀K
      (fun ψ => (rationalNormCharacters L ψ).toMul.comp e.symm.toMulEquiv.toMonoidHom)
      (fun ψ => (hν ψ).comp e.symm.continuous) hr₀
      h₁ hU₁ hδ₁ hP₁ hP₁K hr₁
      (unramifiedCharactersHomeomorph e (fun ψ => (rationalNormCharacters L ψ).toMul)
        χ.val) A
      (standardInductionIntertwinerFamily h₀ hU₀ U₁ e
        (fun ψ => (rationalNormCharacters L ψ).toMul) q₁₀ h₁ hU₁
        μU₁ μI₁₀ hq₁₀ hM hsq₁₀ A χ)))
  (q : RationalOperatorContinuationData
    (standardIntertwiningFullDomainRegion h₁ hU₁ U₀ e
      (fun ψ => (rationalNormCharacters L ψ).toMul) q₀₁ A)
    (fun χ => compactIntertwiningOperator h₁ hU₁ hδ₁ K hP₁ hK hP₁K
      (fun ψ => (rationalNormCharacters L ψ).toMul.comp e.symm.toMulEquiv.toMonoidHom)
      (fun ψ => (hν ψ).comp e.symm.continuous) hr₁
      h₀ hU₀ hδ₀ hP₀ hP₀K hr₀
      (unramifiedCharactersHomeomorph e (fun ψ => (rationalNormCharacters L ψ).toMul)
        χ.val) A
      (standardInductionIntertwinerFamily h₁ hU₁ U₀ e
        (fun ψ => (rationalNormCharacters L ψ).toMul) q₀₁ h₀ hU₀
        μU₀ μI₀₁ hq₀₁ hM hsq₀₁ A χ)))
  {D₁₀ D₀₁ : Set (unramifiedCharacters (fun ψ => (rationalNormCharacters L ψ).toMul))}
  (hD₁₀ : IsOpen D₁₀) (hne₁₀ : D₁₀.Nonempty)
  (hD₁₀Ω : D₁₀ ⊆ standardIntertwiningFullDomainRegion h₀ hU₀ U₁ e
    (fun ψ => (rationalNormCharacters L ψ).toMul) q₁₀ A)
  (hD₀₁ : IsOpen D₀₁) (hne₀₁ : D₀₁.Nonempty)
  (hD₀₁Ω : D₀₁ ⊆ standardIntertwiningFullDomainRegion h₁ hU₁ U₀ e
    (fun ψ => (rationalNormCharacters L ψ).toMul) q₀₁ A)

local notation "π" => SmoothRep.pullback e A
local notation "fC" => continuedCompositeRationalScalar L hp hL p q
  (hne₁₀.mono hD₁₀Ω) (hne₀₁.mono hD₀₁Ω)
local notation "C" => continuedInductionComposite L hp hL
  h₀ hU₀ hδ₀ h₁ hU₁ hδ₁ K hK hP₀ hP₁ hP₀K hP₁K hr₀ hr₁ e hν A
  J₁₀ J₀₁ p q hD₁₀ hne₁₀ hD₁₀Ω hD₀₁ hne₀₁ hD₀₁Ω
variable
  {D : Set (unramifiedCharacters (fun ψ => (rationalNormCharacters L ψ).toMul))}
  (hD : IsOpen D) (hne : D.Nonempty)
  (hi : ∀ χ ∈ D,
    (UnramifiedLeviInduction h₀ hU₀
      (fun ψ => MonoidHom.comp (rationalNormCharacters L ψ).toMul
        e.symm.toMulEquiv.toMonoidHom)
      (unramifiedCharactersHomeomorph e (fun ψ => (rationalNormCharacters L ψ).toMul) χ)
      A).IsIrreducible)

local notation "jC" => standardInductionCompositeCanonicalRationalScalar L hp hL
  h₀ hU₀ hδ₀ h₁ hU₁ hδ₁ K hK hP₀ hP₁ hP₀K hP₁K hr₀ hr₁ e hν A
  q₁₀ q₀₁ μU₀ μU₁ μI₁₀ μI₀₁ hq₁₀ hq₀₁ hM hsq₁₀ hsq₀₁
  p q hne₁₀ hD₁₀Ω hne₀₁ hD₀₁Ω hne hi


variable [TopologicalSpace.SeparableSpace G]

/-- Construct the canonical scalar's invariant presentation on the actual
complex inducing orbit. Its full stabilizer is proved finite from the actual
split component and inducing irreducibility and admissibility. -/
def standardInductionSplitComponentCanonicalOrbitScalarPresentation :
    UnramifiedInvariantScalarPresentation L hp hL
      (smoothRepUnramifiedTwistStabilizer νL π) jC := by
  let := finite_pullback_rationalSmoothRepUnramifiedTwistStabilizer
    L hL s hs hinj e A hAirr hAadm
  exact standardInductionCompositeCanonicalOrbitScalarPresentation L hp hL
    h₀ hU₀ hδ₀ h₁ hU₁ hδ₁ K hK hP₀ hP₁ hP₀K hP₁K hr₀ hr₁ e hν A
    q₁₀ q₀₁ μU₀ μU₁ μI₁₀ μI₀₁ hq₁₀ hq₀₁ hM hsq₁₀ hsq₀₁
    p q hD₁₀ hne₁₀ hD₁₀Ω hD₀₁ hne₀₁ hD₀₁Ω hD hne hi

end StandardComposite

end Langlands.Plancherel
