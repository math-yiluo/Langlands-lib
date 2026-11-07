import Langlands.Representation.Induction.CoefficientSplitStagesComparison

/-! Native split stages with the original inducing coinvariant action. -/

noncomputable section
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.Induction.Coefficient

open MeasureTheory MeasureTheory.Measure
open QuotientIntegration HarmonicAnalysis
open scoped NNReal ENNReal

universe uR uG uL uV uW

variable {R : Type uR} [CommRing R]
variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {L : Type uL} [Group L]
variable {V : Type uV} [AddCommGroup V] [Module R V]
variable (r : G →* L) (s : L →* G) (hrs : ∀ l, r (s l) = l)
variable (P H : Subgroup G) (hker : r.ker ≤ P) (hHP : H ≤ P)
variable (hsH : ∀ l : P.comap s, s (l : L) ∈ H)
variable (σ : Representation R H V)

local notation "K" => P.comap s
local notation "HP" => H.subgroupOf P
local notation "φ" => MulEquiv.toMonoidHom (Subgroup.subgroupOfEquivOfLe hHP)
local notation "σP" => σ.comp φ
local notation "rP" => splitStagesRetraction r s hrs P hker
local notation "sP" => s.subgroupComap P
local notation "N" => r.ker.comap H.subtype
local notation "a" => splitStagesInducingSection s P H hsH

/-- Remove the intermediate subgroup from the coefficient quotient, retaining
the original inducing representation and its actual normal-coinvariant action. -/
def splitStagesAmbientCoefficientEquiv :
    Representation.Equiv
      (splitKernelCoefficientAction rP sP HP (fun l => hsH l) σP)
      ((σ.toCoinvariants N).comp a) where
  toLinearEquiv := splitStagesCoefficientEquiv r s hrs P H hker hHP σ
  isIntertwining' l := by
    apply LinearMap.ext
    intro q
    obtain ⟨v, rfl⟩ := Representation.Coinvariants.mk_surjective _ q
    exact splitStagesCoefficientEquiv_section_mk r s hrs P H hker hHP hsH σ l v

@[simp]
theorem splitStagesAmbientCoefficientEquiv_mk (v : V) :
    splitStagesAmbientCoefficientEquiv r s hrs P H hker hHP hsH σ
        (Representation.Coinvariants.mk
          ((σP).comp ((rP).ker.subtype.subgroupComap HP)) v) =
      Jacquet.mk σ N v := rfl

@[simp]
theorem splitStagesAmbientCoefficientEquiv_symm_mk (v : V) :
    (splitStagesAmbientCoefficientEquiv r s hrs P H hker hHP hsH σ).symm
        (Jacquet.mk σ N v) =
      Representation.Coinvariants.mk
        ((σP).comp ((rP).ker.subtype.subgroupComap HP)) v := rfl

variable {W : Type uW} [AddCommGroup W] [Module R W]
variable {τ : Representation R H W} (T : σ.IntertwiningMap τ)

/-- The coefficient comparison commutes with every original inducing map. -/
theorem splitStagesAmbientCoefficientEquiv_natural
    (q : Representation.Coinvariants ((σP).comp ((rP).ker.subtype.subgroupComap HP))) :
    splitStagesAmbientCoefficientEquiv r s hrs P H hker hHP hsH τ
        (Representation.Coinvariants.map _ _
          (splitStagesIntersectionMap r s hrs P H hker hHP T) q) =
      Representation.Coinvariants.map _ _ (Jacquet.restrictMap T N)
        (splitStagesAmbientCoefficientEquiv r s hrs P H hker hHP hsH σ q) :=
  splitStagesCoefficientEquiv_natural r s hrs P H hker hHP T q

section Assembly

variable [Algebra ℂ R] [Module ℂ V] [IsScalarTower ℂ R V]
variable [T2Space G] [LocallyCompactSpace G]
variable [TopologicalSpace L] [IsTopologicalGroup L]
variable (hr : Continuous r) (hs : Continuous s)
variable (hP : IsClosed (P : Set G)) (hH : IsClosed (H : Set G))
variable (hσ : IsSmooth σ)
variable [LocallyCompactSpace (splitStagesRetraction r s hrs P hker).ker]
variable [MeasurableSpace (splitStagesRetraction r s hrs P hker).ker]
variable [BorelSpace (splitStagesRetraction r s hrs P hker).ker]
variable [MeasurableSpace
  ((H.subgroupOf P).comap (splitStagesRetraction r s hrs P hker).ker.subtype)]
variable [BorelSpace
  ((H.subgroupOf P).comap (splitStagesRetraction r s hrs P hker).ker.subtype)]
variable [MeasurableSpace (LeftQuotient
  ((H.subgroupOf P).comap (splitStagesRetraction r s hrs P hker).ker.subtype))]
variable [BorelSpace (LeftQuotient
  ((H.subgroupOf P).comap (splitStagesRetraction r s hrs P hker).ker.subtype))]
variable (ν : Measure (LeftQuotient
  ((H.subgroupOf P).comap (splitStagesRetraction r s hrs P hker).ker.subtype)))
variable [IsFiniteMeasureOnCompacts ν]
variable (hKernelBasis : ∀ O : Set (splitStagesRetraction r s hrs P hker).ker,
  IsOpen O → (1 : (splitStagesRetraction r s hrs P hker).ker) ∈ O →
    ∃ U : OpenSubgroup (splitStagesRetraction r s hrs P hker).ker,
      IsCompact (U : Set (splitStagesRetraction r s hrs P hker).ker) ∧
        (U : Set (splitStagesRetraction r s hrs P hker).ker) ⊆ O)
variable (μN : Measure (splitStagesRetraction r s hrs P hker).ker)
variable (μI : Measure
  ((H.subgroupOf P).comap (splitStagesRetraction r s hrs P hker).ker.subtype))
variable [IsHaarMeasure μN] [μN.Regular] [IsMulRightInvariant μN]
variable [IsHaarMeasure μI] [μI.Regular] [IsMulRightInvariant μI]
variable (hCompatible : IsCompatible
  ((H.subgroupOf P).comap (splitStagesRetraction r s hrs P hker).ker.subtype) μN μI ν)
variable (hN : IsClosed (r.ker : Set G))
variable (hBasis : ∀ O : Set G, IsOpen O → (1 : G) ∈ O →
  ∃ U : OpenSubgroup G, IsCompact (U : Set G) ∧ (U : Set G) ⊆ O)

local notation "hHPc" => hH.preimage (continuous_subtype_val : Continuous P.subtype)
local notation "χ" =>
  MonoidHom.comp (Units.map (RingHom.toMonoidHom (algebraMap ℂ R)))
    (Jacquet.complexCharacter (splitKernelHaarRatio rP sP HP (fun l => hsH l) hHPc))
local notation "κA" => twist χ (MonoidHom.comp (Representation.toCoinvariants σ N) a)

/-- Native compact stages with coefficient quotient by the actual normal
intersection inside the original inducing group. -/
def splitStagesAmbientCompactEquiv :
    Representation.Equiv (((compactInduced H σ).toCoinvariants r.ker).comp s)
      (compactInduced K κA) :=
  (splitStagesCompactEquiv r s hrs hr hs P H hker hHP hP hH hsH σ hσ
    ν hKernelBasis μN μI hCompatible hN hBasis).trans
      (compactInducedEquiv K
        (twistEquiv χ (splitStagesAmbientCoefficientEquiv r s hrs P H hker hHP hsH σ)))

/-- Evaluate on an actual original compact function: take the relative
integral and identify each coefficient class with its original inducing class. -/
@[simp]
theorem splitStagesAmbientCompactEquiv_eval_mk (f : CompactFunctions H σ) (l : L) :
    eval K κA
      (splitStagesAmbientCompactEquiv r s hrs P H hker hHP hsH σ hr hs hP hH hσ
        ν hKernelBasis μN μI hCompatible hN hBasis
        (Representation.Coinvariants.mk ((compactInduced H σ).comp r.ker.subtype) f)).val l =
      splitStagesCoefficientEquiv r s hrs P H hker hHP σ
        (splitStagesInnerIntegral r s hrs hr hs P H hker hHP hP hH hsH σ hσ ν
          (splitStagesSlice P H hHP hP hH σ f (s l))) := by
  change splitStagesCoefficientEquiv r s hrs P H hker hHP σ
      (eval K _
        (splitStagesCompactEquiv r s hrs hr hs P H hker hHP hP hH hsH σ hσ
          ν hKernelBasis μN μI hCompatible hN hBasis
          (Representation.Coinvariants.mk _ f)).val l) = _
  rw [splitStagesCompactEquiv_eval_mk]

omit [T2Space G] [IsTopologicalGroup L]
  [LocallyCompactSpace (rP).ker]
  [MeasurableSpace (rP).ker] [BorelSpace (rP).ker]
  [MeasurableSpace ((HP).comap (rP).ker.subtype)]
  [BorelSpace ((HP).comap (rP).ker.subtype)] in
/-- The transported simple-function integrand is the actual original class
of `f(n*s(l))`, with the intermediate subgroup removed. -/
@[simp]
theorem splitStagesAmbientIntegrand_mk (f : CompactFunctions H σ) (l : L)
    (n : (rP).ker) :
    splitStagesCoefficientEquiv r s hrs P H hker hHP σ
      (fullCoinvariantsComplexEquiv ((σP).comp ((rP).ker.subtype.subgroupComap HP))
        (quotientCoinvariantSimple ((HP).comap (rP).ker.subtype)
          (Jacquet.CoefficientRestriction.complexRepresentation
            ((σP).comp ((rP).ker.subtype.subgroupComap HP)))
          (compactFunctionsComplexEquiv ((HP).comap (rP).ker.subtype)
            ((σP).comp ((rP).ker.subtype.subgroupComap HP))
            (splitStagesKernelSlice r s hrs hr hs P H hker hHP hP hH hsH σ hσ f l))
          (quotientMap ((HP).comap (rP).ker.subtype) n))) =
      Jacquet.mk σ N (eval H σ f.val (((n : P) : G) * s l)) := rfl

/-- The original inducing intertwiner on the actual coefficient quotient,
restricted through the original section and with the same Haar twist. -/
def splitStagesAmbientCoefficientMap
    {τ : Representation R H W} (T : σ.IntertwiningMap τ) :
    Representation.IntertwiningMap κA
      (twist χ ((τ.toCoinvariants N).comp a)) :=
  twistIntertwining χ (restrictAlongMap a (normalCoinvariantsMap N T))

variable [Module ℂ W] [IsScalarTower ℂ R W] (hτ : IsSmooth τ)

/-- The full comparison is natural for all native inducing intertwiners;
the target map is the original inducing map on its actual normal quotient. -/
theorem splitStagesAmbientCompactEquiv_natural
    (z : Representation.Coinvariants ((compactInduced H σ).comp r.ker.subtype)) :
    splitStagesAmbientCompactEquiv r s hrs P H hker hHP hsH τ hr hs hP hH hτ
        ν hKernelBasis μN μI hCompatible hN hBasis
        (Representation.Coinvariants.map _ _
          (Jacquet.restrictMap (compactInducedMap H T) r.ker) z) =
      compactInducedMap K (splitStagesAmbientCoefficientMap r s hrs P H hker hsH σ hH T)
        (splitStagesAmbientCompactEquiv r s hrs P H hker hHP hsH σ hr hs hP hH hσ
          ν hKernelBasis μN μI hCompatible hN hBasis z) := by
  change compactInducedEquiv K
      (twistEquiv χ (splitStagesAmbientCoefficientEquiv r s hrs P H hker hHP hsH τ))
      (splitStagesCompactEquiv r s hrs hr hs P H hker hHP hP hH hsH τ hτ
        ν hKernelBasis μN μI hCompatible hN hBasis
        (Representation.Coinvariants.map _ _
          (Jacquet.restrictMap (compactInducedMap H T) r.ker) z)) = _
  rw [splitStagesCompactEquiv_natural r s hrs hr hs P H hker hHP hP hH hsH σ hσ
    ν hKernelBasis μN μI hCompatible hτ T hN hBasis z]
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  funext l
  exact splitStagesAmbientCoefficientEquiv_natural r s hrs P H hker hHP hsH σ T
    (eval K _
      (splitStagesCompactEquiv r s hrs hr hs P H hker hHP hP hH hsH σ hσ
        ν hKernelBasis μN μI hCompatible hN hBasis z).val l)

end Assembly

end Langlands.Induction.Coefficient
