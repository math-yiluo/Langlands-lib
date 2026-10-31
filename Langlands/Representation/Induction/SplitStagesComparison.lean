import Langlands.Representation.Induction.CompactTransitivityProof
import Langlands.Representation.Induction.NormalSplitComparison
import Langlands.Representation.Induction.SplitKernelEquivariant
import Langlands.Representation.Induction.SplitStagesRetraction
import Langlands.Representation.Smooth.Transfer.PullbackProof

/-! Assembly of compact stages, normal coinvariants and relative integration. -/

noncomputable section
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.Induction

open MeasureTheory MeasureTheory.Measure
open QuotientIntegration HarmonicAnalysis
open scoped NNReal ENNReal

universe uG uL uV uW

section Transport

variable {G : Type uG} [Group G]
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
variable {W : Type uW} [AddCommGroup W] [Module ℂ W]
variable {ρ : Representation ℂ G V} {τ : Representation ℂ G W}

/-- Transport of actual normal coinvariants retaining the ambient action. -/
def normalCoinvariantsEquiv (N : Subgroup G) [N.Normal] (e : ρ.Equiv τ) :
    (ρ.toCoinvariants N).Equiv (τ.toCoinvariants N) where
  toLinearMap := (normalCoinvariantsMap N e.toIntertwiningMap).toLinearMap
  invFun := normalCoinvariantsMap N e.symm.toIntertwiningMap
  left_inv z := by
    induction z using Representation.Coinvariants.induction_on with
    | h v => exact congrArg (Representation.Coinvariants.mk _) (e.symm_apply_apply v)
  right_inv z := by
    induction z using Representation.Coinvariants.induction_on with
    | h v => exact congrArg (Representation.Coinvariants.mk _) (e.apply_symm_apply v)
  isIntertwining' := (normalCoinvariantsMap N e.toIntertwiningMap).isIntertwining'

@[simp] theorem normalCoinvariantsEquiv_mk (N : Subgroup G) [N.Normal]
    (e : ρ.Equiv τ) (v : V) :
    normalCoinvariantsEquiv N e (Representation.Coinvariants.mk (ρ.comp N.subtype) v) =
      Representation.Coinvariants.mk (τ.comp N.subtype) (e v) := rfl

/-- Equality of normal subgroups transports the actual quotient representation. -/
def normalCoinvariantsCongr (ρ : Representation ℂ G V) {N K : Subgroup G}
    [N.Normal] [K.Normal] (h : N = K) :
    (ρ.toCoinvariants N).Equiv (ρ.toCoinvariants K) := by
  subst K
  exact Representation.Equiv.refl _

@[simp] theorem normalCoinvariantsCongr_mk (ρ : Representation ℂ G V)
    {N K : Subgroup G} [N.Normal] [K.Normal] (h : N = K) (v : V) :
    normalCoinvariantsCongr ρ h (Representation.Coinvariants.mk (ρ.comp N.subtype) v) =
      Representation.Coinvariants.mk (ρ.comp K.subtype) v := by
  subst K
  rfl

/-- Restrict a representation equivalence without changing its linear map. -/
def restrictAlongEquiv {L : Type uL} [Group L] (s : L →* G) (e : ρ.Equiv τ) :
    Representation.Equiv (ρ.comp s) (τ.comp s) where
  toLinearEquiv := e.toLinearEquiv
  isIntertwining' l := e.isIntertwining' (s l)

@[simp] theorem restrictAlongEquiv_apply {L : Type uL} [Group L]
    (s : L →* G) (e : ρ.Equiv τ) (v : V) : restrictAlongEquiv s e v = e v := rfl

variable [TopologicalSpace G] [IsTopologicalGroup G]

/-- Postcomposition transports actual compact induction along an equivalence. -/
def compactInducedEquiv (H : Subgroup G)
    {σ : Representation ℂ H V} {π : Representation ℂ H W} (e : σ.Equiv π) :
    (compactInduced H σ).Equiv (compactInduced H π) where
  toLinearMap := (compactInducedMap H e.toIntertwiningMap).toLinearMap
  invFun := compactInducedMap H e.symm.toIntertwiningMap
  left_inv f := by
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    funext g
    exact e.symm_apply_apply (eval H σ f.val g)
  right_inv f := by
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    funext g
    exact e.apply_symm_apply (eval H π f.val g)
  isIntertwining' := (compactInducedMap H e.toIntertwiningMap).isIntertwining'

@[simp] theorem compactInducedEquiv_eval (H : Subgroup G)
    {σ : Representation ℂ H V} {π : Representation ℂ H W} (e : σ.Equiv π)
    (f : CompactFunctions H σ) (g : G) :
    eval H π (compactInducedEquiv H e f).val g = e (eval H σ f.val g) := rfl

end Transport


section Assembly

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [T2Space G] [LocallyCompactSpace G]
variable {L : Type uL} [Group L] [TopologicalSpace L] [IsTopologicalGroup L]
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
variable (r : G →* L) (s : L →* G) (hrs : ∀ l, r (s l) = l)
variable (hr : Continuous r) (hs : Continuous s)
variable (P H : Subgroup G) (hker : r.ker ≤ P) (hHP : H ≤ P)
variable (hP : IsClosed (P : Set G)) (hH : IsClosed (H : Set G))
variable (hsH : ∀ l : P.comap s, s (l : L) ∈ H)
variable (σ : Representation ℂ H V) (hσ : IsSmooth σ)


local notation "K" => P.comap s
local notation "HP" => H.subgroupOf P
local notation "φ" => MulEquiv.toMonoidHom (Subgroup.subgroupOfEquivOfLe hHP)
local notation "σP" => σ.comp φ
local notation "ρP" => compactInduced HP σP
local notation "rP" => splitStagesRetraction r s hrs P hker
local notation "sP" => s.subgroupComap P

include hsH in
omit [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
  [LocallyCompactSpace G] [TopologicalSpace L] [IsTopologicalGroup L] in
private theorem splitStagesSection_mem (l : P.comap s) :
    sP l ∈ H.subgroupOf P := hsH l

include hσ in
omit [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] in
private theorem splitStagesCoefficient_smooth : IsSmooth σP :=
  isSmooth_comp φ
    ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _) hσ

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

local notation "hSI" => splitStagesSection_mem s P H hsH
local notation "hHPc" => (hH.preimage (continuous_subtype_val : Continuous P.subtype))
local notation "χ" => Jacquet.complexCharacter (splitKernelHaarRatio rP sP HP hSI hHPc)
local notation "κ" => twist χ (splitKernelCoefficientAction rP sP HP hSI σP)

/-- The inner relative integral after identifying the two actual kernel subgroups. -/
def splitStagesInnerEquiv :
    Representation.Equiv
      (((compactInduced HP σP).toCoinvariants (r.ker.subgroupOf P)).comp sP) κ := by
  let : LocallyCompactSpace P := hP.locallyCompactSpace
  let eN := normalCoinvariantsCongr ρP (splitStagesRetraction_ker r s hrs P hker).symm
  exact (restrictAlongEquiv sP eN).trans
    (splitKernelCompactEquivariantEquiv rP sP HP hSI
      (splitStagesRetraction_section r s hrs P hker)
      (continuous_splitStagesRetraction r s hrs P hker hr)
      (continuous_splitStagesSection s P hs) hHPc σP
      (splitStagesCoefficient_smooth P H hHP σ hσ)
      ν hKernelBasis μN μI hCompatible)

/-- The relative integral with local compactness of P derived from closedness. -/
def splitStagesInnerIntegral : CompactFunctions HP σP →ₗ[ℂ]
    Representation.Coinvariants ((σP).comp ((rP).ker.subtype.subgroupComap HP)) := by
  let : LocallyCompactSpace P := hP.locallyCompactSpace
  exact splitKernelCompactIntegral rP sP
    (splitStagesRetraction_section r s hrs P hker)
    (continuous_splitStagesRetraction r s hrs P hker hr)
    (continuous_splitStagesSection s P hs) HP hHPc hSI σP
    (splitStagesCoefficient_smooth P H hHP σ hσ) ν

omit [IsTopologicalGroup L] in
@[simp] theorem splitStagesInnerEquiv_mk (f : CompactFunctions HP σP) :
    splitStagesInnerEquiv r s hrs hr hs P H hker hHP hP hH hsH σ hσ
        ν hKernelBasis μN μI hCompatible
        (Representation.Coinvariants.mk
          ((compactInduced HP σP).comp (r.ker.subgroupOf P).subtype) f) =
      splitStagesInnerIntegral r s hrs hr hs P H hker hHP hP hH hsH σ hσ ν f := by
  let : LocallyCompactSpace P := hP.locallyCompactSpace
  change splitKernelCompactEquivariantEquiv rP sP HP hSI
      (splitStagesRetraction_section r s hrs P hker)
      (continuous_splitStagesRetraction r s hrs P hker hr)
      (continuous_splitStagesSection s P hs) hHPc σP
      (splitStagesCoefficient_smooth P H hHP σ hσ) ν hKernelBasis μN μI hCompatible
      (normalCoinvariantsCongr ρP (splitStagesRetraction_ker r s hrs P hker).symm
        (Representation.Coinvariants.mk _ f)) = _
  rw [normalCoinvariantsCongr_mk]
  rfl

/-- The actual compact function on the intermediate subgroup at an outer point. -/
def splitStagesSlice (f : CompactFunctions H σ) (x : G) : CompactFunctions HP σP :=
  eval P ρP ((compactStagesEquiv H P hHP σ hH hP).symm f).val x

omit [T2Space G] in
@[simp] theorem splitStagesSlice_eval (f : CompactFunctions H σ) (x : G) (q : P) :
    eval HP σP (splitStagesSlice P H hHP hP hH σ f x).val q =
      eval H σ f.val ((q : G) * x) := rfl

/-- The coefficient map is the actual map on the intersection coinvariants. -/
def splitStagesCoefficientMap
    {W : Type uW} [AddCommGroup W] [Module ℂ W]
    {τ : Representation ℂ H W} (T : σ.IntertwiningMap τ) :
    Representation.IntertwiningMap κ
      (twist χ (splitKernelCoefficientAction rP sP HP hSI (τ.comp φ))) :=
  twistIntertwining χ
    { toLinearMap := Representation.Coinvariants.map _ _
        (splitKernelInducingMap rP HP (restrictAlongMap φ T))
      isIntertwining' l := LinearMap.ext fun z =>
        splitKernelCoefficientAction_natural rP sP HP hSI σP
          (restrictAlongMap φ T) l z }

variable {W : Type uW} [AddCommGroup W] [Module ℂ W]
variable {τ : Representation ℂ H W} (hτ : IsSmooth τ) (T : σ.IntertwiningMap τ)

omit [T2Space G] in
/-- The compact slice commutes with coefficient postcomposition. -/
theorem splitStagesSlice_natural (f : CompactFunctions H σ) (x : G) :
    splitStagesSlice P H hHP hP hH τ (compactInducedMap H T f) x =
      compactInducedMap HP (restrictAlongMap φ T) (splitStagesSlice P H hHP hP hH σ f x) := by
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  funext q
  rfl

omit [T2Space G] [IsTopologicalGroup L] in
/-- The raw inner integral commutes with the actual coefficient quotient map. -/
theorem splitStagesInnerIntegral_natural (f : CompactFunctions HP σP) :
    splitStagesInnerIntegral r s hrs hr hs P H hker hHP hP hH hsH τ hτ ν
        (compactInducedMap HP (restrictAlongMap φ T) f) =
      splitStagesCoefficientMap r s hrs P H hker hHP hH hsH σ T
        (splitStagesInnerIntegral r s hrs hr hs P H hker hHP hP hH hsH σ hσ ν f) := by
  let : LocallyCompactSpace P := hP.locallyCompactSpace
  exact splitKernelCompactIntegral_natural rP sP
    (splitStagesRetraction_section r s hrs P hker)
    (continuous_splitStagesRetraction r s hrs P hker hr)
    (continuous_splitStagesSection s P hs) HP hHPc hSI σP
    (splitStagesCoefficient_smooth P H hHP σ hσ) ν
    (splitStagesCoefficient_smooth P H hHP τ hτ) (restrictAlongMap φ T) f

omit [IsTopologicalGroup L] in
/-- The restricted inner integral commutes with every coefficient intertwiner. -/
theorem splitStagesInnerEquiv_natural
    (z : Representation.Coinvariants ((compactInduced HP σP).comp (r.ker.subgroupOf P).subtype)) :
    splitStagesInnerEquiv r s hrs hr hs P H hker hHP hP hH hsH τ hτ
        ν hKernelBasis μN μI hCompatible
        (Representation.Coinvariants.map _ _
          (Jacquet.restrictMap (compactInducedMap HP (restrictAlongMap φ T))
            (r.ker.subgroupOf P)) z) =
      splitStagesCoefficientMap r s hrs P H hker hHP hH hsH σ T
        (splitStagesInnerEquiv r s hrs hr hs P H hker hHP hP hH hsH σ hσ
          ν hKernelBasis μN μI hCompatible z) := by
  let : LocallyCompactSpace P := hP.locallyCompactSpace
  induction z using Representation.Coinvariants.induction_on with
  | h f =>
    change splitStagesInnerEquiv r s hrs hr hs P H hker hHP hP hH hsH τ hτ
        ν hKernelBasis μN μI hCompatible
        (Representation.Coinvariants.mk _ (compactInducedMap HP (restrictAlongMap φ T) f)) = _
    rw [splitStagesInnerEquiv_mk, splitStagesInnerEquiv_mk]
    exact splitStagesInnerIntegral_natural r s hrs hr hs P H hker hHP hP hH hsH σ hσ
      ν hτ T f

variable (hN : IsClosed (r.ker : Set G))
variable (hBasis : ∀ O : Set G, IsOpen O → (1 : G) ∈ O →
  ∃ U : OpenSubgroup G, IsCompact (U : Set G) ∧ (U : Set G) ⊆ O)

/-- Compact stages followed by the outer quotient and inner actual quotient integral. -/
def splitStagesCompactEquiv :
    Representation.Equiv (((compactInduced H σ).toCoinvariants r.ker).comp s)
      (compactInduced K κ) := by
  let : LocallyCompactSpace P := hP.locallyCompactSpace
  let eStages := compactStagesEquiv H P hHP σ hH hP
  let eOuter := normalSplitCompactEquiv hBasis r s hr hs hrs P hP hN hker
    ρP (compactInduced_smooth HP σP)
  let eInner := splitStagesInnerEquiv r s hrs hr hs P H hker hHP hP hH hsH σ hσ
    ν hKernelBasis μN μI hCompatible
  exact (restrictAlongEquiv s (normalCoinvariantsEquiv r.ker eStages.symm)).trans
    (eOuter.trans (compactInducedEquiv K eInner))

/-- The actual compact kernel function at an outer Levi coordinate. -/
def splitStagesKernelSlice (f : CompactFunctions H σ) (l : L) :
    CompactFunctions ((HP).comap (rP).ker.subtype)
      ((σP).comp ((rP).ker.subtype.subgroupComap HP)) := by
  let : LocallyCompactSpace P := hP.locallyCompactSpace
  exact splitKernelCompactEquiv rP sP
    (splitStagesRetraction_section r s hrs P hker)
    (continuous_splitStagesRetraction r s hrs P hker hr)
    (continuous_splitStagesSection s P hs) HP hHPc hSI σP
    (splitStagesCoefficient_smooth P H hHP σ hσ)
    (splitStagesSlice P H hHP hP hH σ f (s l))

omit [T2Space G] [IsTopologicalGroup L]
  [LocallyCompactSpace (rP).ker]
  [MeasurableSpace (rP).ker] [BorelSpace (rP).ker]
  [MeasurableSpace ((HP).comap (rP).ker.subtype)]
  [BorelSpace ((HP).comap (rP).ker.subtype)]
  [MeasurableSpace (LeftQuotient ((HP).comap (rP).ker.subtype))]
  [BorelSpace (LeftQuotient ((HP).comap (rP).ker.subtype))] in
@[simp] theorem splitStagesKernelSlice_eval (f : CompactFunctions H σ) (l : L)
    (n : (rP).ker) :
    eval ((HP).comap (rP).ker.subtype) ((σP).comp ((rP).ker.subtype.subgroupComap HP))
      (splitStagesKernelSlice r s hrs hr hs P H hker hHP hP hH hsH σ hσ f l).val n =
      eval H σ f.val (((n : P) : G) * s l) := rfl

omit [T2Space G] [IsTopologicalGroup L]
  [LocallyCompactSpace (rP).ker]
  [MeasurableSpace (rP).ker] [BorelSpace (rP).ker]
  [MeasurableSpace ((HP).comap (rP).ker.subtype)]
  [BorelSpace ((HP).comap (rP).ker.subtype)] in
/-- The simple-function integrand is precisely the class of f(n*s(l)). -/
@[simp] theorem splitStagesIntegrand_mk (f : CompactFunctions H σ) (l : L)
    (n : (rP).ker) :
    quotientCoinvariantSimple ((HP).comap (rP).ker.subtype)
      ((σP).comp ((rP).ker.subtype.subgroupComap HP))
      (splitStagesKernelSlice r s hrs hr hs P H hker hHP hP hH hsH σ hσ f l)
      (quotientMap ((HP).comap (rP).ker.subtype) n) =
      Representation.Coinvariants.mk ((σP).comp ((rP).ker.subtype.subgroupComap HP))
        (eval H σ f.val (((n : P) : G) * s l)) := rfl

/-- Evaluation is the inner relative integral of the actual slice f(q*s(l)). -/
@[simp] theorem splitStagesCompactEquiv_eval_mk (f : CompactFunctions H σ) (l : L) :
    eval K κ
      (splitStagesCompactEquiv r s hrs hr hs P H hker hHP hP hH hsH σ hσ
        ν hKernelBasis μN μI hCompatible hN hBasis
        (Representation.Coinvariants.mk ((compactInduced H σ).comp r.ker.subtype) f)).val l =
      splitStagesInnerIntegral r s hrs hr hs P H hker hHP hP hH hsH σ hσ ν
        (splitStagesSlice P H hHP hP hH σ f (s l)) := by
  let : LocallyCompactSpace P := hP.locallyCompactSpace
  change splitStagesInnerEquiv r s hrs hr hs P H hker hHP hP hH hsH σ hσ
      ν hKernelBasis μN μI hCompatible
      (eval K (((ρP).toCoinvariants (r.ker.subgroupOf P)).comp sP)
        (normalSplitCompactEquiv hBasis r s hr hs hrs P hP hN hker
          ρP (compactInduced_smooth HP σP)
          (Representation.Coinvariants.mk _
            ((compactStagesEquiv H P hHP σ hH hP).symm f))).val l) = _
  exact (congrArg
    (splitStagesInnerEquiv r s hrs hr hs P H hker hHP hP hH hsH σ hσ
      ν hKernelBasis μN μI hCompatible)
    (normalSplitCompactEquiv_eval_mk hBasis r s hr hs hrs P hP hN hker
      ρP (compactInduced_smooth HP σP) ((compactStagesEquiv H P hHP σ hH hP).symm f) l)).trans
    (splitStagesInnerEquiv_mk r s hrs hr hs P H hker hHP hP hH hsH σ hσ
      ν hKernelBasis μN μI hCompatible (splitStagesSlice P H hHP hP hH σ f (s l)))

/-- The composite is the supplied compatible quotient integral, with no scalar hidden. -/
theorem splitStagesCompactEquiv_eval_mk_integral (f : CompactFunctions H σ) (l : L) :
    eval K κ
      (splitStagesCompactEquiv r s hrs hr hs P H hker hHP hP hH hsH σ hσ
        ν hKernelBasis μN μI hCompatible hN hBasis
        (Representation.Coinvariants.mk ((compactInduced H σ).comp r.ker.subtype) f)).val l =
      AlgebraicIntegral.integral ν
        (quotientCoinvariantSimple ((HP).comap (rP).ker.subtype)
          ((σP).comp ((rP).ker.subtype.subgroupComap HP))
          (splitStagesKernelSlice r s hrs hr hs P H hker hHP hP hH hsH σ hσ f l)) :=
  splitStagesCompactEquiv_eval_mk r s hrs hr hs P H hker hHP hP hH hsH σ hσ
    ν hKernelBasis μN μI hCompatible hN hBasis f l

/-- The assembled comparison is natural for all smooth coefficient intertwiners. -/
theorem splitStagesCompactEquiv_natural
    (z : Representation.Coinvariants ((compactInduced H σ).comp r.ker.subtype)) :
    splitStagesCompactEquiv r s hrs hr hs P H hker hHP hP hH hsH τ hτ
        ν hKernelBasis μN μI hCompatible hN hBasis
        (Representation.Coinvariants.map _ _
          (Jacquet.restrictMap (compactInducedMap H T) r.ker) z) =
      compactInducedMap K (splitStagesCoefficientMap r s hrs P H hker hHP hH hsH σ T)
        (splitStagesCompactEquiv r s hrs hr hs P H hker hHP hP hH hsH σ hσ
          ν hKernelBasis μN μI hCompatible hN hBasis z) := by
  let : LocallyCompactSpace P := hP.locallyCompactSpace
  induction z using Representation.Coinvariants.induction_on with
  | h f =>
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    funext l
    change eval K _
        (splitStagesCompactEquiv r s hrs hr hs P H hker hHP hP hH hsH τ hτ
          ν hKernelBasis μN μI hCompatible hN hBasis
          (Representation.Coinvariants.mk _ (compactInducedMap H T f))).val l =
      splitStagesCoefficientMap r s hrs P H hker hHP hH hsH σ T
        (eval K κ (splitStagesCompactEquiv r s hrs hr hs P H hker hHP hP hH hsH σ hσ
          ν hKernelBasis μN μI hCompatible hN hBasis (Representation.Coinvariants.mk _ f)).val l)
    calc
      _ = splitStagesInnerIntegral r s hrs hr hs P H hker hHP hP hH hsH τ hτ ν
            (splitStagesSlice P H hHP hP hH τ (compactInducedMap H T f) (s l)) :=
        splitStagesCompactEquiv_eval_mk r s hrs hr hs P H hker hHP hP hH hsH τ hτ
          ν hKernelBasis μN μI hCompatible hN hBasis (compactInducedMap H T f) l
      _ = splitStagesInnerIntegral r s hrs hr hs P H hker hHP hP hH hsH τ hτ ν
            (compactInducedMap HP (restrictAlongMap φ T)
              (splitStagesSlice P H hHP hP hH σ f (s l))) :=
        congrArg (splitStagesInnerIntegral r s hrs hr hs P H hker hHP hP hH hsH τ hτ ν)
          (splitStagesSlice_natural P H hHP hP hH σ T f (s l))
      _ = splitStagesCoefficientMap r s hrs P H hker hHP hH hsH σ T
            (splitStagesInnerIntegral r s hrs hr hs P H hker hHP hP hH hsH σ hσ ν
              (splitStagesSlice P H hHP hP hH σ f (s l))) :=
        splitStagesInnerIntegral_natural r s hrs hr hs P H hker hHP hP hH hsH σ hσ
          ν hτ T (splitStagesSlice P H hHP hP hH σ f (s l))
      _ = _ := congrArg (splitStagesCoefficientMap r s hrs P H hker hHP hH hsH σ T)
        (splitStagesCompactEquiv_eval_mk r s hrs hr hs P H hker hHP hP hH hsH σ hσ
          ν hKernelBasis μN μI hCompatible hN hBasis f l).symm

end Assembly

end Langlands.Induction
