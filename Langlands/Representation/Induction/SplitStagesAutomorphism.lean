import Langlands.Representation.Induction.SplitStagesComparison
import Langlands.Analysis.Local.QuotientAutomorphismStatement

/-!
# Automorphism covariance of the compact stages integral

The actual compact stages comparison commutes with inverse pullback and
coefficient transport when the induced inverse map on the inner quotient
preserves its measure.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.Induction

open MeasureTheory MeasureTheory.Measure QuotientIntegration HarmonicAnalysis
open Representation (Coinvariants)

universe uG uL uV

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G]
  {L : Type uL} [Group L] [TopologicalSpace L] [IsTopologicalGroup L]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  (r : G →* L) (s : L →* G) (hrs : ∀ l, r (s l) = l)
  (hr : Continuous r) (hs : Continuous s)
  (P H : Subgroup G) (hker : r.ker ≤ P) (hHP : H ≤ P)
  (hP : IsClosed (P : Set G)) (hH : IsClosed (H : Set G))
  (hsH : ∀ l : P.comap s, s (l : L) ∈ H)
  (σ : Representation ℂ H V) (hσ : IsSmooth σ)

local notation "K" => P.comap s
local notation "HP" => H.subgroupOf P
local notation "rP" => splitStagesRetraction r s hrs P hker
local notation "N" => MonoidHom.ker rP
local notation "I" => Subgroup.comap (Subgroup.subtype N) HP
local notation "σP" => σ.comp (MulEquiv.toMonoidHom (Subgroup.subgroupOfEquivOfLe hHP))
local notation "σI" => MonoidHom.comp σP (MonoidHom.subgroupComap (Subgroup.subtype N) HP)

variable [LocallyCompactSpace (splitStagesRetraction r s hrs P hker).ker]
  [MeasurableSpace (splitStagesRetraction r s hrs P hker).ker]
  [BorelSpace (splitStagesRetraction r s hrs P hker).ker]
  [MeasurableSpace ((H.subgroupOf P).comap (splitStagesRetraction r s hrs P hker).ker.subtype)]
  [BorelSpace ((H.subgroupOf P).comap (splitStagesRetraction r s hrs P hker).ker.subtype)]
  [MeasurableSpace (LeftQuotient
    ((H.subgroupOf P).comap (splitStagesRetraction r s hrs P hker).ker.subtype))]
  [BorelSpace (LeftQuotient
    ((H.subgroupOf P).comap (splitStagesRetraction r s hrs P hker).ker.subtype))]
  (ν : Measure (LeftQuotient
    ((H.subgroupOf P).comap (splitStagesRetraction r s hrs P hker).ker.subtype)))
  [IsFiniteMeasureOnCompacts ν]
  (hKernelBasis : ∀ O : Set (splitStagesRetraction r s hrs P hker).ker,
    IsOpen O → (1 : (splitStagesRetraction r s hrs P hker).ker) ∈ O →
    ∃ U : OpenSubgroup (splitStagesRetraction r s hrs P hker).ker,
      IsCompact (U : Set (splitStagesRetraction r s hrs P hker).ker) ∧
        (U : Set (splitStagesRetraction r s hrs P hker).ker) ⊆ O)
  (μN : Measure (splitStagesRetraction r s hrs P hker).ker)
  (μI : Measure ((H.subgroupOf P).comap (splitStagesRetraction r s hrs P hker).ker.subtype))
  [IsHaarMeasure μN] [μN.Regular] [IsMulRightInvariant μN]
  [IsHaarMeasure μI] [μI.Regular] [IsMulRightInvariant μI]
  (hCompatible : IsCompatible
    ((H.subgroupOf P).comap (splitStagesRetraction r s hrs P hker).ker.subtype) μN μI ν)
  (hN : IsClosed (r.ker : Set G))
  (hBasis : ∀ O : Set G, IsOpen O → (1 : G) ∈ O →
    ∃ U : OpenSubgroup G, IsCompact (U : Set G) ∧ (U : Set G) ⊆ O)

local notation "comparison" => splitStagesCompactEquiv r s hrs hr hs P H hker hHP hP hH hsH σ hσ
  ν hKernelBasis μN μI hCompatible hN hBasis
local notation "slice" => splitStagesKernelSlice r s hrs hr hs P H hker hHP hP hH hsH σ hσ

/-- The compact stages comparison takes the two given compact functions to
evaluations related by the given operator on the intersection coinvariants. -/
def SplitStagesCompactEvalCovariance (A_I : Module.End ℂ (Coinvariants σI))
    (f f' : CompactFunctions H σ) (x y : L) : Prop :=
  eval K _ (comparison (Coinvariants.mk ((compactInduced H σ).comp r.ker.subtype) f')).val x =
    A_I (eval K _ (comparison (Coinvariants.mk ((compactInduced H σ).comp r.ker.subtype) f)).val y)

/-- Apply change of variables to the actual inner integral at the two section
points. The operator on coefficients descends through the intersection
coinvariant quotient by `hA`. -/
theorem splitStagesCompactEvalCovariance_of_measurePreserving
    (α : G ≃ₜ* G) (αN : N ≃ₜ* N) (hαI : ∀ t : N, αN t ∈ I ↔ t ∈ I)
    (hαN : ∀ t : N, (((αN t : N) : P) : G) = α ((t : P) : G))
    (hν : MeasurePreserving (quotientAutomorphism I αN hαI).symm ν ν)
    (A : Module.End ℂ V) (A_I : Module.End ℂ (Coinvariants σI))
    (hA : ∀ v, A_I (Coinvariants.mk σI v) = Coinvariants.mk σI (A v))
    (f f' : CompactFunctions H σ)
    (hf : ∀ g, eval H σ f'.val g = A (eval H σ f.val (α.symm g)))
    (x y : L) (hxy : α (s y) = s x) :
    SplitStagesCompactEvalCovariance r s hrs hr hs P H hker hHP hP hH hsH σ hσ
      ν hKernelBasis μN μI hCompatible hN hBasis A_I f f' x y := by
  have hinv (t : N) : α.symm ((t : P) : G) = (((αN.symm t : N) : P) : G) := by
    apply α.injective
    rw [α.apply_symm_apply, ← hαN, αN.apply_symm_apply]
  have hsection : α.symm (s x) = s y := by
    rw [← hxy, α.symm_apply_apply]
  let e := (quotientAutomorphism I αN hαI).symm
  let φ := quotientCoinvariantSimple I σI (slice f y)
  have hφ : φ.FinMeasSupp ν := quotientCoinvariantSimple_finMeasSupp I σI ν (slice f y)
  have hsimple : quotientCoinvariantSimple I σI (slice f' x) =
      (φ.comp e hν.measurable).map A_I := by
    apply SimpleFunc.ext
    intro q
    induction q using Quotient.inductionOn with
    | h t =>
      change Coinvariants.mk σI (eval H σ f'.val (((t : P) : G) * s x)) =
        A_I (Coinvariants.mk σI
          (eval H σ f.val ((((αN.symm t : N) : P) : G) * s y)))
      rw [hf, map_mul, hinv, hsection, hA]
  unfold SplitStagesCompactEvalCovariance
  rw [splitStagesCompactEquiv_eval_mk_integral, splitStagesCompactEquiv_eval_mk_integral, hsimple]
  change AlgebraicIntegral.integral ν ((φ.comp e hν.measurable).map A_I) =
    A_I (AlgebraicIntegral.integral ν φ)
  have hfinite : (φ.comp e hν.measurable).FinMeasSupp ν :=
    (AlgebraicIntegral.finMeasSupp_comp_measurePreserving φ e hν).mpr hφ
  rw [AlgebraicIntegral.integral_linearMap _ hfinite,
    AlgebraicIntegral.integral_comp_measurePreserving φ e hν]

end Langlands.Induction
