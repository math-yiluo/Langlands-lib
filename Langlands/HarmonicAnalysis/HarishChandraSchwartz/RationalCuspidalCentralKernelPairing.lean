import Langlands.Group.GL.LeviCentralQuotientMeasure
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalCuspidalCentralKernelDiagonal
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.CentralQuotientHaar

/-! # The VIII.4.1 pairing input from the VIII.3.2 integrability form

This module reduces `RationalLevelKernelPairingIntegrable` (from
`RationalCuspidalCentralKernelDiagonal`) to `RationalLevelKernelConjugationIntegrable`. That is
the integrability of Task 7256's descended conjugation pairings of `E` with every Schwartz
function, which is the form of the VIII.3.2 conclusion at `f₁ = E`. Two facts are proved on the
way. Compatible quotient measures on `A \ G` for closed central `A` are invariant under the
inversion `A g ↦ A g⁻¹`. The characteristic function of `H a`, for central `a`, lies in the
Schwartz space.
-/

noncomputable section

open MeasureTheory MeasureTheory.Measure Langlands.QuotientIntegration
open scoped ENNReal NNReal

namespace Langlands.HarishChandraSchwartz

universe u uG

section QuotientInversion

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G]
  {A : Subgroup G} [A.Normal]

/-- The inversion `A g ↦ A g⁻¹` of `A \ G` for a normal subgroup `A`. -/
def quotientInv (A : Subgroup G) [A.Normal] (q : LeftQuotient A) : LeftQuotient A :=
  (normalLeftQuotientHomeomorph A).symm ((normalLeftQuotientHomeomorph A q)⁻¹)

omit [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G] in
@[simp] theorem quotientInv_mk (g : G) :
    quotientInv A (Quotient.mk _ g) = Quotient.mk _ g⁻¹ := by
  rw [quotientInv, normalLeftQuotientHomeomorph_mk, Homeomorph.symm_apply_eq,
    normalLeftQuotientHomeomorph_mk, QuotientGroup.mk_inv]

omit [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G]
  [BorelSpace G] in
theorem continuous_quotientInv : Continuous (quotientInv A) :=
  (normalLeftQuotientHomeomorph A).symm.continuous.comp
    (continuous_inv.comp (normalLeftQuotientHomeomorph A).continuous)

variable (hA : IsClosed (A : Set G)) (hAc : A ≤ Subgroup.center G)
  [MeasurableSpace A] [BorelSpace A]
  {μG : Measure G} [μG.IsMulLeftInvariant]
  {μA : Measure A} [IsHaarMeasure μA] [μA.Regular] [IsMulRightInvariant μA]
  [MeasurableSpace (LeftQuotient A)] [BorelSpace (LeftQuotient A)]
  {ν : Measure (LeftQuotient A)}

include hA hAc in
/-- A compatible quotient measure on `A \ G`, for closed central `A`, is invariant under the
inversion `A g ↦ A g⁻¹`. Its image on the group `G ⧸ A` is a nonzero multiple of a Haar measure
that is left invariant (`IsCompatible.isMulLeftInvariant_map_normalLeftQuotientHomeomorph`) and
right invariant (`IsCompatible.right_invariant`), hence invariant under inversion. -/
theorem IsCompatible.measurePreserving_quotientInv (hν : IsCompatible A μG μA ν) :
    MeasurePreserving (quotientInv A) ν ν := by
  let _ : MeasurableSpace (G ⧸ A) := borel _
  have : BorelSpace (G ⧸ A) := ⟨rfl⟩
  have : IsClosed (A : Set G) := hA
  set e := normalLeftQuotientHomeomorph A with hedef
  have he : Measurable e := e.continuous.measurable
  have hes : Measurable e.symm := e.symm.continuous.measurable
  let μ₀ : Measure (G ⧸ A) := Measure.haar
  obtain ⟨c, hc0, hc⟩ := hν.exists_smul_eq_map hA hAc μ₀
  have hright : ∀ x : G ⧸ A, Measure.map (· * x) (Measure.map e ν) = Measure.map e ν := by
    intro x
    induction x using QuotientGroup.induction_on with
    | H g =>
      have hcomm : (fun y : G ⧸ A => y * (g : G ⧸ A)) ∘ e = e ∘ rightTranslate A g := by
        funext q
        induction q using Quotient.inductionOn with
        | h x => rfl
      rw [Measure.map_map (measurable_mul_const _) he, hcomm,
        ← Measure.map_map he (hν.right_invariant g).measurable, (hν.right_invariant g).map_eq]
  have : μ₀.IsMulRightInvariant := ⟨fun x => by
    have h := hright x
    rw [hc, Measure.map_smul _ (measurable_mul_const x).aemeasurable] at h
    have h' := congrArg (fun m : Measure (G ⧸ A) => c⁻¹ • m) h
    simpa only [inv_smul_smul₀ hc0] using h'⟩
  have : μ₀.IsInvInvariant := Langlands.isInvInvariant_of_isMulRightInvariant μ₀
  have hinv : Measure.map Inv.inv (Measure.map e ν) = Measure.map e ν := by
    rw [hc, Measure.map_smul _ continuous_inv.measurable.aemeasurable, map_inv_eq_self]
  have hcomp : quotientInv A = e.symm ∘ Inv.inv ∘ e := rfl
  refine ⟨continuous_quotientInv.measurable, ?_⟩
  rw [hcomp, ← Measure.map_map hes (continuous_inv.measurable.comp he),
    ← Measure.map_map continuous_inv.measurable he, hinv, Measure.map_map hes he]
  simp

end QuotientInversion

section CosetIndicator

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {Ξ σ : G → ℝ}

/-- For central `a` and a compact open subgroup `H`, the characteristic function of `H a` lies
in the level `C_H` of the Schwartz space: it is `H`-bi-invariant, continuous and compactly
supported. -/
theorem rightCosetIndicator_mem_levelSubmodule (hΞc : Continuous Ξ) (hΞ : ∀ g, 0 < Ξ g)
    (hσc : Continuous σ) (hσ : ∀ g, 0 ≤ σ g) (H : CompactOpenSubgroup G) {a : G}
    (ha : a ∈ Subgroup.center G) :
    rightCosetIndicator H.toSubgroup a ∈ levelSubmodule Ξ σ H.toSubgroup := by
  have hbi : IsBiInvariant H.toSubgroup (rightCosetIndicator H.toSubgroup a) := by
    intro k₁ hk₁ k₂ hk₂ g
    have hc : k₂ * a⁻¹ = a⁻¹ * k₂ :=
      (Subgroup.mem_center_iff.mp (Subgroup.inv_mem _ ha) k₂)
    have e : k₁ * g * k₂ * a⁻¹ = k₁ * (g * a⁻¹) * k₂ := by
      rw [mul_assoc (k₁ * g), hc, ← mul_assoc, mul_assoc k₁]
    simp only [rightCosetIndicator, e]
    by_cases hg : g * a⁻¹ ∈ (H.toSubgroup : Set G)
    · rw [Set.indicator_of_mem hg, Set.indicator_of_mem]
      exact H.toSubgroup.mul_mem (H.toSubgroup.mul_mem hk₁ hg) hk₂
    · rw [Set.indicator_of_notMem hg, Set.indicator_of_notMem]
      intro h
      apply hg
      have h2 := H.toSubgroup.mul_mem (H.toSubgroup.mul_mem (H.toSubgroup.inv_mem hk₁) h)
        (H.toSubgroup.inv_mem hk₂)
      simpa [mul_assoc] using h2
  have hcpt : IsCompact ((fun h : G => h * a) '' (H.toSubgroup : Set G)) :=
    H.2.image (continuous_id.mul continuous_const)
  have hsupp : HasCompactSupport (rightCosetIndicator H.toSubgroup a) := by
    refine HasCompactSupport.intro hcpt fun x hx => ?_
    simp only [rightCosetIndicator]
    rw [Set.indicator_of_notMem]
    intro h
    exact hx ⟨x * a⁻¹, h, by simp⟩
  exact ⟨hbi, nu_lt_top_of_hasCompactSupport hΞc hΞ hσc hσ
    (IsBiInvariant.isLocallyConstant (K := H) hbi).continuous hsupp⟩

end CosetIndicator

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology Langlands.Plancherel
open Langlands.Aubert.General

attribute [local instance] rationalWeightsIsAffine rationalWeightsTopology
  rationalWeightsTopologicalGroup rationalWeightsT2Field rationalWeightsLocallyCompact
  rationalWeightsMeasurableSpace rationalWeightsBorelSpace

section Rational

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {S T : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom]
  {i : S.toGrp ⟶ G} {ν : cocharacterLattice S} {s : T.toGrp ⟶ G}
  {K : OpenSubgroup (rationalPoints G)}
  (hKc : IsCompact (K : Set (rationalPoints G)))
  (hPK : IsIwasawaPair (standardParabolicPoints i ν ∅) (K : Subgroup (rationalPoints G)))
  {N : ℕ} [Nonempty (Fin N)] (ρ : MatrixRepresentation G (Fin N))

local instance rationalKernelPairingSecondCountable :
    SecondCountableTopology (rationalPoints G) :=
  rationalPoint_secondCountableTopology F G
local instance rationalKernelPairingT2 : T2Space (rationalPoints G) := rationalPoint_t2Space F G

/-- The characteristic function of `H a`, for a compact open `H` and `a ∈ A_G(F)`, as an element
of the actual rational Schwartz space. -/
def rationalRightCosetIndicator (hs : IsSplitComponent s) (H : OpenSubgroup (rationalPoints G))
    (hHc : IsCompact (H : Set (rationalPoints G))) (a : (rationalPoints.map s).range) :
    RationalSchwartzSpace hKc hPK ρ :=
  (⟨rightCosetIndicator H.toSubgroup (a : rationalPoints G),
    levelSubmodule_le_schwartzSubmodule _ _ ⟨H, hHc⟩
      (rightCosetIndicator_mem_levelSubmodule (continuous_rationalXi K.isOpen hKc hPK)
        (rationalXi_pos K.isOpen hKc hPK) (continuous_rationalHeight ρ) (rationalHeight_nonneg ρ)
        ⟨H, hHc⟩ (hs.isCentralSplitTorus.isCentral.range_le_center a.2))⟩ :
    schwartzSubmodule _ _)

@[simp] theorem coe_rationalRightCosetIndicator (hs : IsSplitComponent s)
    (H : OpenSubgroup (rationalPoints G)) (hHc : IsCompact (H : Set (rationalPoints G)))
    (a : (rationalPoints.map s).range) :
    ((rationalRightCosetIndicator hKc hPK ρ hs H hHc a : RationalSchwartzSpace hKc hPK ρ) :
      rationalPoints G → ℂ) = rightCosetIndicator H.toSubgroup (a : rationalPoints G) :=
  rfl

/-- **The VIII.3.2 integrability form at `E`.** For every right-invariance instance on `muA`,
every Borel structure on `A_G(F) \ G(F)`, every compatible quotient measure `muQ` and every `f₂`
in the actual Schwartz space, the descended conjugation pairing
`q ↦ ∫ E(q̇ g q̇⁻¹) f₂(g) dmuG(g)` (`rationalLeftConjugationPairing`) is `muQ`-integrable. This is the
second conjunct of Task 7256's `RationalCuspidalConjugationIntegrability` at `f₁ = E`. -/
def RationalLevelKernelConjugationIntegrable (hs : IsSplitComponent s)
    (muA : Measure (rationalPoints.map s).range) (muG : Measure (rationalPoints G))
    (E : RationalSchwartzSpace hKc hPK ρ) : Prop :=
  ∀ [muA.IsMulRightInvariant] [MeasurableSpace (LeftQuotient (rationalPoints.map s).range)]
    [BorelSpace (LeftQuotient (rationalPoints.map s).range)]
    (muQ : Measure (LeftQuotient (rationalPoints.map s).range)),
    IsCompatible (rationalPoints.map s).range muG muA muQ →
    ∀ f₂ : RationalSchwartzSpace hKc hPK ρ,
      Integrable (rationalLeftConjugationPairing hKc hPK ρ s hs muG E f₂) muQ

/-- **The pairing input from the VIII.3.2 integrability form.** From
`RationalLevelKernelConjugationIntegrable` (the VIII.3.2 form at `f₁ = E`), `RationalLevelKernelPairingIntegrable` holds
for every compact open `H`: take `f₂ = 1_{H a}` and transport from `q̇` to `q̇⁻¹` by the
measure-preserving inversion of `A_G(F) \ G(F)`. -/
theorem RationalLevelKernelPairingIntegrable.of_leftConjugationPairing (hs : IsSplitComponent s)
    (muA : Measure (rationalPoints.map s).range) [muA.IsHaarMeasure]
    (muG : Measure (rationalPoints G)) [muG.IsHaarMeasure]
    (H : OpenSubgroup (rationalPoints G)) (hHc : IsCompact (H : Set (rationalPoints G)))
    (E : RationalSchwartzSpace hKc hPK ρ)
    (h32 : RationalLevelKernelConjugationIntegrable hKc hPK ρ hs muA muG E) :
    RationalLevelKernelPairingIntegrable hKc hPK ρ muA muG H E := by
  intro _ _ _ muQ hQ a
  have hA : IsClosed ((rationalPoints.map s).range : Set (rationalPoints G)) :=
    isClosed_range_splitComponent G s hs
  have hAc : (rationalPoints.map s).range ≤ Subgroup.center (rationalPoints G) :=
    hs.isCentralSplitTorus.isCentral.range_le_center
  have : (rationalPoints.map s).range.Normal := rationalSplitCenter_normal s hs
  have : LocallyCompactSpace (rationalPoints.map s).range :=
    hA.isClosedEmbedding_subtypeVal.locallyCompactSpace
  have : SecondCountableTopology (rationalPoints.map s).range :=
    inferInstanceAs (SecondCountableTopology
      ((rationalPoints.map s).range : Set (rationalPoints G)))
  have hι := IsCompatible.measurePreserving_quotientInv hA hAc hQ
  have hint := h32 muQ hQ (rationalRightCosetIndicator hKc hPK ρ hs H hHc a)
  have heq : (fun q : LeftQuotient (rationalPoints.map s).range =>
      conjugationPairing muG (E : rationalPoints G → ℂ)
        (rightCosetIndicator H.toSubgroup (a : rationalPoints G)) (q.out)⁻¹) =
      rationalLeftConjugationPairing hKc hPK ρ s hs muG E
        (rationalRightCosetIndicator hKc hPK ρ hs H hHc a) ∘
          quotientInv (rationalPoints.map s).range := by
    funext q
    conv_rhs => rw [← Quotient.out_eq q]
    rw [Function.comp_apply, quotientInv_mk, rationalLeftConjugationPairing_mk]
    rfl
  rw [heq]
  exact (hι.integrable_comp hint.aestronglyMeasurable).mpr hint

end Rational

end Langlands.HarishChandraSchwartz
