import Langlands.Representation.Aubert.General.InductionFiniteLengthReflection
import Langlands.Representation.Aubert.General.RestrictedLeviTopology
import Langlands.Representation.Aubert.General.RationalInductionStagesGeometry
import Langlands.Representation.Induction.SmoothTransitivity
import Langlands.Representation.Induction.SmoothSplitQuotient
import Langlands.Representation.Induction.Equivalences
import Langlands.Representation.Smooth.FiniteLengthGrothendieckTwist
import Langlands.Representation.Smooth.FiniteLengthGrothendieckTransport

/-! # Ordinary induction in stages for nested semidirect decompositions -/

noncomputable section
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

open scoped MonoidAlgebra

namespace Langlands.Aubert.General

universe uG uV uW

private theorem finiteLength_of_representationEquiv
    {G : Type uG} [Group G]
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    {W : Type uW} [AddCommGroup W] [Module ℂ W]
    {ρ : Representation ℂ G V} {σ : Representation ℂ G W}
    (e : ρ.Equiv σ) (hρ : IsFiniteLength ℂ[G] ρ.asModule) :
    IsFiniteLength ℂ[G] σ.asModule :=
  hρ.of_surjective
    (f := Representation.IntertwiningMap.equivLinearMapAsModule _ _ e.toIntertwiningMap)
    e.toLinearEquiv.surjective

section Ordinary

variable {G : Type uG} [Group G] [TopologicalSpace G]
  [LocallyCompactSpace G] [NonarchimedeanGroup G]
  {P M U : Subgroup G} (h : IsSemidirectDecomposition P M U)
  (hU : IsClosed (U : Set G))

/-- Inverse twisting on the Levi cancels the actual parabolic normalization
when the radical is unimodular. The map on induced functions is pointwise. -/
def ordinaryInductionAsNormalizedEquiv (hδ : IsUnimodularModulus U hU)
    (A : SmoothRep.{0, uG, uV} ℂ M) :
    let χ := HaarModulus.closedHalfCharacter U hU M h.levi_le_normalizer
    let hχ := HaarModulus.isOpen_ker_closedHalfCharacter U hU M h.levi_le_normalizer
    let hInv : IsOpen ((χ⁻¹).ker : Set M) := by
      have hk : (χ⁻¹).ker = χ.ker := by
        ext g
        simp
      simpa only [hk] using hχ
    (((normalizedInductionFunctor h hU).obj (A.twist χ⁻¹ hInv)).representation).Equiv
      (Induction.smoothInduced P (A.representation.comp h.projection)) := by
  dsimp only
  apply Induction.smoothInducedEquiv
  apply equivOfRepresentationEq
  ext p v
  change (HaarModulus.closedHalfCharacter U hU P h.le_normalizer p : ℂ) •
      ((HaarModulus.closedHalfCharacter U hU M h.levi_le_normalizer
        (h.projection p))⁻¹ : ℂˣ) • A.representation (h.projection p) v =
    A.representation (h.projection p) v
  rw [closedHalfCharacter_eq_comp_projection h hU hδ]
  simp only [MonoidHom.comp_apply, Units.smul_def, smul_smul,
    Units.val_inv_eq_inv_val, mul_inv_cancel₀ (Units.ne_zero _), one_smul]

/-- Ambient finite-length preservation for normalized induction also gives it
for ordinary induction of inflated smooth Levi coefficients. -/
theorem isFiniteLength_ordinaryInduction
    (hδ : IsUnimodularModulus U hU)
    (hiFl : SmoothRep.PreservesFiniteLength (normalizedInductionFunctor.{uG, uV} h hU))
    (A : SmoothRep.{0, uG, uV} ℂ M) (hA : A.HasFiniteLength) :
    IsFiniteLength ℂ[G]
      (Induction.smoothInduced P (A.representation.comp h.projection)).asModule := by
  let χ := HaarModulus.closedHalfCharacter U hU M h.levi_le_normalizer
  have hχ := HaarModulus.isOpen_ker_closedHalfCharacter U hU M h.levi_le_normalizer
  have hInv : IsOpen ((χ⁻¹).ker : Set M) := by
    have hk : (χ⁻¹).ker = χ.ker := by
      ext g
      simp
    simpa only [hk] using hχ
  have ht : (A.twist χ⁻¹ hInv).HasFiniteLength :=
    (finiteLength_twist_iff χ⁻¹ A.representation).mpr hA
  exact finiteLength_of_representationEquiv
    (ordinaryInductionAsNormalizedEquiv h hU hδ A)
    (hiFl (A.twist χ⁻¹ hInv) ht)

end Ordinary

section Stages

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {P₀ M₀ U₀ P₁ M₁ U₁ : Subgroup G}
  (h₀ : IsSemidirectDecomposition P₀ M₀ U₀)
  (h₁ : IsSemidirectDecomposition P₁ M₁ U₁)
  (hL : IsSemidirectDecomposition
    (P₀.subgroupOf M₁) (M₀.subgroupOf M₁) (U₀.subgroupOf M₁))
  (hP : P₀ ≤ P₁) (hM : M₀ ≤ M₁) (hU : U₁ ≤ U₀)
  (hproj : Continuous h₁.projection)
  (A : SmoothRep.{0, uG, uV} ℂ M₀)

local notation "HP" => P₀.subgroupOf P₁
local notation "φ" => MulEquiv.toMonoidHom (Subgroup.subgroupOfEquivOfLe hP)
local notation "σ" => A.representation.comp h₀.projection
local notation "s" => Subgroup.inclusion h₁.levi_le
local notation "eM" => MulEquiv.toMonoidHom (Subgroup.subgroupOfEquivOfLe hM)
local notation "τ" => MonoidHom.comp (A.representation.comp eM) hL.projection
local notation "σP" => MonoidHom.comp σ φ

include h₀ hU in
omit [TopologicalSpace G] [IsTopologicalGroup G] in
private theorem stages_kernel_le : h₁.projection.ker ≤ HP := by
  intro p hp
  exact h₀.unipotent_le (hU ((h₁.projection_eq_one_iff p).mp hp))

include hU in
omit [IsTopologicalGroup G] in
private theorem stages_kernel_trivial (p : HP)
    (hp : h₁.projection (p : P₁) = 1) (v : A) :
    (σP) p v = v := by
  have hu : ((p : P₁) : G) ∈ U₀ :=
    hU ((h₁.projection_eq_one_iff (p : P₁)).mp hp)
  have hz : h₀.projection (φ p) = 1 := (h₀.projection_eq_one_iff _).mpr hu
  change A.representation (h₀.projection (φ p)) v = v
  rw [hz, map_one]
  rfl

omit [IsTopologicalGroup G] in
private theorem stages_section_representation :
    (σP).comp ((s).subgroupComap HP) = τ := by
  ext p v
  have he := IsSemidirectDecomposition.projection_subgroupOf h₀ hL p
  have hp : h₀.projection (φ ((s).subgroupComap HP p)) = eM (hL.projection p) :=
    he.symm
  change A.representation (h₀.projection (φ ((s).subgroupComap HP p))) v =
    A.representation (eM (hL.projection p)) v
  rw [hp]

/-- Ordinary induction in stages followed by the actual split quotient
identifies fine induction with induction of the inflated inside-Levi induction.
No relation between three Haar moduli is used. -/
def ordinaryStagesInflationEquiv :
    (Induction.smoothInduced P₀ σ).Equiv
      (Induction.smoothInduced P₁ ((Induction.smoothInduced (P₀.subgroupOf M₁) τ).comp
        h₁.projection)) :=
by
  let e := Induction.smoothInducedEquiv (P₀.subgroupOf M₁)
    (equivOfRepresentationEq
      (stages_section_representation (h₀ := h₀) (h₁ := h₁) (hL := hL)
        (hP := hP) (hM := hM) (A := A)))
  let eInfl : Representation.Equiv
      ((Induction.smoothInduced (P₀.subgroupOf M₁)
        ((σP).comp ((s).subgroupComap HP))).comp h₁.projection)
      ((Induction.smoothInduced (P₀.subgroupOf M₁) τ).comp h₁.projection) :=
    { toLinearEquiv := e.toLinearEquiv
      isIntertwining' p := e.isIntertwining' (h₁.projection p) }
  exact (Induction.smoothStagesEquiv P₀ P₁ hP σ).symm.trans
    (Induction.smoothInducedEquiv P₁
      ((Induction.smoothSplitQuotientEquiv h₁.projection hproj s
        (continuous_subtype_val.subtype_mk _) h₁.projection_levi HP
        (stages_kernel_le (h₀ := h₀) (h₁ := h₁) (hU := hU)) (σP)
        (stages_kernel_trivial (h₀ := h₀) (h₁ := h₁) (hP := hP)
          (hU := hU) (A := A))).trans eInfl))

end Stages

end Langlands.Aubert.General
