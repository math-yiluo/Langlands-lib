import Langlands.Automorphic.CuspidalWhittakerSmoothBound
import Langlands.Global.RankinSelberg.UnramifiedWhittakerFactorizationProof
import Langlands.Representation.Archimedean.SmoothDerivativeTopology
import Langlands.Representation.Smooth.Definitions
import Mathlib.Algebra.Module.Submodule.Equiv

/-! # Continuous extensions of actual finite-level Whittaker functionals -/

set_option autoImplicit false

noncomputable section

open scoped CategoryTheory.MonObj Manifold ContDiff

namespace Langlands.Automorphic

open Langlands.Global Langlands.Global.RankinSelbergGlobal
  ContinuousRationalFunctions MeasureTheory
open Langlands.Archimedean

universe u w u𝔤 uH uG uV

section ExtensionAlongEmbedding

variable {𝔤 : Type u𝔤} [NormedAddCommGroup 𝔤] [NormedSpace ℝ 𝔤]
  {H : Type uH} [TopologicalSpace H] (I : ModelWithCorners ℝ 𝔤 H)
  {G : Type uG} [Group G] [TopologicalSpace G] [ChartedSpace H G]
  {E : Type w} [NormedAddCommGroup E] [NormedSpace ℂ E]
  (π : G →* (E →L[ℂ] E)) [LieGroup I ∞ G]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- Hahn--Banach along an injective genuine smooth embedding preserves the
specified finite word bound. It gives existence only. -/
theorem exists_extension_along_smoothEmbedding
    (j : V →ₗ[ℂ] Langlands.Archimedean.smoothVectors I π) (hj : Function.Injective j)
    (ℓ : V →ₗ[ℂ] ℂ) (S : Finset (List 𝔤)) (C : ℝ) (hC : 0 ≤ C)
    (hℓ : ∀ v, ‖ℓ v‖ ≤ C * ∑ Xs ∈ S, ‖iteratedLieDerivative I π Xs (j v)‖) :
    ∃ L : Langlands.Archimedean.smoothVectors I π →ₗ[ℂ] ℂ,
      (∀ v, L (j v) = ℓ v) ∧
      (∀ v, ‖L v‖ ≤ C * ∑ Xs ∈ S, ‖iteratedLieDerivative I π Xs v‖) ∧
      IsContinuousOnSmoothVectors I π L := by
  let e := LinearEquiv.ofInjective j hj
  let ℓ' : j.range →ₗ[ℂ] ℂ := ℓ.comp e.symm.toLinearMap
  have hb : ∀ v : j.range, ‖ℓ' v‖ ≤
      C * ∑ Xs ∈ S, ‖iteratedLieDerivative I π Xs (v : Langlands.Archimedean.smoothVectors I π)‖ := by
    intro v
    have hv : j (e.symm v) = (v : Langlands.Archimedean.smoothVectors I π) :=
      LinearEquiv.ofInjective_symm_apply j v
    have h := hℓ (e.symm v)
    rw [hv] at h
    exact h
  obtain ⟨L, hL, hbL, hcL⟩ :=
    exists_extension_of_word_bound I π j.range ℓ' S C hC hb
  refine ⟨L, ?_, hbL, hcL⟩
  intro v
  have h := hL (e v)
  change L (j v) = ℓ (e.symm (e v)) at h
  simpa only [LinearEquiv.symm_apply_apply] using h

end ExtensionAlongEmbedding

local instance extensionRationalGroup (F : Type u) [Field F] [NumberField F] (n : ℕ) :
    AddCommGroup (RationalInvariantFunctions F n) := Submodule.addCommGroup _
local instance extensionContinuousGroup (F : Type u) [Field F] [NumberField F] (n : ℕ) :
    AddCommGroup (ContinuousRationalFunctions F n) := Submodule.addCommGroup _
local instance extensionFiniteSmoothGroup (F : Type u) [Field F] [NumberField F] (n : ℕ) :
    AddCommGroup (FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _
local instance extensionFormGroup (F : Type u) [Field F] [NumberField F] (n : ℕ) :
    AddCommGroup (AutomorphicForms F n) := Submodule.addCommGroup _
local instance extensionStableGroup (F : Type u) [Field F] [NumberField F] (n : ℕ) :
    AddCommGroup (StableAutomorphicFunctions F n) := Submodule.addCommGroup _
local instance extensionSpaceGroup {F : Type u} [Field F] [NumberField F] {n : ℕ}
    (S : OperatorRealization F n) : AddCommGroup S.Space := Submodule.addCommGroup _

variable (F : Type u) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
  {r : ℕ} (T : CuspidalOperatorRealization F r)
  (hL2 : ∀ x : T.Space,
    MemLp (OperatorDeterminantSlice.toQuotient F (r + 1) T.realization x) 2
      ((OperatorDeterminantSlice.quotientHaarMeasure F (r + 1)).restrict
        (OperatorDeterminantSlice.band F (r + 1))))
  (ψ : AddChar (Adeles F) ℂ)
  {𝔤 : Type u𝔤} [NormedAddCommGroup 𝔤] [NormedSpace ℝ 𝔤]
  {H : Type uH} [TopologicalSpace H] (I : ModelWithCorners ℝ 𝔤 H)
  {G : Type uG} [Group G] [TopologicalSpace G] [ChartedSpace H G]
  {E : Type w} [NormedAddCommGroup E] [NormedSpace ℂ E]
  (π : G →* (E →L[ℂ] E))
  (j : T.Space →ₗ[ℂ] Langlands.Archimedean.smoothVectors I π)
  (ζ : ArchimedeanGL.RealLieAlgebra F (r + 1) → 𝔤)

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1600000 in
/-- For a standard additive character, the actual band bound supplies continuous
extensions at each fixed finite level and adelic point, with one finite word bound
uniform on a compact point set. The injective smooth embedding, norm equality and
real-generator compatibility are hypotheses. Existence only is asserted. -/
def CuspidalWhittakerSmoothExtensionStatement [LieGroup I ∞ G] : Prop :=
  IsStandardAdditiveCharacter F ψ →
  ∀ (_hbound : CuspidalWhittakerBandBound F T hL2 ψ)
    (_hj : Function.Injective j)
    (_hnorm : ∀ v : T.Space,
      ‖OperatorDeterminantSlice.toL2 F (r + 1) T.realization
        (OperatorDeterminantSlice.quotientHaarMeasure F (r + 1)) hL2 v‖ = ‖(j v : E)‖)
    (_hgen : ∀ (X : ArchimedeanGL.RealLieAlgebra F (r + 1)) (v : T.Space),
      (j (T.realization.envelopingAction
        (ArchimedeanGL.envelopingGenerator F (r + 1)
          (ArchimedeanGL.complexify F (r + 1) X)) v) : E) =
        lieDerivative I π (ζ X) (j v))
    (J : Subgroup (FiniteAdelicGL F (r + 1)))
    (_hJo : IsOpen (J : Set (FiniteAdelicGL F (r + 1))))
    (_hJc : IsCompact (J : Set (FiniteAdelicGL F (r + 1))))
    (Q : Set (Points F (r + 1))) (_hQ : IsCompact Q),
    ∃ (S : Finset (List 𝔤)) (C : ℝ), 0 ≤ C ∧
      ∀ g ∈ Q, ∃ L : Langlands.Archimedean.smoothVectors I π →ₗ[ℂ] ℂ,
        (∀ v : T.Space,
          (∀ k : J, T.realization.finiteRepresentation
            (k : FiniteAdelicGL F (r + 1)) v = v) →
          L (j v) = cuspWhittaker F T ψ v g) ∧
        (∀ v, ‖L v‖ ≤ C * ∑ Xs ∈ S, ‖iteratedLieDerivative I π Xs v‖) ∧
        IsContinuousOnSmoothVectors I π L

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1600000 in
/-- Extend each actual fixed-level evaluation by its uniform genuine word bound. -/
theorem exists_cuspWhittaker_smoothExtensions_of_bandBound [LieGroup I ∞ G] :
    CuspidalWhittakerSmoothExtensionStatement F T hL2 ψ I π j ζ := by
  intro hψ hbound hj hnorm hgen J hJo hJc Q hQ
  classical
  let j₀ : T.Space →ₗ[ℂ] E := (Langlands.Archimedean.smoothVectors I π).subtype.comp j
  obtain ⟨S, C, hC, hb⟩ :=
    cuspWhittaker_smoothBound_of_bandBound F T hL2 ψ I π j₀ ζ
      hbound hnorm hgen J hJo hJc Q hQ
  refine ⟨S, C, hC, ?_⟩
  intro g hg
  let V := Langlands.fixedVectors T.realization.finiteRepresentation J
  let jV : V →ₗ[ℂ] Langlands.Archimedean.smoothVectors I π := j.comp V.subtype
  have hjV : Function.Injective jV := hj.comp Subtype.val_injective
  let ℓ : V →ₗ[ℂ] ℂ :=
    (UnramifiedWhittaker.whittakerFunctional F ψ hψ T g).comp V.subtype
  have hbℓ : ∀ v : V, ‖ℓ v‖ ≤
      C * ∑ Xs ∈ S, ‖iteratedLieDerivative I π Xs (jV v)‖ := by
    intro v
    have hv : ∀ k : J, T.realization.finiteRepresentation
        (k : FiniteAdelicGL F (r + 1)) (v : T.Space) = (v : T.Space) := by
      exact v.property
    exact hb (v : T.Space) hv g hg
  obtain ⟨L, hL, hbL, hcL⟩ :=
    exists_extension_along_smoothEmbedding I π jV hjV ℓ S C hC hbℓ
  refine ⟨L, ?_, hbL, hcL⟩
  intro v hv
  have hvV : v ∈ V := by
    exact hv
  exact hL ⟨v, hvV⟩

end Langlands.Automorphic
