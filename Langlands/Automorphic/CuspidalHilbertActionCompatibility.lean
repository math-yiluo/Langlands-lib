import Langlands.Automorphic.CuspidalAdelicHilbertAction

/-! # Compatibility of the actual full Hilbert action with the original bounded actions -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 20000
set_option Elab.async false

namespace Langlands.UnitaryEmbeddingFamily
universe uG uD uV uE uH
variable {G : Type uG} [Group G] {D : Type uD} {V : Type uV}
  {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- Agreement of a bounded group action with prescribed isometries. -/
def AgreesWithIsometries (U : G →* (E →L[ℂ] E)) (φ : D → G)
    (B : D → E →ₗᵢ[ℂ] E) : Prop := ∀ d x, U (φ d) x = B d x

/-- Actual values on a dense carrier identify a restricted reconstructed action
with the independently supplied completed operators. -/
theorem agreesWithIsometries_of_values
    (j : V → E) (hj : DenseRange j) (J : G → E →ₗᵢ[ℂ] H)
    (U : G →* (E →L[ℂ] E)) (hU : RealizesEmbeddings J U)
    (φ : D → G) (B : D → E →ₗᵢ[ℂ] E) (ρ : D → V → V)
    (k : G → V → H) (hvalue : ∀ a v, J a (j v) = k a v)
    (hk : ∀ d v, k (φ d) v = k 1 (ρ d v))
    (hB : ∀ d v, B d (j v) = j (ρ d v)) :
    AgreesWithIsometries U φ B := by
  intro d x
  refine hj.induction_on x (isClosed_eq (U (φ d)).continuous (B d).continuous) ?_
  intro v
  apply (J 1).injective
  exact (hU.1 (φ d) (j v)).trans ((hvalue (φ d) v).trans
    ((hk d v).trans ((hvalue 1 (ρ d v)).symm.trans
      (congrArg (J 1) (hB d v)).symm)))

end Langlands.UnitaryEmbeddingFamily

namespace Langlands.Automorphic.OperatorUnitaryFormCore
universe uG0 uK0 uA0 uV0 uH0 uX0
variable {G0 : Type uG0} [Group G0] {K0 : Type uK0} [Group K0]
  {A : Type uA0} [Group A] {V : Type uV0} [AddCommGroup V] [Module ℂ V]
  {H : Type uH0} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {X : Type uX0} {ρ : Representation ℂ G0 V} {κ : Representation ℂ K0 V}
  {D : X → Module.End ℂ V}

/-- The full bounded action restricts to both supplied completed actions on the
same original form completion. -/
def BoundedActionCompatibility (b : OperatorUnitaryFormCore ρ κ D)
    (U : A →* (b.finiteForm.HilbertCompletion →L[ℂ] b.finiteForm.HilbertCompletion))
    (φG : G0 → A) (φK : K0 → A) : Prop :=
  Langlands.UnitaryEmbeddingFamily.AgreesWithIsometries U φG
    (fun d => (b.completedFiniteOperator d).toLinearIsometry) ∧
  Langlands.UnitaryEmbeddingFamily.AgreesWithIsometries U φK
    (fun k => (b.completedCompactOperator k).toLinearIsometry)

/-- Generic form-level packaging of both actual completed-action comparisons. -/
theorem boundedActionCompatibility_of_values (b : OperatorUnitaryFormCore ρ κ D)
    (J : A → b.finiteForm.HilbertCompletion →ₗᵢ[ℂ] H)
    (U : A →* (b.finiteForm.HilbertCompletion →L[ℂ] b.finiteForm.HilbertCompletion))
    (hU : Langlands.UnitaryEmbeddingFamily.RealizesEmbeddings J U)
    (φG : G0 → A) (φK : K0 → A) (k : A → V → H)
    (hvalue : ∀ a v, J a (b.finiteForm.toHilbert v) = k a v)
    (hkG : ∀ d v, k (φG d) v = k 1 (ρ d v))
    (hkK : ∀ c v, k (φK c) v = k 1 (κ c v)) :
    BoundedActionCompatibility b U φG φK :=
  ⟨Langlands.UnitaryEmbeddingFamily.agreesWithIsometries_of_values
    b.finiteForm.toHilbert b.finiteForm.denseRange_toHilbert J U hU φG
    (fun d => (b.completedFiniteOperator d).toLinearIsometry)
    (fun d v => ρ d v) k hvalue hkG b.completedFiniteOperator_toHilbert,
   Langlands.UnitaryEmbeddingFamily.agreesWithIsometries_of_values
    b.finiteForm.toHilbert b.finiteForm.denseRange_toHilbert J U hU φK
    (fun c => (b.completedCompactOperator c).toLinearIsometry)
    (fun c v => κ c v) k hvalue hkK b.completedCompactOperator_toHilbert⟩

end Langlands.Automorphic.OperatorUnitaryFormCore

namespace Langlands.Automorphic
open Langlands.Global MeasureTheory
open scoped NumberField
universe u
variable {F : Type u} [Field F] [NumberField F] {n : ℕ}

local instance actionCompatibilityRationalGroup : AddCommGroup (RationalInvariantFunctions F n) :=
  Submodule.addCommGroup _
local instance actionCompatibilityContinuousGroup : AddCommGroup (ContinuousRationalFunctions F n) :=
  Submodule.addCommGroup _
local instance actionCompatibilitySmoothGroup : AddCommGroup (FiniteSmoothRationalFunctions F n) :=
  Submodule.addCommGroup _
local instance actionCompatibilityFormsGroup : AddCommGroup (AutomorphicForms F n) :=
  Submodule.addCommGroup _
local instance actionCompatibilityStableGroup : AddCommGroup (StableAutomorphicFunctions F n) :=
  Submodule.addCommGroup _
local instance actionCompatibilitySpaceGroup (S : OperatorRealization F n) : AddCommGroup S.Space :=
  Submodule.addCommGroup _



namespace OperatorDeterminantSlice
variable [CompactSpace (AdeleQuotient F)] (S : OperatorRealization F n)

/-- The actual finite translated band function is the band function of the
original finite action. -/
theorem translatedToL2_finite_action (hS : S.IsCuspidal)
    (d : FiniteAdelicGL F n) (f : S.Space) :
    translatedToL2 S hS (AdelicGL.ofFinite F n d) f =
      translatedToL2 S hS 1 (S.finiteRepresentation d f) := by
  apply Lp.ext
  filter_upwards [(memLp_translate_of_cuspidal S hS (AdelicGL.ofFinite F n d) f).coeFn_toLp,
    (memLp_translate_of_cuspidal S hS 1 (S.finiteRepresentation d f)).coeFn_toLp]
      with q hf hg
  have h1 : toQuotient F n S (S.finiteRepresentation d f) (translate F n 1 q) =
      toQuotient F n S (S.finiteRepresentation d f) q := by simp only [translate_one]
  exact hf.trans ((toQuotient_finite F n S d f q).symm.trans (h1.symm.trans hg.symm))

/-- The actual compact translated band function is the band function of the
original compact action. -/
theorem translatedToL2_compact_action (hS : S.IsCuspidal)
    (k : standardInfiniteCompact F n) (f : S.Space) :
    translatedToL2 S hS (AdelicGL.ofInfinite F n k.val) f =
      translatedToL2 S hS 1 (S.compactRepresentation k f) := by
  apply Lp.ext
  filter_upwards [(memLp_translate_of_cuspidal S hS (AdelicGL.ofInfinite F n k.val) f).coeFn_toLp,
    (memLp_translate_of_cuspidal S hS 1 (S.compactRepresentation k f)).coeFn_toLp]
      with q hf hg
  have h1 : toQuotient F n S (S.compactRepresentation k f) (translate F n 1 q) =
      toQuotient F n S (S.compactRepresentation k f) q := by simp only [translate_one]
  exact hf.trans ((toQuotient_compact F n S k f q).symm.trans (h1.symm.trans hg.symm))


variable {r : ℕ} (T : CuspidalOperatorRealization F r)
  (hcoeff : CuspidalHilbertOrbitCoefficientStatement.{u})
  (χ : NumberField.IdeleClassGroup (𝓞 F) F →ₜ* ℂˣ)
  (hχ : ∀ z, ‖(χ z : ℂ)‖ = 1) (hTχ : T.realization.HasCentralCharacter χ)
  (b : T.realization.UnitaryForm)
  (hb : ∀ f g : T.Space, b.inner f g =
    ∫ q, Inner.inner ℂ (toQuotient F (r + 1) T.realization f q)
      (toQuotient F (r + 1) T.realization g q)
      ∂(quotientHaarMeasure F (r + 1)).restrict (band F (r + 1)))

/-- Both original bounded completed actions agree with the corresponding
restrictions of the constructed full adelic action. -/
theorem adelicHilbertRepresentation_boundedCompatibility :
    b.BoundedActionCompatibility (adelicHilbertRepresentation T hcoeff χ hχ hTχ b hb)
      (AdelicGL.ofFinite F (r + 1))
      (fun k : standardInfiniteCompact F (r + 1) => AdelicGL.ofInfinite F (r + 1) k.val) :=
  b.boundedActionCompatibility_of_values
    (translatedHilbertEmbedding T.realization T.cuspidal (Nat.succ_ne_zero r) χ hχ hTχ b hb)
    (adelicHilbertRepresentation T hcoeff χ hχ hTχ b hb)
    (adelicHilbertRepresentation_realizes T hcoeff χ hχ hTχ b hb)
    (AdelicGL.ofFinite F (r + 1))
    (fun k : standardInfiniteCompact F (r + 1) => AdelicGL.ofInfinite F (r + 1) k.val)
    (fun a f => translatedToL2 T.realization T.cuspidal a f)
    (translatedHilbertEmbedding_toHilbert T.realization T.cuspidal (Nat.succ_ne_zero r)
      χ hχ hTχ b hb)
    (translatedToL2_finite_action T.realization T.cuspidal)
    (translatedToL2_compact_action T.realization T.cuspidal)

end OperatorDeterminantSlice
/-- The constructed full adelic action retains both original bounded completed
actions, under its explicit scalar-coefficient premise. -/
def CuspidalHilbertActionCompatibilityStatement : Prop :=
  ∀ (hcoeff : CuspidalHilbertOrbitCoefficientStatement.{u})
    (F : Type u) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
    (r : ℕ) (T : CuspidalOperatorRealization F r)
    (χ : NumberField.IdeleClassGroup (𝓞 F) F →ₜ* ℂˣ)
    (hχ : ∀ z, ‖(χ z : ℂ)‖ = 1) (hTχ : T.realization.HasCentralCharacter χ)
    (b : T.realization.UnitaryForm)
    (hb : ∀ f g : T.Space, b.inner f g =
      ∫ q, Inner.inner ℂ (OperatorDeterminantSlice.toQuotient F (r + 1) T.realization f q)
        (OperatorDeterminantSlice.toQuotient F (r + 1) T.realization g q)
        ∂(OperatorDeterminantSlice.quotientHaarMeasure F (r + 1)).restrict
          (OperatorDeterminantSlice.band F (r + 1))),
    b.BoundedActionCompatibility
      (OperatorDeterminantSlice.adelicHilbertRepresentation T hcoeff χ hχ hTχ b hb)
      (AdelicGL.ofFinite F (r + 1))
      (fun k : standardInfiniteCompact F (r + 1) => AdelicGL.ofInfinite F (r + 1) k.val)

theorem cuspidalHilbertActionCompatibility : CuspidalHilbertActionCompatibilityStatement.{u} := by
  intro hcoeff F _ _ _ r T χ hχ hTχ b hb
  exact OperatorDeterminantSlice.adelicHilbertRepresentation_boundedCompatibility
    T hcoeff χ hχ hTχ b hb

end Langlands.Automorphic
