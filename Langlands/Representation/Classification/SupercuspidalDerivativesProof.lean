import Langlands.Representation.Classification.SupercuspidalDerivativesStatement
import Langlands.Representation.Classification.SupercuspidalTopDerivative
import Langlands.Representation.Whittaker.MultiplicityOneProof
import Langlands.LocalField.Normalization.Proof

/-!
# Derivatives of irreducible supercuspidal representations (BZ77 §4.4)

Every derivative of order strictly between `0` and `n + 1` of an irreducible
supercuspidal representation of `GL_(n+1)` vanishes, and the top derivative is
one-dimensional.
-/

noncomputable section

open CategoryTheory

namespace Langlands.Classification.SupercuspidalDerivativesProof

open GeneralLinear GeneralLinear.Mirabolic Derivative Derivative.Mirabolic HarmonicAnalysis
  SupercuspidalDerivativeVanishing SupercuspidalTopDerivative

universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}

/-- A vector space with a nonzero functional of which every functional is a multiple is
one-dimensional. -/
theorem finrank_eq_one_of_dual {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (f₀ : Module.Dual K V) (hf₀ : f₀ ≠ 0) (h : ∀ f : Module.Dual K V, ∃ c : K, f = c • f₀) :
    Module.finrank K V = 1 := by
  have hinj : Function.Injective f₀ := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro x hx
    rw [LinearMap.mem_ker] at hx
    apply (Module.forall_dual_apply_eq_zero_iff K x).mp
    intro f
    obtain ⟨c, rfl⟩ := h f
    rw [LinearMap.smul_apply, hx, smul_zero]
  have hsurj : Function.Surjective f₀ := LinearMap.surjective_of_ne_zero hf₀
  rw [(LinearEquiv.ofBijective f₀ ⟨hinj, hsurj⟩).finrank_eq, Module.finrank_self]

/-- Whittaker multiplicity one for `A` makes a nonzero top derivative one-dimensional. -/
theorem finrank_top_of_multiplicityOne (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (n : ℕ) :
    letI := T.topology
    ∀ A : SmoothRep.{0, uF, uV} ℂ (GeneralLinear (0 + n + 1) F.Carrier),
      (∀ ℓ₁ ℓ₂ : Whittaker.glFunctionals ψ (0 + n) A.representation, ℓ₁.val ≠ 0 →
        ∃! c : ℂ, ℓ₂ = c • ℓ₁) →
      Nontrivial ((generalLinearDerivativePositive T ψ 0 n).obj A) →
        Module.finrank ℂ ((generalLinearDerivativePositive T ψ 0 n).obj A) = 1 := by
  let _ := T.topology
  intro A hM hD
  obtain ⟨x, hx⟩ := exists_ne (0 : (generalLinearDerivativePositive T ψ 0 n).obj A)
  obtain ⟨f₀, hf₀⟩ := not_forall.mp (mt (Module.forall_dual_apply_eq_zero_iff ℂ x).mp hx)
  have hsurj := topQuotient_surjective T ψ n A
  refine finrank_eq_one_of_dual f₀ (fun h => hf₀ (by rw [h]; rfl)) fun f => ?_
  let ℓ₀ : Whittaker.glFunctionals ψ (0 + n) A.representation :=
    ⟨f₀ ∘ₗ topQuotient T ψ n A, comp_topQuotient_mem_glFunctionals T ψ n A f₀⟩
  let ℓ : Whittaker.glFunctionals ψ (0 + n) A.representation :=
    ⟨f ∘ₗ topQuotient T ψ n A, comp_topQuotient_mem_glFunctionals T ψ n A f⟩
  have hℓ₀ : ℓ₀.val ≠ 0 := by
    intro h0
    obtain ⟨y, rfl⟩ := hsurj x
    exact hf₀ (LinearMap.congr_fun h0 y)
  obtain ⟨c, hc, -⟩ := hM ℓ₀ ℓ hℓ₀
  refine ⟨c, LinearMap.ext fun z => ?_⟩
  obtain ⟨y, rfl⟩ := hsurj z
  exact LinearMap.congr_fun (congrArg Subtype.val hc) y

/-- The published Whittaker multiplicity one, stated for the canonical normed topology,
holds for `T.topology`. -/
theorem multiplicityOne_of_topologicalData (T : F.TopologicalData) :
    letI := T.topology
    ∀ (n : ℕ) (V : Type uV) [AddCommGroup V] [Module ℂ V]
      (ψ : UnitaryAdditiveCharacter F.Carrier)
      (π : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) V),
      IsAdmissible π → Representation.IsIrreducible π →
      ∀ ℓ₁ ℓ₂ : Whittaker.glFunctionals ψ n π, ℓ₁.val ≠ 0 →
        ∃! c : ℂ, ℓ₂ = c • ℓ₁ := by
  have h := T.topology_eq_canonicalNormTopology
  have hM' := Whittaker.multiplicityOne.{uF, uV} p inferInstance F
  rw [h]
  exact hM'

/-- The top derivative `GL_(0+n+1) → GL_0` of an irreducible supercuspidal representation
is one-dimensional. -/
theorem finrank_generalLinearDerivativePositive_top (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (n : ℕ) :
    letI := T.topology
    ∀ A : SmoothRep.{0, uF, uV} ℂ (GeneralLinear (0 + n + 1) F.Carrier),
      A.IsIrreducible → IsSupercuspidal A.representation →
        Module.finrank ℂ ((generalLinearDerivativePositive T ψ 0 n).obj A) = 1 := by
  let _ := T.topology
  intro A hirr hsc
  exact finrank_top_of_multiplicityOne T ψ n A
    (multiplicityOne_of_topologicalData T (0 + n) A ψ A.representation hsc.1 hirr)
    (nontrivial_generalLinearDerivativePositive_top T ψ n A hsc
      (nontrivial_of_isIrreducible A.representation hirr))

/-- BZ77 §4.4, top derivative: the derivative of order `n + 1` of an irreducible
supercuspidal representation of `GL_(n+1)` is one-dimensional. -/
theorem finrank_generalLinearDerivative_top (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (n : ℕ) :
    letI := T.topology
    ∀ A : SmoothRep.{0, uF, uV} ℂ (GeneralLinear (n + 1) F.Carrier),
      A.IsIrreducible → IsSupercuspidal A.representation →
        Module.finrank ℂ ((generalLinearDerivative T ψ (n + 1) (n + 1) le_rfl).obj A) = 1 := by
  let _ := T.topology
  intro A hirr hsc
  have key : ∀ (m : ℕ) (hm : m = 0) (h : n + 1 = m + n + 1),
      Module.finrank ℂ ((generalLinearDerivativePositive T ψ m n).obj
        ((generalLinearRankCast T h).obj A)) = 1 := by
    intro m hm h
    subst hm
    exact finrank_generalLinearDerivativePositive_top T ψ n _
      (isIrreducible_rankCast T h A hirr) (isSupercuspidal_rankCast T h A hsc)
  exact key (n + 1 - (n + 1)) (Nat.sub_self _) (rank_eq_of_succ_le le_rfl)

end Langlands.Classification.SupercuspidalDerivativesProof

namespace Langlands.Classification

universe uF uW

variable {p : ℕ} [Fact p.Prime]

/-- BZ77 §4.4: an irreducible supercuspidal representation of `GL_(n+1)` has vanishing
derivatives of every order strictly between `0` and `n + 1`, and a one-dimensional top
derivative. -/
theorem supercuspidalDerivatives (F : PadicField.{uF} p) (T : F.TopologicalData) :
    SupercuspidalDerivatives.{uF, uW} F T := by
  let _ := T.topology
  intro ψ n A hirr hsc
  refine ⟨fun k hk hpos hlt => ?_, ?_⟩
  · exact SupercuspidalDerivativeVanishing.subsingleton_generalLinearDerivative T ψ (n + 1) k hk
      hpos hlt A hsc
  · exact SupercuspidalDerivativesProof.finrank_generalLinearDerivative_top T ψ n A hirr hsc

end Langlands.Classification
