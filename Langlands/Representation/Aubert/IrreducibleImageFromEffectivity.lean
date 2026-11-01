import Langlands.Representation.Aubert.ActualFixedFactorVector
import Langlands.Representation.Aubert.InvolutivityProof
import Langlands.Representation.Aubert.QuasicuspidalEigenvalue
import Langlands.Representation.Aubert.SignedEffectivityStatement
import Langlands.Representation.CuspidalSupport.QuasicuspidalEmbeddingProof

/-!
# Irreducible Aubert images assuming common-sign effectivity

The actual quasicuspidal embedding, induced eigenvalue and involutivity reduce
the irreducible-image assertion to the explicit signed-effectivity proposition.
This module does not prove that proposition.
-/

noncomputable section

namespace Langlands.Aubert

open GeneralLinear Parabolic SmoothRep

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

/-- The actual normalized induction packaged with its proved finite length. -/
def normalizedInducedFiniteLengthObject {n : ℕ} (B : BlockShape n) :
    letI := T.topology
    ∀ (σ : SmoothRep.{0, uF, max uF uV} ℂ (B.Levi F.Carrier)),
      σ.HasFiniteLength →
        FiniteLengthObject.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier) := by
  let := T.topology
  intro σ hσ
  exact ⟨(T.normalizedParabolicInductionFunctor.{uF, max uF uV} B).obj σ,
    normalizedInductionK0_hasFiniteLength.{uF, uV} F T B σ hσ⟩

/-- Published involutivity makes the actual Aubert endomorphism injective. -/
theorem alternatingOperator_injective (n : ℕ) :
    letI := T.topology
    Function.Injective (alternatingOperator.{uF, uV} F T n) := by
  let := T.topology
  have h : Function.Involutive (alternatingOperator.{uF, uV} F T n) := by
    intro x
    exact LinearMap.congr_fun (involutivity.{uF, uV} F T n) x
  exact h.injective

/-- Common-sign effectivity on constituents of quasicuspidal induction implies
the actual irreducible-image assertion in every rank. -/
theorem irreducibleImage_of_signedEffectivity
    (heff : SignedEffectivityStatement.{uF, uV} F T) :
    IrreducibleImageStatement.{uF, uV} F T := by
  let := T.topology
  intro n π hπ
  by_cases hn : n = 0
  · subst n
    exact irreducibleImage_rankZero F T π hπ
  obtain ⟨B, σ, hσ, hqc, j, hj⟩ :=
    CuspidalSupport.normalizedQuasicuspidalEmbedding.{uF, max uF uV}
      F T n (Nat.pos_of_ne_zero hn) π hπ
  let hσfl := hasFiniteLength_of_isIrreducible hσ
  let M := normalizedInducedFiniteLengthObject.{uF, uV} F T B σ hσfl
  let s : ℤ := (-1 : ℤ) ^ (n - B.length)
  have hs : s = 1 ∨ s = -1 := neg_one_pow_eq_or ℤ (n - B.length)
  have hsq : s * s = 1 := by
    rcases hs with hs | hs <;> simp [hs]
  have hfix :
      (s • alternatingOperator.{uF, uV} F T n)
          (SmoothRep.FiniteLengthGrothendieckGroup.ofRepresentation M.val M.property) =
        SmoothRep.FiniteLengthGrothendieckGroup.ofRepresentation M.val M.property := by
    change s • alternatingOperator.{uF, uV} F T n
        (GeneralLinear.finiteLengthClass n F.Carrier M.val M.property) =
      GeneralLinear.finiteLengthClass n F.Carrier M.val M.property
    have he := alternatingOperator_normalizedInductionK0_quasicuspidal.{uF, uV}
      F T B σ hσfl hqc
    rw [normalizedInductionK0_finiteLengthClass F T B σ hσfl M.property] at he
    change alternatingOperator.{uF, uV} F T n
        (GeneralLinear.finiteLengthClass n F.Carrier M.val M.property) =
      s • GeneralLinear.finiteLengthClass n F.Carrier M.val M.property at he
    rw [he, smul_smul, hsq, one_smul]
  apply IrreducibleOperator.exists_irreducible_image_of_embedding_in_effective_fixed_class
    (alternatingOperator.{uF, uV} F T n)
    (alternatingOperator_injective.{uF, uV} F T n) s hs M hfix
    (fun C hC hsub => heff n B σ hσ hqc C hC hsub) π hπ j hj

end Langlands.Aubert
