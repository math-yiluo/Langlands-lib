import Langlands.Representation.Whittaker.IrreducibleCoinvariantFinitenessProof
import Langlands.AllField.Group.GL.UpperUnipotentCompactContainmentProof
import Langlands.AllField.Representation.CuspidalSupport.CuspidalEmbeddingProof
import Langlands.AllField.Representation.Whittaker.IrreducibleCoinvariantFinitenessStatement
import Langlands.AllField.Representation.Whittaker.LeviCuspidalCoinvariantFinitenessProof
import Langlands.AllField.Representation.Whittaker.ParabolicInducedCoinvariantFinitenessProof
/-!
# Assembly of irreducible coinvariant finiteness

Embed an irreducible smooth representation into normalized parabolic induction
from irreducible cuspidal Levi data. Published coefficient finiteness and
induction preservation make the latter's character quotient finite-dimensional;
exactness embeds the original quotient into it. Admissibility handles rank zero.
-/

noncomputable section

namespace Langlands.AllField.Whittaker
open Langlands.Whittaker hiding CompactLocalizationStatement IrreducibleCoinvariantFinitenessStatement LeviCuspidalCoinvariantFinitenessStatement ParabolicInducedCoinvariantFinitenessStatement SupercuspidalCoinvariantFinitenessStatement UnipotentOrbitStatement compactLocalization irreducibleCoinvariantFiniteness leviCuspidalCoinvariantFiniteness parabolicInducedCoinvariantFiniteness supercuspidalCoinvariantFiniteness unipotentOrbit
open Langlands.AllField.Whittaker

universe uF uV

open Langlands.GeneralLinear hiding UpperUnipotentCompactContainmentStatement upperUnipotentCompactContainment upperUnipotent_isLimitOfCompactSubgroups
open Langlands.AllField.GeneralLinear
open Langlands.Jacquet.Localization

private theorem finiteDimensional_rankZero
    (F : Type uF) [Field F]
    (T : LocalFieldData F) :
    letI := T.topology
    ∀ (V : Type uV) [AddCommGroup V] [Module ℂ V]
      (ρ : Representation ℂ (GeneralLinear 0 F) V),
      IsSmooth ρ → ρ.IsIrreducible → FiniteDimensional ℂ V := by
  let := T.topology
  let := T.generalLinearTopologicalGroup 0
  intro V _ _ ρ hρ hρirr
  have hadm : IsAdmissible ρ :=
    (Langlands.AllField.CuspidalSupport.cuspidalEmbedding F T 0 (SmoothRep.of ρ hρ) hρirr).1
  let K : OpenSubgroup (GeneralLinear 0 F) := ⊤
  have hfixed (v : V) : v ∈ fixedVectors ρ K.toSubgroup := by
    intro g
    change ρ (g : GeneralLinear 0 F) v = v
    rw [Subsingleton.elim (g : GeneralLinear 0 F) 1, map_one]
    rfl
  let : Module.Finite ℂ (fixedVectors ρ K.toSubgroup) := hadm.2 K
  exact FiniteDimensional.of_surjective
    (fixedVectors ρ K.toSubgroup).subtype (fun v => ⟨⟨v, hfixed v⟩, rfl⟩)

/-- The final embedding argument, given finiteness of cuspidal induction. -/
private theorem irreducibleCoinvariantFiniteness_of_cuspidal_induction
    (hind : ∀ (F : Type uF) [Field F]
      (T : LocalFieldData F),
      letI := T.topology
      ∀ (n : ℕ), 0 < n →
      letI := T.generalLinearTopologicalGroup n
      ∀ (B : BlockShape n)
        (σ : SmoothRep.{0,uF,uV} ℂ (B.Levi F)),
        σ.IsIrreducible → CuspidalSupport.IsLeviCuspidal B σ.representation →
        ∀ θ : upperUnipotent n F →* ℂˣ,
          IsLocallyConstant (fun u => (θ u : ℂ)) →
          FiniteDimensional ℂ
            (Coinvariants
              (Induction.smoothInduced (B.parabolic F)
                (twist (T.parabolicHalfModulus B)
                  (σ.representation.comp (B.leviProjection F))))
              (upperUnipotent n F) θ)) :
    IrreducibleCoinvariantFinitenessStatement.{uF,uV} := by
  intro F _ T
  let := T.topology
  intro n V _ _ ρ hρ hρirr θ hθ
  cases n with
  | zero =>
    let : FiniteDimensional ℂ V :=
      finiteDimensional_rankZero F T V ρ hρ hρirr
    infer_instance
  | succ n =>
    let := T.generalLinearTopologicalGroup (n + 1)
    obtain ⟨_, B, σ, hσ, hcuspidal, j, hj⟩ :=
      Langlands.AllField.CuspidalSupport.cuspidalEmbedding F T (n + 1) (SmoothRep.of ρ hρ) hρirr
    let π := Induction.smoothInduced (B.parabolic F)
      (twist (T.parabolicHalfModulus B)
        (σ.representation.comp (B.leviProjection F)))
    let : FiniteDimensional ℂ (Coinvariants π (upperUnipotent (n + 1) F) θ) :=
      hind F T (n + 1) (Nat.zero_lt_succ n) B σ hσ hcuspidal θ hθ
    have hinv : IsInvariant (upperUnipotent (n + 1) F)
        ⊥ bot_le θ := by
      intro m u
      apply congrArg θ
      apply Subtype.ext
      have hm : (m : GeneralLinear (n + 1) F) = 1 :=
        Subgroup.mem_bot.mp m.property
      simp [conjugate, hm]
    exact FiniteDimensional.of_injective
      (mapLinear (upperUnipotent (n + 1) F) θ j)
      (map_injective_of_smooth
        (upperUnipotent (n + 1) F)
        (upperUnipotent_isLimitOfCompactSubgroups F T (n + 1))
        θ hθ ⊥ bot_le hinv j hj (Induction.smoothInduced_smooth _ _))

/-- The finiteness assertion of Bernstein--Zelevinsky (1976), Theorem 5.21,
for every locally constant upper-unipotent character, including rank zero. -/
theorem irreducibleCoinvariantFiniteness :
    IrreducibleCoinvariantFinitenessStatement.{uF,uV} := by
  apply irreducibleCoinvariantFiniteness_of_cuspidal_induction
  intro F _ T
  let := T.topology
  intro n hn
  let := T.generalLinearTopologicalGroup n
  intro B σ hσ hcuspidal θ hθ
  exact parabolicInducedCoinvariantFiniteness.{uF,uV} F T n hn B σ
    (leviCuspidalCoinvariantFiniteness.{uF,uV} F T n hn B σ hσ hcuspidal) θ hθ

end Langlands.AllField.Whittaker
