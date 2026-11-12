import Langlands.Representation.Families.InducedTwistQuotientExponentStatements
import Langlands.GroupScheme.Rational.SplitComponentProof
import Langlands.Representation.Plancherel.RationalUnramifiedCharacterDensity
import Langlands.Representation.LanglandsClassification.LeviInductionQuotient
import Langlands.Representation.CuspidalSupport.QuasicuspidalEmbeddingProof

/-! # Irreducible induced twists from exclusion and persistence of the inducing exponent

Exclusion and persistence of the `A_M`-exponent of `ρψ` in the normalized Jacquet modules
of quotients of `i_P^G(ρψ)` together give an unramified twist with irreducible induction.
-/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Renard.AlgebraicFamily

open Langlands.Aubert.General Langlands.Aubert.General.RepresentedParabolic GroupScheme

/-- Exclusion and persistence imply the existence of an irreducible induced unramified
twist: at a character in both generic loci, a proper nonzero invariant subspace would
give a quotient whose Jacquet module both has and lacks an exponent of `ρψ`. -/
theorem irreducibleInducedTwistExistence_of_quotientExponentStatements
    (h : InducedTwistQuotientExponentStatements.{u, v}) :
    IrreducibleInducedTwistExistenceStatement.{u, v} := by
  intro k _ _ _ _ _ G hG _ _ P M U p l r hp hl hr hmul ρ hρ hadm
  have := hG.isAffineHom
  let : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
  have := hl.isConnectedReductive.isAffineHom
  let : TopologicalSpace (rationalPoints M) := leviPointTopology l hl
  have : LocallyCompactSpace (rationalPoints M) := leviPoints_locallyCompactSpace p l hp hl
  have : NonarchimedeanGroup (rationalPoints M) := leviPoints_nonarchimedeanGroup p l hp hl
  obtain ⟨A, a, ha⟩ := (splitComponentStatement k M hl.isConnectedReductive).1
  obtain ⟨fC, hfC, hC⟩ := h.1 k G hG P M U p l r hp hl hr hmul A a ha ρ hρ hadm
  obtain ⟨fB, hfB, hB⟩ := h.2 k G hG P M U p l r hp hl hr hmul A a ha ρ hρ hadm
  obtain ⟨ψ, hψ⟩ := (Plancherel.dense_rationalUnramifiedPrincipalOpen M
    hl.isConnectedReductive (fC * fB) (mul_ne_zero hfC hfB)).nonempty
  rw [Plancherel.mem_rationalUnramifiedPrincipalOpen, MvPolynomial.eval_mul] at hψ
  have hψC : ψ ∈ Plancherel.rationalUnramifiedPrincipalOpen M hl.isConnectedReductive fC :=
    (Plancherel.mem_rationalUnramifiedPrincipalOpen _ _ _ _).mpr (left_ne_zero_of_mul hψ)
  have hψB : ψ ∈ Plancherel.rationalUnramifiedPrincipalOpen M hl.isConnectedReductive fB :=
    (Plancherel.mem_rationalUnramifiedPrincipalOpen _ _ _ _).mpr (right_ne_zero_of_mul hψ)
  refine ⟨ψ, ?_⟩
  have : Nontrivial (ρ.twist ψ.val.toMonoidHom
      (Plancherel.unramifiedCharacter_isOpen_ker _ ψ)) :=
    CuspidalSupport.QuasicuspidalEmbedding.nontrivial_of_isIrreducible _
      ((SmoothRep.isIrreducible_twist_iff _ _ ρ).mpr hρ)
  have : Nontrivial ((leviInductionFunctor p l r hp hr hl hmul).obj
      (ρ.twist ψ.val.toMonoidHom (Plancherel.unramifiedCharacter_isOpen_ker _ ψ))) :=
    nontrivial_leviInduction p l r hp hl hr hmul _
  have hbot : (⊥ : Subrepresentation ((leviInductionFunctor p l r hp hr hl hmul).obj
      (ρ.twist ψ.val.toMonoidHom
        (Plancherel.unramifiedCharacter_isOpen_ker _ ψ))).representation) ≠ ⊤ := by
    intro hbt
    obtain ⟨x, hx⟩ := exists_ne (0 : (leviInductionFunctor p l r hp hr hl hmul).obj
      (ρ.twist ψ.val.toMonoidHom (Plancherel.unramifiedCharacter_isOpen_ker _ ψ)))
    have hxbot := (congrArg (fun T => x ∈ T.toSubmodule) hbt).mpr Submodule.mem_top
    exact hx ((Submodule.mem_bot ℂ).mp hxbot)
  refine { toNontrivial := ⟨⟨⊥, ⊤, hbot⟩⟩, eq_bot_or_eq_top := fun S => ?_ }
  by_contra hS
  rw [not_or] at hS
  obtain ⟨χ, hχρ, hχS⟩ := hB ψ hψB S hS.2
  exact hC ψ hψC χ hχρ S hS.1 hχS

end Langlands.Renard.AlgebraicFamily
