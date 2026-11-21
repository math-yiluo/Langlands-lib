import Langlands.Automorphic.BlockTermCentralCharacter
import Langlands.Automorphic.CyclicOperatorAlgebra

/-! # The selected cuspidal block period with its actual cyclic quotient -/

noncomputable section
universe u
set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Automorphic

open Langlands.Global Langlands.GeneralLinear _root_.Representation
open scoped CategoryTheory.MonObj

private theorem exists_succBlockShape {n : ℕ} (shape : BlockShape n) :
    ∃ (k : ℕ) (m : Fin k → ℕ) (hm : ∑ i, (m i + 1) = n),
      shape = ⟨k, fun i => m i + 1, fun _ => Nat.succ_pos _, hm⟩ := by
  obtain ⟨k, d, hd, hs⟩ := shape
  let m : Fin k → ℕ := fun i => d i - 1
  have he : (fun i => m i + 1) = d :=
    funext fun i => Nat.sub_add_cancel (Nat.succ_le_iff.mpr (hd i))
  have hm : ∑ i, (m i + 1) = n := by
    rw [show (∑ i, (m i + 1)) = ∑ i, d i from congrArg (Finset.univ.sum) he]
    exact hs
  have hshape (e : Fin k → ℕ) (hde : d = e) (hepos : ∀ i, 0 < e i)
      (hesum : ∑ i, e i = n) :
      (⟨k, d, hd, hs⟩ : BlockShape n) = ⟨k, e, hepos, hesum⟩ := by
    subst e
    rfl
  exact ⟨k, m, hm, hshape _ he.symm _ hm⟩

private theorem cyclicGenerator_ne_zero_of_surjective {R V W : Type*} [Semiring R]
    [AddCommMonoid V] [Module R V] [AddCommMonoid W] [Module R W] [Nontrivial W]
    {v : V} (p : (R ∙ v) →ₗ[R] W) (hp : Function.Surjective p) : v ≠ 0 := by
  intro hv
  obtain ⟨w, hw⟩ := exists_ne (0 : W)
  obtain ⟨x, rfl⟩ := hp w
  have hx : x = 0 := by
    apply Subtype.ext
    change x.val = 0
    obtain ⟨a, ha⟩ := (Submodule.mem_span_singleton (M := V)).mp x.property
    exact ha.symm.trans (by rw [hv, smul_zero])
  exact hw ((congrArg p hx).trans p.map_zero)

variable (F : Type u) [Field F] [NumberField F]

attribute [local instance] subquotientRationalGroup subquotientContinuousGroup
  subquotientSmoothGroup subquotientFormGroup subquotientStableGroup subquotientRealizationGroup

local instance selectedPeriodOperatorRing (n : ℕ) : Ring (automorphicOperatorAlgebra F n) :=
  Subalgebra.toRing _

private theorem finiteSmooth_refinement_eq_zero {n : ℕ} (B : BlockShape n)
    (S : OperatorRealization F n)
    (h : ∀ T : BlockShape n, B.cuts ⊂ T.cuts →
      ∀ w : S.representation.asModule, realizedBlockConstantTerm F T S w = 0)
    (w : S.Space) (t : Finset (Fin (n - 1))) (ht : B.cuts ⊂ t) :
    finiteSmoothBlockConstantTerm F (standardBlockWeight (n := n) t) (S.ambient w) = 0 := by
  let T := (BlockShape.cutEquiv n).symm t
  have hT : T.cuts = t := BlockShape.cuts_cutEquiv_symm (n := n) t
  have hz := h T (hT.symm ▸ ht) w
  let e := GeneralLinearGroupPoints.adelicEquiv F n
  funext g
  have hv := congrFun hz (e g)
  change finiteSmoothBlockConstantTerm F (standardBlockWeight T.cuts)
    (S.ambient w) (e.symm (e g)) = 0 at hv
  rwa [e.symm_apply_apply, hT] at hv

/-- The selected actual block period with continuous central character,
a cyclic quotient onto the original representation, and zero strict refinements. -/
def HasCuspidalSupportSelectedPeriod {r : ℕ} (Q : IrreducibleOperatorSubquotient F r) : Prop :=
  ∃ (k : ℕ) (m : Fin k → ℕ) (hm : ∑ i, (m i + 1) = r + 1)
      (S : OperatorRealization F (r + 1)),
    let B : BlockShape (r + 1) := ⟨k, fun i => m i + 1, fun _ => Nat.succ_pos _, hm⟩
    let A := translatedBlockTermOperatorAction F B S
    ∃ (v : Representation.asModule (AlgHom.toMonoidHom' A)) (χ : (Fin k → Ideles F) →ₜ* ℂˣ)
      (q : IntertwiningMap (AlgHom.toMonoidHom' (cyclicAlgebraAction A v)) Q.representation),
      Function.Surjective q ∧
      (∀ z : Fin k → Ideles F, translatedFunctionAction (blockConstantTermScalarAction F B)
        (realizedBlockConstantTerm F B S) z v = (χ z : ℂ) • v) ∧
      (∀ a : Fin k → Fˣ, χ (fun i => diagonalUnits F (a i)) = 1) ∧
      ∀ (w : S.Space) (t : Finset (Fin r)), B.cuts ⊂ t →
        finiteSmoothBlockConstantTerm F (standardBlockWeight (n := r + 1) t) (S.ambient w) = 0

/-- Minimal constant-term selection followed by the central character argument
keeps the original irreducible quotient on one actual cyclic translated period. -/
theorem exists_cuspidalSupportSelectedPeriod {r : ℕ} (Q : IrreducibleOperatorSubquotient F r) :
    HasCuspidalSupportSelectedPeriod F Q := by
  obtain ⟨B, S, p, hp, hker, href⟩ := exists_cuspidalBlockTermSource F Q
  obtain ⟨k, m, hm, rfl⟩ := exists_succBlockShape B
  let B : BlockShape (r + 1) := ⟨k, fun i => m i + 1, fun _ => Nat.succ_pos _, hm⟩
  let A := translatedBlockTermOperatorAction F B S
  obtain ⟨v, χ, p', hp', hχ⟩ :=
    exists_translatedBlockTerm_centralCyclicQuotient F B S p hp hker
  let : Nontrivial Q.representation.asModule :=
    IsSimpleModule.nontrivial (MonoidAlgebra ℂ (automorphicOperatorAlgebra F (r + 1))) _
  have hv : v ≠ 0 := cyclicGenerator_ne_zero_of_surjective p' hp'
  obtain ⟨hcont, hprincipal⟩ :=
    continuous_character_of_translatedBlockTerm_eigenvector F B S v hv χ hχ
  let χ₀ : (Fin k → Ideles F) →ₜ* ℂˣ := ⟨χ, hcont⟩
  let q := cyclicAlgebraIntertwiner A Q.representation v p'
  have hq := cyclicAlgebraIntertwiner_surjective A Q.representation v p' hp'
  exact ⟨k, m, hm, S, v, χ₀, q, hq, hχ, hprincipal,
    finiteSmooth_refinement_eq_zero F B S href⟩

end Langlands.Automorphic
