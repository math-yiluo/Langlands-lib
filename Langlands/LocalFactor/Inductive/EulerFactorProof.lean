import Langlands.LocalFactor.Inductive.Statement
import Langlands.LocalFactor.Inductive.LocalInductionAux
import Langlands.Weil.Representation.CoinductionDegreeCyclic
import Langlands.LocalFactor.Euler.CyclicBlockProof

noncomputable section

namespace Langlands.LocalFactor.Inductive

universe u

open FiniteRepresentation Weil.Local
open FiniteRepresentation.InductionDegree

set_option maxHeartbeats 1200000 in
set_option backward.isDefEq.respectTransparency false in
/-- The Euler polynomial of actual local Weil induction is the residue-degree
expansion of the source Euler polynomial, with the corresponding spectral
evaluation identity for every complex argument. -/
theorem eulerFactorInduction :
    ∀ {p : ℕ} [Fact p.Prime], EulerFactorInductionStatement.{u} (p := p) := by
  intro p hp E E' g A _hA Φ Φ' hΦ hΦ'
  dsimp only
  let dG := (localDegree E).toMonoidHom
  let dH := (localDegree E').toMonoidHom
  let ι := (extensionWeilMap E E' g).toMonoidHom
  let e := InductionAlong.invariantCoinductionEquiv ι
    (extensionWeilMap_injective E E' g) (localInertia E) A
  let _ : FiniteDimensional ℂ (Source dH A.representation) := by
    change FiniteDimensional ℂ (invariants (localInertia E') A)
    infer_instance
  let F := (invariants (localInertia E)
    (induceAlong ι (extensionWeilMap_injective E E' g) A)).representation Φ
  let F' : Module.End ℂ (Source dH A.representation) :=
    (invariants (localInertia E') A).representation Φ'
  let C : Module.End ℂ (Target dG ι A.representation) :=
    ((Representation.coind ι A.representation).toInvariants dG.ker) Φ
  have hconj : e.conj F = C := by
    apply LinearMap.ext
    intro x
    change C (e (e.symm x)) = C x
    rw [e.apply_symm_apply]
  let n := extensionResidueDegree E E' g - 1
  have hn : extensionResidueDegree E E' g = n + 1 := by
    have hf := extensionResidueDegree_pos E E' g
    dsimp only [n]
    omega
  have hdeg : ∀ h : localWeilGroup E',
      intDegree dG (ι h) = ((n + 1 : ℕ) : ℤ) * intDegree dH h := by
    intro h
    simp only [dG, dH, ι, intDegree, ← hn]
    exact localDegreeInt_extensionWeilMap E E' g h
  let T := cyclicOperator dG dH ι A.representation n hdeg Φ hΦ Φ' hΦ'
  let ec := coordinates dG dH ι A.representation (n + 1) (Nat.succ_pos n)
    hdeg Φ hΦ Φ' hΦ'
  have htotal : (e.trans ec).conj F = T := by
    change ec.conj (e.conj F) = ec.conj C
    rw [hconj]
  have hcyclic := eulerCyclicBlock ℂ (Source dH A.representation) F' n T
    (cyclicOperator_zero dG dH ι A.representation n hdeg Φ hΦ Φ' hΦ')
    (cyclicOperator_succ dG dH ι A.representation n hdeg Φ hΦ Φ' hΦ')
  have hlocal : eulerPolynomial (R := ℂ) F =
      Polynomial.expand ℂ (extensionResidueDegree E E' g) (eulerPolynomial (R := ℂ) F') := by
    calc
      eulerPolynomial (R := ℂ) F = eulerPolynomial (R := ℂ) ((e.trans ec).conj F) :=
        (eulerPolynomial_conj (e.trans ec) F).symm
      _ = eulerPolynomial (R := ℂ) T := by rw [htotal]
      _ = _ := by
        simpa only [Polynomial.expand_eq_comp_X_pow, hn] using hcyclic.1
  refine ⟨hlocal, ?_⟩
  intro s
  change (eulerPolynomial (R := ℂ) F).eval _ = (eulerPolynomial (R := ℂ) F').eval _
  rw [hlocal]
  exact extensionExpandedPolynomial_eval E E' g (eulerPolynomial (R := ℂ) F') s

end Langlands.LocalFactor.Inductive
