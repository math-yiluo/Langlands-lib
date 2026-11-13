import Langlands.Global.Factors.CuspidalPairFunctionalEquationReduction
import Langlands.Global.Factors.CuspidalPairFiniteLayer

/-! # The local data of cuspidal pairs -/

set_option autoImplicit false

universe u uQ

namespace Langlands.Global

open CuspidalPairFunctionalEquation

/-- The local data of cuspidal pairs exist: a finite factor choice, the archimedean
components of `ψ`, and one finite set `S` outside which every factor choice is
unramified. The contragredient hypotheses are not needed. -/
theorem cuspidalPairLocalData : CuspidalPairLocalDataStatement.{u, uQ} := by
  intro F _ _ _ ψ _ hdiag r t T Td T' Td' _ _ P P' Pd Pd' h h' hd hd'
  exact ⟨nonempty_finitePairFactorChoice ψ hdiag P P' Pd Pd' h h' hd hd',
    exists_isRealAdditiveComponent ψ hdiag, exists_isComplexAdditiveComponent ψ hdiag,
    exists_isUnramifiedOutside ψ hdiag P P' Pd Pd' h h' hd hd'⟩

end Langlands.Global
