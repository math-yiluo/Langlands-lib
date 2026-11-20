import Langlands.Automorphic.AssociatedFactorTCReductionStatement

/-! # The totally complex cuspidal-pair functional equation from its three parts

`cuspidalPairFunctionalEquationReductionTC` proves
`CuspidalPairFunctionalEquationReductionTCStatement`: the local data of cuspidal pairs, the
archimedean parameters of cuspidal realizations over totally complex fields and the completed
equation over totally complex fields imply the completed Rankin–Selberg functional equation of
cuspidal pairs over totally complex fields. The proof is the published proof of
`cuspidalPairFunctionalEquationReduction` with one more instance argument introduced; each
premise is applied only at the given totally complex field. See the paired Markdown.
-/

noncomputable section

universe u uQ

set_option autoImplicit false

namespace Langlands.Global

/-- **The totally complex reduction.** The local data of cuspidal pairs, the archimedean
parameters over totally complex fields and the completed equation over totally complex fields
imply the completed Rankin–Selberg functional equation of cuspidal pairs over totally complex
fields. -/
theorem cuspidalPairFunctionalEquationReductionTC :
    CuspidalPairFunctionalEquationReductionTCStatement.{u, uQ} := by
  intro hLD hC hE F _ _ _ _ ψ hψ hdiag r t T Td T' Td' hTd hTd' P P' Pd Pd' h h' hd hd'
  obtain ⟨hne, hRa, hCa, S, hP, hP', hPd, hPd', hsupp, hun⟩ :=
    hLD F ψ hψ hdiag r t T Td T' Td' hTd hTd' P P' Pd Pd' h h' hd hd'
  refine ⟨⟨hne, fun v => ⟨hRa v, (hC F r T).1 v, (hC F t T').1 v, (hC F r Td).1 v,
      (hC F t Td').1 v⟩, fun v => ⟨hCa v, (hC F r T).2 v, (hC F t T').2 v, (hC F r Td).2 v,
      (hC F t Td').2 v⟩⟩, S, hP, hP', hPd, hPd', hsupp, fun c => ⟨hun c, ?_⟩⟩
  intro aR haR aC haC dR dR' dRd dRd' hdR hdR' hdRd hdRd' dC dC' dCd dCd' hdC hdC' hdCd hdCd'
  exact hE F ψ hψ hdiag r t T Td T' Td' hTd hTd' P P' Pd Pd' h h' hd hd' S hP hP' hPd hPd'
    hsupp c (hun c) aR haR aC haC dR dR' dRd dRd' hdR hdR' hdRd hdRd' dC dC' dCd dCd' hdC hdC'
    hdCd hdCd'

end Langlands.Global
