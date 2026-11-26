import Langlands.Global.Arithmetic.HarrisProposition48ExactStabilizerPrimeBranchReductionProof

/-!
# Proof of the totally complex reduction of the exact-stabilizer prime branch

Proves `Proposition48ExactStabilizerPrimeBranchReductionTCStatement` by the same
prime-orbit argument of Harris (1998), Proposition 4.8 (printed p.203), as
`proposition48ExactStabilizerPrimeBranchReduction`: the common argument
`proposition48ExactStabilizerPrimeBranch_of_inputs` takes the totally complex
forms of B2 and B4 directly, and the totally complex form of the self-duality
input, applied to `CuspidalSpectralRigidityTCStatement`.
-/

noncomputable section

universe uF uV

set_option autoImplicit false

namespace Langlands.Global.Harris

/-- The exact target `Proposition48ExactStabilizerPrimeBranchReductionTCStatement`:
the same interfaces, with the totally complex form of the self-duality input,
imply the totally complex exact-stabilizer prime branch. Theorem 1.2, totally
complex isobaric invariance and totally complex B3 are not used. -/
theorem proposition48ExactStabilizerPrimeBranchReductionTC :
    Proposition48ExactStabilizerPrimeBranchReductionTCStatement.{uF, uV} := by
  intro h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 _ hRig _ hB2 _ hB4 hB7 hBridge
  exact proposition48ExactStabilizerPrimeBranch_of_inputs h1 h2 h3 h4 h5 h6 h8 h9 h10 h11 h12
    (h7 hRig) hB2 hB4 hB7 hBridge

end Langlands.Global.Harris
