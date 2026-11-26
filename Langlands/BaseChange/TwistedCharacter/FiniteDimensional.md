# Finite-dimensional twisted character functions

`Langlands.BaseChange.finiteDimensionalTwistedCharacter` proves
`FiniteDimensionalTwistedCharacterStatement` for admissible complex
representations of locally profinite groups on finite-dimensional spaces.
For any linear endomorphism \(A\), the function
\(g\mapsto\operatorname{tr}(\rho(g)A)\) is locally constant on the group and
represents the twisted distribution for every Haar measure.

In the proof, smoothness makes each diagonal coefficient
\(g\mapsto b_i^*(\rho(g)A b_i)\) locally constant. Their finite sum is continuous
and locally integrable. The coefficient formula for the integrated action
identifies each diagonal entry of \(\rho(f)A\) with the integral of the
corresponding coefficient times \(f\). The integrands are continuous with
compact support, so the finite trace sum commutes with integration.

The formula is the finite-dimensional specialization of the trace definition
in Henniart–Lemaire, *Changement de base et induction automorphe pour
GL_n en caractéristique non nulle*, II.1.3, printed pp. 56–57.
Source ID `provided-a0a5445aba86b871bcd83f08813de3234fddb463ff9bb3c9dfd60d2d2fcdae61`,
SHA-256 `7af2940c75a75937c1bf9096eb329931d4245cf592e3572db0ff93ec6e76c5e0`.
