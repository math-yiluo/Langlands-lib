# Functional-equation inputs for determinant twists of equal-rank pairs

`AutomorphicTwistSetup.HasEngineInputs` asks for the Rankin–Selberg functional equation for every determinant twist of the first member of a supplied cuspidal pair by a Hecke character trivial at infinity. For each such character there is a finite exceptional set \(S\). For every finite enlargement \(B\) of \(S\), the ordinary and dual partial L-functions are nonzero meromorphic functions. Their Euler products omit \(B\) and all infinite places and agree with the functions on a common right half-plane. The functional equation uses the corresponding gamma factors at \(B\) and at the infinite places, with the local data from the supplied setup.

`EqualRankTwistEngineInputsFromSemilocalStatement` derives these inputs from `EqualSemilocalEquationStatement` for each `AutomorphicTwistSetup ψ r r` over a number field \(F\) with compact additive adelic quotient. Both cuspidal realizations have rank \(r+1\). The character \(\psi\) is a nontrivial unitary additive character of the adèles and is trivial on the diagonal copy of \(F\). The number-field and presentation universes are independent.

`equalRankTwistEngineInputs_of_semilocalEquation` combines the equal-rank semi-local equation with the established global analytic, unfolding and Euler factorization results for equal-rank pairs. For each twist it chooses a finite set containing the exceptional places of the two presentations and their contragredients and the finite additive ramification. The given archimedean parameters still apply because the twisting character is trivial there. The equal-rank partial equation is formed with the integral gamma factors of the chosen local pair data. The finite-factor comparison then gives continuation of the completed functions. The Satake bounds give Euler convergence, and the engine adapter gives the functional equation for each enlargement of the chosen set.

`EqualRankTwistEngineInputsAt F` expresses the twist property at a specified field `F`. The
proof from `EqualPackageAt F` uses the same local factor choices and the same continuation
argument for any such field. `equalRankTwistEngineInputsAt_of_semilocalEquationTC` uses
`equalPackageTC` to construct that package from the totally complex equal-rank semi-local
equation when `F` is totally complex.

The equal-rank global integrals and their Euler factorization are those of Cogdell, *Analytic theory of L-functions for GL(n)* (2004), §2.3 and Theorem 2.2, pp. 209–211. The character on the additive adelic quotient is fixed in §1, pp. 198–199. The passage from global and local integral equations to the Rankin–Selberg equation follows the argument for Theorem 4.1, pp. 219–220, through its equal-rank formulation in the Library.
