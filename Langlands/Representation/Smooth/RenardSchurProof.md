# Renard III.1.7–III.1.11

Author: Worker 138. Namespace `Langlands.Renard.Smooth`.

`renardSchurStatements` has exactly the type `Langlands.Renard.Smooth.RenardSchurStatements.{u,v,w}`. It assembles the following five component proofs, retaining the three independent universe parameters and adding no hypothesis:

- `admissibleBidual` proves `AdmissibleBidualStatement`: compact-open fixed-space duality and strict algebraic dual-rank growth give the converse, while published admissible duality gives canonical bijectivity.
- `sigmaCompactSchur` proves `SigmaCompactSchurStatement`: a nonzero smooth orbit is countable under a compact covering, spans by irreducibility, and satisfies published countable-dimensional Schur. Every nonzero intertwiner between irreducibles is an equivalence.
- `invariantContragredientPairing` proves `InvariantContragredientPairingStatement`: the form maps into the smooth bidual; canonical admissible biduality and admissible Schur make it scalar. Smooth-dual separation and nonzero scalar multiplication give nondegeneracy.
- `centralCharacter` proves `CentralCharacterStatement`: the scalar central operators multiply as a unit-valued character, differing scalar characters exclude nonzero intertwiners, and the categorical-center component is already a scalar intertwining endomorphism.
- `heckeCompleteness` proves `HeckeCompletenessStatement`: positivity and a countable compact-open corner produce a simple nondegenerate full-Hecke quotient, the independently proved Hecke-module equivalence reconstructs the smooth representation, and a countable basis permits any target carrier universe.

The paired documentation of each component and each Hecke construction describes its implemented Lean proof. The final file is only the conjunction constructor applied to those proofs. In particular it introduces no new representation model, smoothness convention or assertion about the dimension of the full Hecke algebra.

Source: David Renard, *Représentations des groupes réductifs p-adiques*, French version dated 9 July 2026, III.1.7–III.1.11, printed pp.62–65 / PDF pp.68–71; registered as `renard-2026-representations-groupes-reductifs-padiques`, SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`. The unchanged published statement pair remains in `Langlands/Representation/Smooth/RenardSchurStatements` with all its imports unchanged.
