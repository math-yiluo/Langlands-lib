# Renard IV.1.4: coefficients, smooth endomorphisms and the formal degree

Author: Worker 140. The theorem `Langlands.Renard.CompactRepresentation.compactFormalDegree` has exactly the type `Langlands.Renard.CompactRepresentation.CompactFormalDegreeStatements.{u, v}`, retaining its independent universe parameters. The published statement pair and its import closure are unchanged.

The source is David Renard, *Représentations des groupes réductifs p-adiques*, French version dated 9 July 2026, IV.1.4, printed pp.90–92 / PDF pp.96–98: equations (IV.1.4.1)–(IV.1.4.3), the Proposition, the definition of the formal degree and Remark 2. Source ID: `renard-2026-representations-groupes-reductifs-padiques`, SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.

The Lean proof assembles three component theorems. Their paired Markdown files describe the implemented arguments in full:

- `SmoothEndomorphismTensorProof`: basis coordinates prove injectivity of the rank-one tensor map. An endomorphism fixed on both sides by an open subgroup has finite-dimensional fixed-vector image by admissibility. Its coordinate functionals are smooth by right invariance, giving the required tensor and the exact range equality.
- `FormalDegreeOrthogonality`: the existing integral intertwiner vanishes between inequivalent irreducibles. Admissible Schur applied first to the representation and then to its smooth contragredient gives one scalar `κ` for all inverse coefficients, with `τ(ˇφ_{a,ℓ}) x = (κ ℓ(x)) a`. A positive square integral of a nonzero compact coefficient proves `κ ≠ 0`. Inverse coefficients themselves are test functions by local constancy and compact support.
- `CompactGroupFormalDegreeProof`: an irreducible smooth representation of a compact group has a finite spanning orbit, so is finite-dimensional. The trace of the coefficient integral intertwiner is `ℓ(x)` for Haar mass one; Schur and the trace of a scalar identity determine its scalar as `dim(τ)⁻¹ ℓ(x)`.

These are unconditional proofs of the three published components. The conjunction is assembled in the order in which `CompactFormalDegreeStatements` defines them. No additional premise is introduced, and all actions are the existing measure-indexed Hecke actions. Integrals with values in algebraic representation spaces are the published algebraic integrals; no topology on those carriers is assumed.

The proof routes differ from Renard's: coordinates replace his dimension count, two applications of admissible Schur replace Schur on the product representation, and positivity replaces the completeness lemma. The final compact formula is proved by an explicit finite-basis trace calculation.
