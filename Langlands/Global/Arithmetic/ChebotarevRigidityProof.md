# Proof of finite Galois Chebotarev realization and character rigidity

This file proves the Library statement
`Langlands.Global.ChebotarevRigidityStatement.{u, v, w, z}` of
`Langlands/Global/Arithmetic/ChebotarevStatement.lean`, exactly as
published, at arbitrary universes. It introduces no statement, no
definition and no hypothesis.

## Declaration

- `Langlands.Global.chebotarevRigidityStatement :
  ChebotarevRigidityStatement.{u, v, w, z}` is the target theorem.

## The implemented proof

The target is by definition the conjunction
`ChebotarevPrimeRealizationStatement.{u, v} ∧
FiniteGaloisFrobeniusRigidityStatement.{u, v, w, z}`. The proof is the
anonymous pair of the Library's two published proofs of the conjuncts:

`⟨chebotarevPrimeRealizationStatement, finiteGaloisFrobeniusRigidityStatement⟩`.

1. `Langlands.Global.chebotarevPrimeRealizationStatement :
   ChebotarevPrimeRealizationStatement.{u, v}`, in module
   `Langlands.Global.Arithmetic.ChebotarevPrimeRealizationProof`.
   It is Chebotarev's theorem in existence form, proved through the port of
   the Chebotarev closure of the Anthropic FLT repository under
   `Langlands/AnthropicFLT/`. Its proof is described in
   `Langlands/Global/Arithmetic/ChebotarevPrimeRealizationProof.md`.
2. `Langlands.Global.finiteGaloisFrobeniusRigidityStatement :
   FiniteGaloisFrobeniusRigidityStatement.{u, v, w, z}`, in module
   `Langlands.Global.Arithmetic.FiniteGaloisFrobeniusRigidityProof`.
   It combines prime realization with the finite complex
   character theorem. Its proof is described in
   `Langlands/Global/Arithmetic/FiniteGaloisFrobeniusRigidityProof.md`.

The universe parameters line up directly: the first conjunct is used at
`u, v` and the second at `u, v, w, z`, as in the target. All the
mathematical content is in these two inputs. This file only pairs them, so
both conjuncts enter as proved theorems and neither is a premise.

## Sources

The target's Markdown (`ChebotarevStatement.md`) records the provenance of
both conjuncts. They are also in the plan note
`operator-external-inputs-plan-2026-11-16`, Section 2.6 (interface F) and
Section 4.4. The literature enters only through the two inputs:

- Chebotarev's theorem, existence form: J. Neukirch, *Algebraic Number
  Theory* (1999), Chapter VII, Theorem 13.4, printed pp. 545–546 (source
  `neukirch-1999-algebraic-number-theory`), through
  `chebotarevPrimeRealizationStatement`.
- Equality of complex characters determines a representation up to
  isomorphism: J.-P. Serre, *Linear Representations of Finite Groups*
  (1977), Part I, Section 2.3, Theorem 4 and Corollary 2, printed p. 16
  (source `serre-1977-linear-representations`), through
  `finiteGaloisFrobeniusRigidityStatement`.

## Checks

A check with Lean 4.34.0 and Mathlib
`5ed2965256430c3649e86755f9576b54eca72435` compiled
this module against Library `97bd11ee` with no errors or warnings. The theorem
`Langlands.Global.chebotarevRigidityStatement` uses only the axioms
`propext`, `Classical.choice` and `Quot.sound`, and its universe parameters
are `u, v, w, z`.
