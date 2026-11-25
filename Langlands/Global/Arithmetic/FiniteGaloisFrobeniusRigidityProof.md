# Proof of finite Galois Frobenius-trace rigidity

This file proves the Library statement
`Langlands.Global.FiniteGaloisFrobeniusRigidityStatement.{u, v, w, z}`
of `Langlands/Global/Arithmetic/ChebotarevStatement.lean`, exactly as
published, at arbitrary universes. It introduces no statement and no
hypothesis beyond those of the target.

## Declarations

- `Langlands.Global.finiteGaloisFrobeniusRigidity_of_primeRealization
  (h : ChebotarevPrimeRealizationStatement.{u, v}) :
  FiniteGaloisFrobeniusRigidityStatement.{u, v, w, z}`
  is the reduction. It depends only on Mathlib and two Library
  modules: the statement file and the finite character theory proof.
- `Langlands.Global.finiteGaloisFrobeniusRigidityStatement :
  FiniteGaloisFrobeniusRigidityStatement.{u, v, w, z}`
  is the target theorem. It applies the reduction to the Library's proof
  `Langlands.Global.chebotarevPrimeRealizationStatement` of module
  `Langlands.Global.Arithmetic.ChebotarevPrimeRealizationProof` (the port
  of the Chebotarev closure of the Anthropic FLT repository).
  Prime realization therefore enters as a proved theorem, not as a
  premise.

## The implemented proof

Fix number fields `K` and `L` with `[Algebra K L] [IsGalois K L]`, complex
finite-dimensional representations `ρ` on `V` and `τ` on `W` of
`L ≃ₐ[K] L`, a finite set `S` of height-one primes of `𝓞 K`, and the trace
hypothesis `hS`.

1. **Equality of characters.** By function extensionality it suffices to
   show `ρ.character σ = τ.character σ` for each `σ : L ≃ₐ[K] L`. Prime
   realization at `K`, `L`, `σ`, `S` gives a height-one prime `p ∉ S` of
   `𝓞 K` and a height-one prime `q` of `𝓞 L` with `q.asIdeal.LiesOver
   p.asIdeal`, `Algebra.IsUnramifiedAt (𝓞 K) q.asIdeal` and
   `(RingOfIntegers.mapAlgHom σ).IsArithFrobAt q.asIdeal`. These are exactly
   the four premises of `hS` at `p`, `q` and `σ`, so `hS` gives the
   equality at `σ`. The lying-over, unramifiedness and Frobenius
   predicates of the two Library statements are the same Mathlib terms, so
   the witnesses are passed on without conversion.
2. **Character theorem.** `Langlands.FiniteCharacter.isomorphism` (Library
   `Langlands/Representation/Finite/CharacterTheoryProof.lean`), whose
   statement is `Langlands.FiniteCharacterIsomorphismStatement`, says that
   for a finite group `G` two finite-dimensional complex representations
   have equal characters if and only if `Nonempty (ρ.Equiv σ)`. It is
   applied with `G := L ≃ₐ[K] L`, and its forward direction turns step 1
   into the conclusion `Nonempty (ρ.Equiv τ)`.

The instances needed by the character theorem are found by instance
search, with no transport. The group structure is Mathlib's
`AlgEquiv.aut`, the one used in the statement's
`Representation ℂ (L ≃ₐ[K] L) V`. `[Fintype (L ≃ₐ[K] L)]` is Mathlib's
`AlgEquiv.fintype` (`Mathlib/FieldTheory/Fixed.lean`). It uses
`FiniteDimensional K L`, which is Mathlib's instance for an algebra between
number fields (`Mathlib/NumberTheory/NumberField/Basic.lean`). The
`Fintype` instance appears only in the hypotheses of the character theorem,
not in the target, so no compatibility of instances is needed.
`Representation.character` and `Representation.Equiv` in the target are
the same Mathlib constructions as in the character theorem.

## Sources

The route is the two-step argument recorded in the target's Markdown
(`ChebotarevStatement.md`, section "Character rigidity"). It is also in the
plan note `operator-external-inputs-plan-2026-11-16`, Section 2.6
(interface F) and Section 4.4.

- Equality of complex characters determines a representation up to
  isomorphism: J.-P. Serre, *Linear Representations of Finite Groups*
  (1977), Part I, Section 2.3, Theorem 4 and Corollary 2, printed p. 16
  (source `serre-1977-linear-representations`). It is used only through
  the Library's `Langlands.FiniteCharacter.isomorphism`.
- Realization of every automorphism as a Frobenius outside a finite set:
  J. Neukirch, *Algebraic Number Theory* (1999), Chapter VII,
  Theorem 13.4, printed pp. 545–546 (source
  `neukirch-1999-algebraic-number-theory`). It is used only through the
  Library's `Langlands.Global.chebotarevPrimeRealizationStatement`.

## Checks

A check with Lean 4.34.0 and Mathlib
`5ed2965256430c3649e86755f9576b54eca72435` compiled
this module against Library `2613dbbf`, which contains the published
`ChebotarevPrimeRealizationProof` module, with no errors or warnings. The target theorem
`Langlands.Global.finiteGaloisFrobeniusRigidityStatement` uses only the axioms
`propext`, `Classical.choice` and `Quot.sound`, and its universe parameters
are `u, v, w, z`. An earlier check compiled the reduction alone against
Library `97101ec2`, with the same axioms and universe parameters.
