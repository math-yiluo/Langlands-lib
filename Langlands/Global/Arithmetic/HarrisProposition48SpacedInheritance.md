# Weights at distance at least two pass to the Mackey children of Proposition 4.8

This module proves that the two clauses of `Proposition48Problem.IsSpaced` (module
`HarrisProposition48SpacedData`) pass from a problem of the induction for Harris (1998),
Proposition 4.8, to each of its Mackey children. At a Mackey step the child's base field is
a copy of an intermediate field `D ⊇ E` of the normal closure `L`. The child's inducing
character is the Mackey character `a(ξ) ∘ N_{D·a(E')/a(E')}` on the compositum `D · a(E')`,
carried to the child's fields by the isomorphisms of the published `IsMackeyChild`. The
weights of the child above a place of `D` are among the weights of `ξ` above the place of
`E` below (Harris 1998, proof of Proposition 4.8, printed pp. 202–203; Henniart 2001, §5.9).
So weights at distance at least two stay so. All results are proved; only the standard
axioms are used.

## Results

All in namespace `Langlands.Global.Harris`.

- `IsRelativelySpaced.comap e e' hc h`: for isomorphisms `e : A ≃+* B` of base fields and
  `e' : A' ≃+* B'` of top fields compatible with the algebra maps, a character `χ` of `B'`
  relatively spaced over `B` gives a character `comap e' χ` of `A'` relatively spaced over
  `A`. The places of `A, A'` correspond to those of `B, B'` through the published
  `infinitePlaceEquiv`. The components correspond through the published
  `comap_infiniteComponent` and a square of completed maps, by density of the field in its
  completions. The rotation character `z ↦ z / z̄` is preserved or inverted according to
  the orientation of the embeddings; the condition is symmetric in `k ↦ −k`.
- `isRelativelySpaced_mackeyCharacter`: if `ξ` is relatively spaced over `E`, the Mackey
  character `Q.mackeyCharacter D a` is relatively spaced over `D`. Distinct places of
  `D · a(E')` above a place of `D` restrict to distinct places of `E'` above the place of
  `E` below. At those places the components of the Mackey character are those of `ξ`.
  This is the argument of the published private lemma
  `isRelativelyRegular_mackeyCharacter` of `HarrisProposition48MackeyCharacterProof`,
  extended by the rotation twist.
- `Proposition48Problem.IsSpaced.of_auxiliaryMackeyChild`: if `Q.IsSpaced` and
  `Q.IsAuxiliaryMackeyChild D a R`, then `R.IsSpaced`. For the real degree,
  `[R.E : ℚ] = [D : ℚ] = [D : E][E : ℚ]` is divisible by `4` with `[E : ℚ]`
  (`hasEvenRealDegree_iff`). For the weights, the child's character is `comap e'` of the
  Mackey character, and the two results above apply.

The parity correction of the induction is handled by
`Proposition48Problem.IsSpaced.withCorrectedCharacter` in `HarrisProposition48SpacedData`.
Together they give the passage of `IsSpaced` through every step of the induction:
the Mackey children and the corrected children.

## Provenance of the helper lemmas

The private lemmas `completedMap`, `completedMap_comp`, `completedMap_algebra`,
`completionEmbedding_of_eq`, `completionEmbedding_of_conjugate_eq`, `normComp_comap_component`,
`mackeyEmbedding` and `mackeyEmbedding_restricted_places_ne` repeat, with the same proofs,
the private lemmas of the same names in the published
`HarrisProposition48MackeyCharacterProof`. Private declarations of a module cannot be used
from another one. The new lemma `rotation_completedMap` computes the rotation character
along a completed map.

## Sources

- M. Harris, *The local Langlands conjecture for `GL(n)` over a `p`-adic field, `n < p`*,
  Invent. Math. 134 (1998), Proposition 4.8 and its proof, printed pp. 201–203. Registered
  `harris-1998-local-langlands`, SHA256
  `7934239ea37d0b91f741ae70c2ac157fe5d619cda4dd992ac24e39ae460c375b`.
- G. Henniart, *Sur la conjecture de Langlands locale pour `GL_n`*, J. Théor. Nombres
  Bordeaux 13 (2001), §§5.8–5.9, printed pp. 180–181. Registered
  `henniart-2001-langlands-locale-gln-jtnb`, SHA256
  `c9db009ee2f2e561d834b9e1ef07a8b27ff40d0edd19546d3351f38f39b2dac5`.
