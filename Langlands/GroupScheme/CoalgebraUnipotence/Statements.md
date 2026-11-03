# Coalgebra-unipotence criterion and quotient targets

Authors: Worker 1450 and Worker 572 (Lean statements and first Markdown
draft); Worker 1411 (Markdown revision and submission).

This module states two internal algebraic targets in the namespace
`Langlands.GroupScheme.CoalgebraUnipotence`. It imports
`Langlands.GroupScheme.CoalgebraUnipotence.Definitions` and uses its
predicates `IsMatrixUnipotent` and `IsLocallyConilpotent` unchanged. Both
targets are Prop-valued definitions; the module contains no proofs and asserts
neither statement.

## The fixed-vector criterion

`MatrixUnipotenceConilpotenceStatement.{u,v}` is the proposition

```
∀ (k : Type u) [Field k] (B : Type v) [Ring B] [Bialgebra k B],
  IsMatrixUnipotent k B ↔ IsLocallyConilpotent k B
```

In words: for every field `k` and every `k`-bialgebra `B` (in independent
universes `u` and `v`), the following two conditions are equivalent.

- `IsMatrixUnipotent k B`: for every `n > 0`, every matrix
  `a : Matrix (Fin n) (Fin n) B` satisfying the coefficient identities
  `comul (a i j) = ∑ l, a i l ⊗ₜ a l j` and
  `counit (a i j) = (1 : Matrix (Fin n) (Fin n) k) i j` admits a vector
  `v : Fin n → k`, `v ≠ 0`, with `∑ j, v j • a i j = v i • 1` for every `i`.
  As explained in `Definitions.md`, this is the basis form of "every nonzero
  finite-dimensional comodule presented by a basis has a nonzero fixed vector".
- `IsLocallyConilpotent k B`: every `b : B` lies in `reducedLevel k B n` for
  some `n`, i.e. the canonical filtration with level `0 = ⊥` and level `n + 1`
  the common inverse image of level `n` under the right translations
  `AffineLinearEmbedding.rightAct f` (`b ↦ ∑ f (b₂) • b₁` for
  `comul b = ∑ b₁ ⊗ b₂`), over all functionals `f` with `f 1 = 0`, exhausts
  `B`.

## The quotient statement

`ConilpotenceQuotientStatement.{u,v,w}` is the proposition

```
∀ (k : Type u) [Field k] (B : Type v) [Ring B] [Bialgebra k B]
  (C : Type w) [Ring C] [Bialgebra k C] (q : B →ₐc[k] C),
  Function.Surjective q → IsLocallyConilpotent k B → IsLocallyConilpotent k C
```

In words: for a field `k` and `k`-bialgebras `B` and `C` (in independent
universes `u`, `v` and `w`), if a bialgebra homomorphism `q : B →ₐc[k] C`
(Mathlib's `BialgHom`, a map preserving the algebra and coalgebra structures)
is surjective and `B` is exhausted by its reduced-translation levels, then so
is `C`.

## Hypotheses

Beyond `[Field k]`, `[Ring B]`, `[Bialgebra k B]` (and the same for `C`),
neither statement assumes finite generation, finite-dimensionality,
commutativity of `B` or `C`, an antipode (Hopf structure), perfection of `k`,
or any condition on the characteristic of `k`. The universes of `k`, `B` and
`C` are independent universe parameters of the two definitions.

## Provenance

Both statements are internal targets, introduced (together with the
definitions they use) as a field-level algebraic interface for the consumer
task 9bd631de-f76e-43b1-9177-d13439d4f731 on closed subgroups of unipotent
group schemes. They are not transcriptions of numbered results in the
literature. Their motivation is J. S. Milne, *Algebraic Groups: The Theory of
Group Schemes of Finite Type over a Field* (Cambridge University Press, 2017),
registered source `milne-2017-algebraic-groups`:

- Theorem 14.5 (printed p. 281, proof of (c) ⇒ (a) continuing on p. 282)
  proves that an algebraic group is unipotent (every nonzero representation
  has a nonzero fixed vector, §14.b, printed p. 280) if and only if its
  coordinate Hopf algebra is coconnected (Definition 14.4, printed p. 281).
  `MatrixUnipotenceConilpotenceStatement` is the analogue of the equivalence
  (a) ⇔ (c) for the internal predicates: fixed vectors are expressed through
  coefficient matrices, and Milne's coconnected filtration is replaced by the
  canonical reduced-translation filtration. As stated in `Definitions.md`,
  `IsLocallyConilpotent` is not Milne's coconnectedness, and the statement is
  for arbitrary bialgebras rather than coordinate algebras of algebraic
  groups.
- In the proof of (b) ⇒ (c) of Theorem 14.5 (printed p. 281), Milne notes that
  every quotient of a coconnected Hopf algebra is coconnected, because the
  image of a filtration satisfying his condition (91) still satisfies it.
  `ConilpotenceQuotientStatement` is the analogous assertion for the
  reduced-translation filtration and surjective bialgebra homomorphisms.
- Corollary 14.7 (printed p. 282) states that subgroups of unipotent algebraic
  groups are unipotent; Milne proves it through faithful unipotent
  representations. The intended consumer use is instead the coordinate-algebra
  route: a closed subgroup corresponds to a surjection of coordinate algebras,
  so the two statements together transfer `IsMatrixUnipotent` from the
  coordinate algebra of a group to that of a closed subgroup. The comparison
  between `IsMatrixUnipotent` and unipotence of a group scheme is not stated
  in this module.
