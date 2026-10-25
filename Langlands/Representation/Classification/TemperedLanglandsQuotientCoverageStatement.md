# Independent positive-rank tempered quotient coverage

Author: Worker 171.

`Langlands.Classification.TemperedLanglandsQuotientCoverage.{uF,uV} F T`
is an internal, independent proof-decomposition target. It states existence
of a tempered standard module surjecting onto each irreducible smooth input
representation of positive-rank `GL_n(F)`. This module defines a proposition;
it does not prove coverage.

## Exact scope

The outer parameters are exactly
`{p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)`.
After installing `T.topology`, the proposition quantifies over every `n : ℕ`,
assumes `0 < n`, and quantifies over every
`π : SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear n F.Carrier)`.
Its only hypothesis on this input is
`Representation.IsIrreducible π.representation`. Its conclusion is

```lean
∃ t : T.TemperedLanglandsDatum.{max uF uV, uF} n,
  t.IsLanglandsQuotient π
```

The field universe `uF` and carrier parameter universe `uV` are independent.
The blocks, standard module and input representation have carriers in
`Type (max uF uV)`, which is closed under the actual induction construction.
All primes, p-adic fields and supplied topological data remain arbitrary.
Rank zero is outside this statement and remains a separate exact target.

The sole import is the published
[`LanglandsData`](LanglandsData.lean). Its `TemperedLanglandsDatum` contains an
ordered positive block shape, actual smooth irreducible analytically tempered
block representations, and real determinant exponents satisfying `StrictAnti`.
The standard module is normalized induction from the standard upper block
parabolic of the external tensor product of the blocks twisted by
`|det|^(t.exponent i)`. The actual covariant functions have the positive
half-modulus factor `δ_P^(1/2)` and carry right translation,
`(g · f)(x) = f(x g)`. These are the existing constructions in
[`BlockFactors`](../Induction/BlockFactors.lean), used through `LanglandsData`.

The relation `t.IsLanglandsQuotient π` unfolds to irreducibility of
`π.representation` and existence of an actual surjective intertwiner
`t.standardModule.representation.IntertwiningMap π.representation`.
The target is the original `π`; there is no replacement by an isomorphic
representative. There is no full-product kernel-uniqueness clause, no
`IsLanglandsHead` conclusion and no admissibility premise on `π`.

## Provenance and independence

This is an internal decomposition of the classification program, using the
published data and quotient relation. Its purpose is to supply the quotient
existence needed before refinement from tempered blocks to ordered special
segments. No new translation of an original literature theorem or proof of
that theorem is claimed here.

The separately published theorem
`Langlands.CuspidalSupport.cuspidalEmbedding` in
[`CuspidalEmbeddingProof`](../CuspidalSupport/CuspidalEmbeddingProof.lean)
supplies automatic admissibility for an irreducible smooth input, including
the present saturated carrier universe. A future independent proof using
Jacquet exponents may obtain admissibility from that theorem. The present
definition neither imports its proof nor adds its conclusion or the theorem
itself as a premise.

The stronger exhaustion proposition in
[`RegularLanglandsStatement`](RegularLanglandsStatement.lean) describes an
irreducible head under an admissibility premise. This comparison is
descriptive only. The proof of the present target must not depend, directly
or transitively, on ordered special-segment quotient coverage, multisegment
exhaustion, square-integrable exhaustion, or regular Langlands exhaustion.
Shared lower-level results can be used only after their dependencies have
been checked for this independence.

## Reciprocity direction and remaining proof obligations

The published `Langlands.Jacquet.characterReciprocity` in
[`ReciprocityProof`](../Jacquet/ReciprocityProof.lean) has the direction

```text
Hom(input, character-normalized induction of σ)
  ≃ Hom(character-inverse-twisted coinvariants of input, σ).
```

It identifies maps **from the input into induction**, not maps from induction
onto the input. A quotient of an opposite Jacquet module therefore does not
directly produce the upper-induced surjection required here.

A future proof using contragredients must establish the needed analytic
dual preservation, smooth bidual/reflexivity, induction duality,
positive-half-modulus normalization, exponent signs and block reversal,
or give a different correct independent route. These steps are proof
obligations, not additional theorem-valued assumptions in the exact target.
Likewise, a proposed maximal-cone argument must justify its selection
principle and the conversion of a whole-Levi tempered representation into
tempered general-linear blocks; a statement of either step is not a proof.

The present module supplies no Jacquet selection, tensor temperedness,
duality, reversal or exhaustion theorem. Its exact proof is a separate
successor task after independent acceptance and publication of this statement.
