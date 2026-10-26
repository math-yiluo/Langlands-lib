# Finite character-localization filtration collapse

Author: Worker 673. The theorem
`Langlands.Jacquet.Localization.filtrationCollapse.{uG,uV}` proves exactly the
closed published proposition
`Langlands.Jacquet.Localization.FiltrationCollapseStatement.{uG,uV}`.
Its group and representation-carrier universes are independent. The statement
pair and all its imports are preserved.

The proof uses the actual finite filtration, its invariant subspaces, their
successive quotients, and the actual character-localization maps. The selected
quotient can occur at any index and can itself have zero localization.

## Adjacent sequences and localization

Write `S_k = s.subrepresentation k`, `Q_i = s.gradedRepresentation i`, and
`C(ρ) = Coinvariants ρ ⊤ (θ.comp (⊤ : Subgroup G).subtype)`.

The private `stepEmbedding` is the inclusion of a subrepresentation into
the ambient representation. The private `stepInclusion` is the actual
submodule inclusion for two ordered subrepresentations. Both are
intertwiners because the step actions restrict the ambient action.
Monotonicity gives an inclusion `S_i → S_(i+1)`, injective by equality of
the underlying vectors.

The private `adjacent_exact` proves that its range equals the kernel of
`s.gradedProjection i`. The latter is the actual quotient projection onto
the upper step modulo the pullback of the lower step. The submodule
quotient zero criterion identifies its kernel with the upper-step vectors
lying in the lower step. Such a vector has a unique lift to the lower step.
Together with `s.gradedProjection_surjective`, this derives the adjacent
short exact sequences from the filtration data.

`isSmooth_of_injective`, applied to `stepEmbedding`, gives smoothness of
every step from smoothness of the ambient representation. The restricted
character on the top subgroup is locally constant by composition with
the continuous subtype map. The normalizing subgroup is `⊥`: its inclusion
in the normalizer is automatic, and its only element is the identity,
so it preserves the character.

The imported `LocalizationExactnessProof` supplies
`map_injective_of_smooth`, `map_range_eq_ker`, and `map_surjective`.
Applied to the derived adjacent sequences, they show that the underlying
localized linear maps

```text
f_i : C(S_i) → C(S_(i+1)),
p_i : C(S_(i+1)) → C(Q_i)
```

are respectively injective, middle exact, and surjective. The Lean proof
uses `mapLinear`, definitionally the underlying linear map of the
`Localization.map` appearing in those imported theorems. Only smoothness
of the upper step is required by the injectivity theorem.

If `i ≠ j`, the hypothesis that `C(Q_i)` is subsingleton makes every
upper-step vector lie in the kernel of `p_i`. Middle exactness then
makes `f_i` surjective. Combined with injectivity this gives a linear
equivalence through `LinearEquiv.ofBijective`.

## Implemented finite induction and endpoints

The initial step is zero by `s.subrepresentation_zero`. Its carrier is
subsingleton, and so is its localization. `Fin.induction` proves, for
each step index `k`, both implications:

```text
k ≤ j  →  Subsingleton (C(S_k)),
j < k  →  Nonempty (C(S_k) ≃ₗ[ℂ] C(Q_j)).
```

In a successor step below or at `j`, the relevant quotient has index
different from `j`. The surjective localized inclusion carries the
subsingleton previous step onto the new step.

At index `j`, the preceding step is subsingleton. If two elements have
the same image under `p_j`, their difference lies in its kernel and
therefore in the range of `f_j`. Every vector in the source of `f_j`
is zero, so the difference vanishes. Thus `p_j` is injective as well
as surjective, giving the required equivalence at step `j + 1`.

At a later index, the inverse of the bijective localized inclusion
is composed with the previous equivalence to `C(Q_j)`. This proves the
second implication throughout the remaining steps.

Finally `j.isLt` places the last step above `j`. The endpoint identity
`s.subrepresentation_last` makes its actual inclusion into `A` surjective.
Its localization is bijective by the same imported injectivity and
surjectivity results. Composing the inverse of that equivalence with the
inductively constructed equivalence proves the required existence of
`C(A) ≃ₗ[ℂ] C(Q_j)`.

## Source, provenance, and scope

This is a derived finite-induction consequence of the published exactness
theorem and object-filtration definitions. Its proof route was specified
in the published statement companion and task context; no unpublished
proof draft was reused.

The source context is I. N. Bernstein and A. V. Zelevinsky, *Induced
representations of reductive p-adic groups I*, Ann. Sci. ENS (4) 10 (1977),
441–472. Registered source: `bernstein-zelevinsky-1977-induced-i`.
The retained original is
`/home/taskhub/central-library/Bernstein-Zelevinsky--Induced representations of reductive p-adic groups I--1977.pdf`,
SHA256 `8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`.
Worker 673 read PDF pages 5–6: section 1.8(b), printed page 444, defines
the character-relation quotient; the paragraph preceding Proposition 1.9
and Proposition 1.9(a), printed page 445, give the compact-subgroup
condition and exactness; section 1.11 on that page describes finite
zero-to-full filtrations. No source-specific errata entry was found in
the available project and Library notes.

The single-survivor assertion is an internal consequence, not a literal
theorem quotation from BZ77. Its arbitrary-topological-group scope comes
from the published localization exactness proof. The conclusion concerns
complex quotient vector spaces, with no additional action or modulus
normalization. No splitting, finite-dimensionality, or additional
exactness hypothesis is introduced.

The module was checked with environment
`3b864ddf-f0af-4c18-8903-c6f813a0ce0f` (Lean 4.34.0; Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`). The development Lake build
and declaration inspection succeeded, with universe parameters `uG`, `uV`
and only the assumptions `propext`, `Classical.choice`, and `Quot.sound`.
Independent semantic review and publication remain separate requirements.
