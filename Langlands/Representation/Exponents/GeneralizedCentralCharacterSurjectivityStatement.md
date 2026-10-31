# Surjectivity on uniform generalized central-character spaces

Authors: Worker 526 (draft) and Worker 277 (adaptation), with design guidance
from Workers 8 and 359.

`Langlands.GeneralizedCentralCharacterSurjectivityStatement.{uG,uV,uW}` is an
internal Prop-valued definition. This module states it and proves nothing.
The group universe `uG` and the two carrier universes `uV` and `uW` are
independent.

## The proposition

The proposition quantifies, in this order:

- an arbitrary group `G : Type uG`;
- complex vector spaces `V : Type uV` and `W : Type uW` (`AddCommGroup` and
  `Module ℂ`);
- actual representations `ρ : Representation ℂ G V` and
  `σ : Representation ℂ G W`.

It assumes that

```text
Module.Finite ℂ
  (Submodule.span ℂ (Set.range (fun z : Subgroup.center G => ρ (z : G))))
```

This is the span, inside `Module.End ℂ V`, of the source's action operators
`ρ z` for all elements `z` of the full centre `Subgroup.center G`. It is not
a span over a scalar subgroup chosen in advance, and it is not a finiteness
assumption on `V`, on `W`, on any central-character space, or on the length
of either representation.

Then, for every actual intertwiner `f : ρ.IntertwiningMap σ` with
`Function.Surjective f` on the ambient carriers, and for every
`χ : Subgroup.center G →* ℂˣ`, it asserts

```text
Function.Surjective (generalizedCentralCharacterMap f χ).
```

`χ` is a full algebraic character of the centre: no continuity or open
kernel is required, and `χ` need not occur in `ρ` or `σ`.

The spaces and the map are the existing public definitions of
`Langlands.Representation.Exponents.Central`.
`generalizedCentralCharacterSpace ρ χ` is the actual subrepresentation of
vectors `v` with

```text
∃ n, ∀ z : Subgroup.center G, ((ρ z - χ(z) • 1) ^ n) v = 0
```

(`mem_generalizedCentralCharacterSpace`): one finite exponent serves all
central elements for each vector. `generalizedCentralCharacterMap f χ`
restricts the given `f` to these subrepresentations of `ρ` and `σ`; no
other target action or map is introduced. Since that map sends `v` to
`⟨f v, _⟩`, the conclusion says: every `w : W` with
`∃ n, ∀ z, ((σ z - χ(z) • 1) ^ n) w = 0` equals `f v` for some `v : V` with
`∃ m, ∀ z, ((ρ z - χ(z) • 1) ^ m) v = 0`.

## What is not claimed or assumed

The exponent `m` of the preimage is not required to equal the exponent `n`
of the image, and nothing is asserted for the finite spaces
`centralCharacterSpace` at a fixed exponent. Such a fixed-exponent claim is
false. For example, let the integers act on `ℂ²` through the unipotent
Jordan block `[[1, 1], [0, 1]]`, and let `f` be the projection onto the
quotient by the invariant line, on which the integers act trivially. The
central operators span a two-dimensional space. For the trivial character,
the exponent-one space of the source is the invariant line, which `f` sends
to zero, while the exponent-one space of the target is the whole quotient.
At exponent two, the source space is all of `ℂ²` and maps onto the target.
The statement therefore keeps the generalized spaces with their nilpotent
directions; it does not replace them by scalar eigenspaces.

There is no topology, smoothness, open-kernel, local-constancy,
admissibility, irreducibility, finite-generation, occurrence, nonzero-space,
support or carrier-dimension hypothesis. No finiteness of the target's
central operator span is assumed. Zero carriers and the trivial group are
included. A character that does not occur in the source is handled by the
same statement: the conclusion then says that its target generalized space
is zero.

The module supplies no grouped real block, direct-sum decomposition or
projector construction, no finiteness of the full central span for an
actual Jacquet module, no Jacquet compatibility, no opposite geometric
identity layer, no strict tempered-exponent exclusion, no Hom factorization
and no dimension bound.

## Provenance and intended derivation

The proposition is internal algebra, not quoted from the literature. It is
motivated by the need to restrict actual quotient maps between
representations to generalized central-character spaces. Generalized
central-character spaces themselves follow Casselman's 1995 notes, section
2.1, as recorded in the `Central` Markdown.

Intended derivation, which this module does not carry out:

1. The span `B` of the central operators `ρ z` contains the identity
   (`z = 1`) and is closed under composition, since `ρ z ∘ ρ z' = ρ (z z')`
   with `z z'` central. It is therefore a commutative unital complex
   algebra, finite dimensional by the hypothesis.
2. The public topology-free lemmas of
   `Langlands.Representation.Exponents.FiniteActionSpectrumProof` apply to
   `B`: `FiniteActionSpectrum.finite_algHom` gives finitely many complex
   characters `φ` of `B`, and `FiniteActionSpectrum.exists_decomposition`
   gives `N` and elements `h φ` killed by `(ker φ) ^ N` whose sum is a
   unit, not necessarily one. Normalizing,
   `p φ = h φ * (∑ ψ, h ψ)⁻¹` gives elements with `∑ φ, p φ = 1` that
   are still killed by `(ker φ) ^ N`. These properties in fact make the
   `p φ` pairwise orthogonal idempotents: for `φ ≠ ψ` choose `b` in `B`
   with `φ b ≠ ψ b`; then `p φ * p ψ` is killed by the `N`-th powers of
   both `b - φ b • 1` and `b - ψ b • 1`, so it is zero by
   `FiniteActionSpectrum.eq_zero_of_pow_sub_smul` applied to
   multiplication by `b` on `B`, and hence
   `p φ = p φ * ∑ ψ, p ψ = p φ * p φ`. The argument below does not use
   idempotence. The vectors `p φ v` are generalized, not scalar,
   eigenvectors: their nilpotent directions are kept.
3. For each `φ`, the character `z ↦ φ (ρ z)` of the centre (compare
   `FiniteActionSpectrum.algebraCharacter`) is a unit-valued character
   `χ_φ`. Since `ρ z - χ_φ(z) • 1` lies in `ker φ`, every vector `p φ v`
   lies in the generalized `χ_φ` space of `ρ`, with the single exponent `N`
   for all central `z`.
4. Let `w` lie in the generalized `χ` space of `σ` and choose `v` with
   `f v = w`, using the ambient surjectivity of `f`. For `b = ρ z`,
   intertwining gives `f (b v) = σ z w`, which lies in the generalized `χ`
   space of `σ` because that space is a subrepresentation. By linearity the
   same holds for every `b` in `B`. Equivalently, `ker f` is stable under
   `B`, so `B` acts on `W`; this action is derived from `ρ` and `f`, not
   assumed.
5. If `χ_φ ≠ χ`, choose a central `z` with `χ_φ(z) ≠ χ(z)`. By step 3 and
   intertwining, `f (p φ v)` is killed by a power of `σ z - χ_φ(z) • 1`,
   and by step 4 also by a power of `σ z - χ(z) • 1`. The public
   `FiniteActionSpectrum.eq_zero_of_pow_sub_smul` then gives
   `f (p φ v) = 0`.
6. Hence `w = ∑ φ, f (p φ v) = f (∑ φ with χ_φ = χ, p φ v)`, and this last
   sum lies in the generalized `χ` space of `ρ` by step 3. No occurrence of
   `χ`, extension of `χ` to `B`, or idempotence is needed; an empty
   matching set and zero carriers fall under the same sums.

The lift uses the algebra's exponent `N`, which may exceed the exponent of
`w`; this is why only generalized spaces are stated.

## Imports

The module imports the public `Langlands.Representation.Exponents.Central`
unchanged, for `generalizedCentralCharacterSpace` and
`generalizedCentralCharacterMap`, together with Mathlib's complex numbers
and finite-dimensionality definitions. That file already proves that every
intertwiner preserves generalized central-character spaces; the additional
content stated here is surjectivity under the hypotheses above. The module
does not import `FiniteActionSpectrumProof`; the lemmas named in the
intended derivation are for a separate proof.
