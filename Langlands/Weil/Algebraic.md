# Algebraic interface for the generic Weil pullback

`Langlands.Weil.AlgebraicProperties` is a proposition definition. The companion
[AlgebraicProof](AlgebraicProof.md) in the current Library proves it as
`Langlands.Weil.algebraicProperties : AlgebraicProperties.{u}`. This statement
module defines the target without introducing an axiom or importing its proof.
The parameter `u` allows the original group to live in any chosen universe.

The statement asserts injectivity of the canonical integer map into the actual
profinite completion. It then quantifies over every group `Γ` with a topology
and every continuous homomorphism `φ` into that completion, and asserts:

1. The square commutes: `φ ∘ projection = frobenius ∘ degree`.
2. `projection` is injective, and its image is exactly the inverse image under
   `φ` of the integer-Frobenius subgroup.
3. `inertiaInclusion` is injective and its composite with `projection` is the
   original subgroup inclusion of `ker φ` into `Γ`.
4. The image of `inertiaInclusion` is `inertiaSubgroup`, defined as the kernel
   of degree. Thus this is the required exactness at the pullback.
5. **If `φ` is surjective**, degree is surjective onto the integers.

The hypothesis in item 5 is essential to this interface. No surjectivity
of degree is claimed for arbitrary input. No splitting or Frobenius lift is
chosen. The group of degrees uses multiplicative notation for additive
integers, so the kernel is degree zero.

## Provenance and source correspondence

This is derived algebraic content of the explicit pair construction in
`Langlands.Weil.Pullback`. The injectivity of the integer map is the
residual-finiteness property of the integers. In `AlgebraicProof`,
`degree_residuallyFinite` separates a nonzero integer `n` using the finite
cyclic quotient `ZMod (|n| + 1)`; `frobenius_injective` then applies Mathlib's
criterion for injectivity into the profinite completion. The other clauses express
coordinate identities, the image/kernel description, and the consequence
of surjectivity of `φ`. They do not depend on unproved field-theoretic facts.

The motivating original source is Guy Henniart, *Representations du groupe de
Weil d'un corps local*, L'Enseignement Mathematique (2) 26 (1980), 155-172,
Section 2.1 and the first paragraph of Section 2.2, page 158 (PDF page 5).
These paragraphs give the integer-Frobenius preimage, inertia, and the
integer quotient for the actual local group. The present statement generalizes
the algebraic description to arbitrary `φ`, retaining the extra surjectivity
hypothesis wherever the integer quotient is asserted to be all of `ℤ`.

- `literature_id`: `henniart-1980-weil-representations`
- `content_sha256`: `451a8bd31a58be9bf5ce49588503c2d229b1a73bf3e65ae0c7b2f491c1c4e017`
- File: `C:/Central-Library/Henniart--Representations du groupe de Weil dun corps local--1980.pdf`
- Locator: Section 2.1 and first paragraph of Section 2.2, printed page 158,
  PDF page 5.
- [Original source DOI](https://doi.org/10.5169/seals-51064).

This is not a quotation of a general theorem from that source. The generic
statement and its dependencies must be independently reviewed.

## Exact dependencies and validation boundary

The only project definition dependency of this statement module is
`Langlands.Weil.Pullback`. No project proof dependency is imported here.
Its [paired Markdown](Pullback.md) explains the generic construction.
The actual p-adic specialization and geometric sign convention are supplied
by [Local/Assembly](Local/Assembly.md) and
[Local/AssemblyProof](Local/AssemblyProof.md).

Environment: `2ecc41bc-2901-4e34-96c5-6d98fbb3c74d`, Lean 4.34.0 at
`293d5d0c0c3f3dded4688b3ccd6a33939ac5102b`, Mathlib at
`5ed2965256430c3649e86755f9576b54eca72435`.

Compilation and target inspection check this proposition definition. Its proof
is the theorem in `AlgebraicProof`, including `degree_surjective`, which still
requires `Function.Surjective φ`. The current theorem and its full declaration
were checked for this documentation correction. The exported Test 2 receipts
record independent approval by Reviewer 82, accepted proof validation including
the exact target, and publication of `AlgebraicProof` at Test 2 commit
`5bc58c2525e0499012801c80f17b6a9c04d57263`. Its archived final Lean/Markdown
pair matches the pair carried into the current pilot Library. That commit
belongs to Test 2, whose Library seeded this pilot; it is not a pilot commit.
