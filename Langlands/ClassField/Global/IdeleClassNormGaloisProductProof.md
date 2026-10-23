# The idele-class norm is the Galois product

The theorem
`Langlands.ClassField.Global.ideleClassNormGaloisProduct.{u,v}` proves exactly
`Langlands.ClassField.Global.IdeleClassNormGaloisProduct.{u,v}`, imported
from `IdeleClassNormGaloisProductStatement`. For number fields in independent
universes and any Galois extension `L / K`, it gives

```text
ideleClassInclusion (ideleClassNorm x)
  = ∏ σ : L ≃ₐ[K] L, relativeIdeleClassAut K L σ x.
```

The maps and the idele-class quotient are the existing published constructions.
The proof assumes no cyclic, abelian, or unramified hypothesis. Number fields
supply finite dimensionality and finiteness of the relative automorphism group;
the target's local `Fintype.ofFinite` only enumerates that group.

## Implemented proof

The proof first establishes the stronger formula on adeles. It compares
continuous maps on finite products of completions, where weak approximation
makes the diagonal image of `L` dense.

At a finite place `q` of `L`, put `p = q.under (𝓞 K)`. The private lemma
`relative_finitePlace_under` shows that every relative automorphism pulls `q`
back to another place above `p`. Indeed, its induced map on the ring of integers
fixes the image of every integer of `K`, so the two contracted prime ideals
are equal. This proof only needs the field and algebra structures.

The private lemma `finite_galois_product` compares two continuous maps from
`∏ w : FinitePlacesAbove L p, w.1.adicCompletion L` to `q.adicCompletion L`:

- take the product of local norms at `p`, then apply the completed inclusion
  into the completion at `q`;
- for each relative automorphism, select the coordinate at its pullback of
  `q`, apply `finiteCompletionEquiv`, and multiply all the resulting elements.

The published `denseRange_finiteAbove` reduces their equality to diagonal
field elements. On these elements,
`finiteNorm_principal_of_bijective` applies with the published
`completedTensorComparison`. The completed embeddings preserve field
embeddings, and Mathlib's `Algebra.norm_eq_prod_automorphisms` gives the
required equality. `DenseRange.equalizer` then proves equality on the whole
finite product. Evaluation on the coordinates of an arbitrary finite adele
gives the desired coordinate formula. No claim that principal full adeles
are dense is used.

At infinity, `infinite_galois_product` uses
`InfiniteAdeleRing.denseRange_algebraMap` and the same equalizer argument.
Its diagonal norm formula is the first projection of the published
`adeleNorm_principal`; arithmetic transport on diagonal elements is
`infiniteAdeleEquiv_diagonal`. The field norm product theorem again supplies
the equality on the dense image.

The private lemma `adele_galois_product` assembles the infinite and finite
formulas by product extensionality. The projection and coordinate monoid
homomorphisms preserve finite products. `Units.ext` then gives the identity
on actual ideles. Finally, `QuotientGroup.induction_on` chooses an idele
representative, the existing representative formulas for the quotient norm
and inclusion reduce the left side, and the quotient homomorphism preserves
the product. The quotient transport is definitionally the published
`relativeIdeleClassAut` on representatives.

Finite products are independent of the chosen `Fintype` instance. The
coordinate proofs explicitly identify the two universal finite sets when
Mathlib's automorphism enumeration differs from the target's enumeration.

## Provenance

This is a derived proof using the published arithmetic constructions,
completed tensor comparison, principal norm compatibility, and weak
approximation, together with Mathlib's field norm theorem. The new helper
lemmas are private implementation steps; the only new public declaration
is the exact requested theorem.

J. S. Milne, *Class Field Theory*, version 4.03 (2020), Chapter VII section 2,
printed pp. 206–207 (PDF pp. 215–216), supplies the mathematical source
correspondence: the Galois product on ideles, the products of local norms,
and the induced norm on idele classes. Registered source:
`milne-2020-class-field-theory`, local file
`/home/taskhub/central-library/Milne--Class Field Theory (v4.03)--2020.pdf`.
These pages were read for this proof. The Lean argument establishes the
compatibility by continuity and weak approximation; it does not claim to
formalize a particular proof from those pages. The original source
conventions for the three maps are also documented in the imported
statement's paired Markdown.
