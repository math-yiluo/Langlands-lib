# Etale affineness over arbitrary valuation domains

`Langlands.AlgebraicGeometry.ValuationRingEtaleAffinenessStatement.{u}` states:
for every commutative valuation domain `R` in universe `u`, every scheme `X` in
that universe and every morphism `f : X ⟶ Spec R`, if `f` is quasi-compact,
separated and etale, then `f` is affine. The ring may have arbitrary valuation
rank. No noetherian, discrete, positive-rank, henselian, algebraically closed
fraction-field, nonempty-source or group-scheme hypothesis is imposed.

This is a proposition definition, not a proof. It isolates general scheme
geometry that could support the arbitrary-base Weyl-quotient argument in the
fibrewise-affineness task.

## Original source and specialization

Michael Temkin and Ilya Tyomkin, *Prufer algebraic spaces*,
arXiv:1101.3199v3, 27 May 2016, provide the following ingredients:

- Corollary 4.1.15 and section 4.1.18, PDF/printed pages 17-18, identify
  valuation spectra as Prufer spaces and characterize their local rings.
- Corollary 4.1.17, page 18, preserves Pruferness under etale morphisms
  between quasi-compact quasi-separated algebraic spaces.
- Lemma 5.1.2, page 25, characterizes semi-local Prufer spaces by any etale
  presentation. Here semi-local means finitely many closed points.
- Lemma 5.1.7, page 26, describes quasi-compact generizing subsets of a
  semi-local Prufer space as finite unions of sets of generalizations of
  points.
- Proposition 5.1.9(i), page 26, says that a separated semi-local Prufer space
  is an affine scheme; its relative assertion identifies separated morphisms
  from such a space with affine morphisms.

For this specialization, `Spec R` is an affine valuation space. Quasi-compactness
of `f` makes `X` quasi-compact. Separatedness over the affine base makes `X`
separated and hence quasi-separated. The image of `f` is an open quasi-compact
subset `U` of the valuation spectrum. If it is nonempty, Lemma 5.1.7 and the
linear ordering of the prime ideals show that `U` has a unique closed point:
the finite union in that lemma is a single set of generalizations. Its scheme
structure is therefore again an affine valuation spectrum, by taking an affine
neighbourhood of that closed point, which contains all its generalizations.
Consequently `U` is semi-local Prufer. The factorization `X ⟶ U` is an etale
surjective presentation, so Lemma 5.1.2 makes `X` semi-local Prufer.
Proposition 5.1.9 then makes `X` affine. Since the target is affine as well,
`f` is affine. The empty-source case is affine directly.

This is a derived scheme specialization of the cited algebraic-space results.
The Lean statement uses the existing Mathlib `ValuationRing` class together with
`IsDomain`, ordinary schemes and their actual morphism properties. It introduces
no Prufer-space interface, supplied affine model, or extra data assumption.
Affineness of `f` is relative affineness; over the stated affine base this is
equivalent to affineness of `X`.

The retained source is registered as
`temkin-tyomkin-prufer-algebraic-spaces-1101-3199-v3`, SHA-256
`688f1b92a1c90787114822a656d797e3d3faf7ff0c5fdbdb8a0d5634640abc6d`.
The source PDF is at
`https://math.huji.ac.il/~temkin/papers/Prufer_Algebraic_Spaces.pdf`.
No source-specific errata note was found in the consulted Library.
