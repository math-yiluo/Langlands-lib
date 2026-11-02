# The telescope resolution of increasing submodules

Let `R` be a commutative ring in universe `u`, let `M` be an `R`-module
in the independent universe `v`, and let `F : ℕ → Submodule R M` be
monotone. No finiteness, domain, or Noetherian hypothesis is imposed.

The entry definition `sequentialSubmoduleShortComplex` is the actual
complex of `R`-modules

```
⨁ n, F n  --difference-->  ⨁ n, F n  --augmentation-->  M.
```

On the `n`th summand, the shift is inclusion into `F (n + 1)`, followed
by insertion into the next summand. The difference is identity minus
this shift. The augmentation is the sum of the inclusions `F n → M`.
The composite is zero because both inclusions give the same element of
`M`.

The difference is injective: its coefficient at zero is the original
coefficient at zero, and its coefficient at `n + 1` is the original
coefficient there minus the image of the preceding coefficient. A zero
difference therefore forces every coefficient to vanish by induction.

To prove exactness, induction on the later index shows that insertion
in one summand and insertion of the same element in any later summand
differ by an element in the difference map's range. Direct-sum induction
then writes each finite sum, modulo that range, as a single element of a
common later summand. Its image in `M` is exactly the augmentation.
When the augmentation vanishes, the representative vanishes because
`F n` is a submodule of `M`. This proves equality of range and kernel.

If `iSup F = ⊤`, the augmentation is surjective, using Mathlib's
description of the range of the sum of submodule inclusions. The theorem
`sequentialSubmoduleShortComplex_shortExact` proves short exactness of
the displayed complex.

Finally,
`hasProjectiveDimensionLE_one_of_sequential_projective_submodules`
assumes each `F n` is projective and that the sequence exhausts `M`.
Both direct sums are then projective. Mathlib's dimension bound for a
short exact sequence gives projective dimension at most one for
`ModuleCat.of R M`.

This is an internal construction with an explicit elementary proof,
using Mathlib's direct sums, submodule inclusions, and homological
dimension API. It supplies a conditional algebraic prerequisite; it
does not assert that any specified module admits such an exhaustion,
that a polynomial ring is coherent, or that a line bundle extends.
