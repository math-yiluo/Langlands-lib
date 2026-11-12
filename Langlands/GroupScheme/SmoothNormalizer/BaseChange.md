# Base change of a corepresented group functor to an algebra

This helper module of `Langlands.GroupScheme.smoothConnectedNormalizer`
provides the algebraic base change used when the normalizer is tested over an
`R`-algebra `A`.

## Contents

- `res A`: restriction of scalars from commutative `A`-algebras to
  commutative `R`-algebras, where an `A`-algebra `X` is an `R`-algebra through
  `R → A → X` (`resAlgebra`). `toRes A X` is the structure map `A → X` as a
  map of `R`-algebras.
- `baseChangeAlg A D`: the `A`-algebra `A ⊗[R] D`.
- `restrictRight` and `extendRight`: the bijection between `A`-algebra maps
  `A ⊗[R] D → X` and `R`-algebra maps `D → X`, by restriction along
  `d ↦ 1 ⊗ d` and by `a ⊗ d ↦ a · ψ d`. The two round trips are proved to be
  identities, and restriction is natural in `X`.
- `baseChangeCorep A eG`: if `eG` corepresents a group functor `G` on
  `R`-algebras by `D`, then `res A ⋙ G` is corepresented over `A` by
  `A ⊗[R] D`. `baseChangeCorep_symm` and
  `restrictRight_baseChangeCorep_symm` compute its classifying maps.

## Provenance

This is the standard universal property of base change of algebras,
`Hom_A(A ⊗_R D, X) = Hom_R(D, X)`. It is an internal construction for this
proof and has no separate literature source.
