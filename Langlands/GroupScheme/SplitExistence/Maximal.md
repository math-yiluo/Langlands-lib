# The torus is a maximal torus of the Chevalley group

Module `Langlands.GroupScheme.SplitExistence.Maximal`, namespace
`Langlands.GroupScheme.SplitExistence.ChevalleyData.ChevGroup`. Internal helper of the proof of
the split reductive Existence Theorem (task 2132924b). The argument is the classical one: a torus
equal to its own centralizer is maximal.

## Declarations

- `torusCentralizer_le_centralizer`: the Library's all-test centralizer `torusCentralizer t`
  of the torus lies in the dynamic centralizer `Z_G(λ)` of the regular cocharacter. A point
  `g` that commutes with every torus point commutes with `λ(s)`. Hence its conjugation orbit
  `λ(s) g λ(s)⁻¹` is constant, which is the defining equation of `Z_G(λ)`.
- `range_le_torusCentralizer`: the torus centralizes itself, because its points form a
  commutative group and `t` is a homomorphism.
- `torusCentralizer_eq` (`J` finite, `P` reduced, `X` finitely generated): the two inclusions
  together with `centralizer_le` (module `Centralizer`) give
  `torusCentralizer t = range t`.
- `isMaximalTorus`: `t : D(X) ⟶ G` is a maximal torus in the Library's sense. The torus is
  split (`isSplitTorus_Tk`), `t` is closed (`t_closed`), and the Library's
  `isMaximalTorus_of_torusCentralizer_eq` turns the self-centralizing equation into
  maximality.
