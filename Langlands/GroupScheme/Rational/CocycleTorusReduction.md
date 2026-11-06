# Actual finite-Galois reduction of a cocycle to a torus

`Cocycle.TorusReduction ξ` is data for an actual group scheme `G` over a field
`K : Type u` and a natural all-test cocycle on a relative scheme `U`. It records
an extension `E : Type u` that is finite Galois over `K`, its actual spectrum
`V = Spec E` over `Spec K`, and an fpqc refinement `r : V → U`. In particular,
quasi-compactness, flatness and surjectivity concern the actual underlying
scheme morphism `r.left`.

The remaining data are a cochain `f : V → G`, a ground-field group scheme `T`
with the existing `IsTorus` property, and a closed inclusion `j : T → G`.
For every `Z` over `K` and every `a,b : Z → V`, the definition requires an
actual point `t : Z → T` with

```
t ≫ j = f(a)⁻¹ * ξ(a ≫ r,b ≫ r) * f(b).
```

Thus the twist of the refined cocycle factors through this torus on every
relative scheme-valued test. The factorization is an existence requirement;
its uniqueness follows from the closed immersion but is not an additional
field of the structure. The cochain and cocycle use the convention already
implemented in `TorsorCocycle`. No restriction to rational points or to field
extensions is made in the test quantifier. Neither the torus nor the cochain
is required to be split or trivial on the original cover.

This is an internal concrete interface for cocycle reduction. It introduces
no existence theorem and applies as data to any `U` and `G`. The separate
`QuasiSplitCocycleTorusReductionStatement` asks for its existence when `G` is
quasi-split semisimple and `U` is a finite Galois field cover. The finite cover,
cochain, inclusion and all-test factorization make the remaining structural
proof obligation explicit; none is obtained merely by defining this structure.
