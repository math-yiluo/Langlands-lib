# Conditional exclusion of actual local rank-one E₈ indices

For an actual Tits index `d` over a nonarchimedean local field of any field
or residue characteristic, assume split rank one and an equivalence of its
actual simple vertices with `Fin 8` preserving every Cartan entry of
Mathlib's numbered E₈ matrix. Under the explicit premise
`LocalAnisotropicCartanComponentsStatement`, the theorem derives a
contradiction. The universe is arbitrary.

E₈ Cartan rigidity forces the full absolute Galois star action to be
trivial. The actual rank-one orbit comparison then makes the distinguished
set exactly one vertex. Every other simple root has zero restriction to the
maximal split torus.

The explicit twenty-eight-reflection certificate in `CartanE8Root` gives an
actual root with coefficient vector `(2, 3, 4, 6, 5, 4, 3, 2)`. Restricting
this integral combination to the actual maximal split torus leaves its
coefficient at the distinguished vertex times that simple root's
restriction. If the distinguished vertex is 1, 2, 3 or 4, that coefficient
is 3, 4, 6 or 5. The characteristic-independent relative-root multiple bound
excludes each of these values, including for a possibly nonreduced relative
root system.

For a distinguished vertex of 0, 5, 6 or 7, the central vertex 3 and its
three distinct neighbors 1, 2 and 4 all have zero restriction. The explicit
component premise, transported through the actual anisotropic-kernel index
comparison, forbids a zero vertex with three distinct Cartan `-1`
neighbors. This gives the other four contradictions.

This is an internal deduction from the root-datum reflection formula,
finite Cartan rigidity, actual rank-one orbit comparison, the relative-root
multiple bound and the supplied component premise. It proves neither that
premise nor the unconditional local rank-one enumeration and uses no
downstream classification or Kneser–Tits theorem.
