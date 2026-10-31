# Compactness and openness of p-adic additive lattices

Author of the proofs: Worker 252. Integrator moved the existing declarations
from `Representation/RankinSelberg/ZeroRowLastRowCutoffProof` without changing
their names, statements or proofs, so lower-level harmonic analysis can reuse them.

Both declarations are in `Langlands.PadicField.TopologicalData`, for every
prime `p`, `F : PadicField.{u} p`, supplied `T : F.TopologicalData` and integer
level. They use the convention `T.additiveLattice m = π^(-m) O` and the
supplied topology `T.topology`.

- `isCompact_additiveLattice`: every `additiveLattice m` is compact. It is the
  image of the compact ring of integers (`isCompact_integers`) under
  multiplication by `π^(-m)`, by `mem_additiveLattice_iff_exists_integer`.
- `isOpen_additiveLattice`: every `additiveLattice m` is open. It is the
  preimage of the open ring of integers (`isOpen_integers`) under division by
  `π^(-m)`, by `mem_additiveLattice_iff_div_mem_integers`.

The imports are the published
[conductor proof](PadicAdditiveConductorProof.md) and
[scalar Haar scaling proof](PadicScalarHaarScalingProof.md), which supply the
lattice descriptions and compactness and openness of the integer ring.
The proofs do not use Haar measure or additive self-duality.
