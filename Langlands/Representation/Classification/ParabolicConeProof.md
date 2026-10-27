# Root/weight cone theorem for GL block parabolics

Author: Worker 534.

`Langlands.glParabolicRootWeightCone` proves exactly the published
`Langlands.GLParabolicRootWeightConeStatement`, with arbitrary ring universe
`uR`. For every positive rank, actual fine block shape and real exponent
vector, it gives a unique actual coarse block shape with all the numerical
conditions and the parabolic and Levi containments over every commutative
ring in that universe.

## Implemented proof

The proof assembles three established theorems imported from their proof
modules:

- [`glBlockConeExists`](ParabolicConeExistenceProof.md) supplies the coarse
  shape `C`, a monotone surjection `q`, and a strictly antitone vector `t`.
  Its numerical conditions give the fiber sizes, fiber averages and
  nonpositive residual sums on initial segments of each fiber.
- [`glBlockCoarseningSubgroups`](ParabolicConeSubgroupProof.md) takes this
  same `q`, its monotonicity and surjectivity, and the fiber-size equations.
  It gives both actual subgroup containments for every commutative ring.
  These complete the existence witness for the target.
- [`glBlockConeUnique`](ParabolicConeUniquenessProof.md) compares that
  witness with any competing coarse shape `D`. The proof extracts the
  numerical conditions from the competing witness and applies numerical
  uniqueness with `D` first and `C` second, obtaining the equality `D = C`
  required by `ExistsUnique`.

The imported numerical existence theorem applies to every natural rank,
including zero. The separate subgroup theorem applies to every
size-compatible monotone surjective coarsening, independently of the
numerical cone conditions. These remain public named theorems available
through this module's imports. The closing theorem keeps the target's
positive-rank quantifier; its proof does not need that positivity assumption.
Uniqueness is asserted for the actual ordered block shape `C`; the maps
and exponent vectors are existential witnesses.

## Provenance

This is an internal assembly proof for the coordinate specialization
documented in [the target's paired Markdown](ParabolicConeStatement.md).
Its numerical existence, numerical uniqueness and matrix arguments are
implemented in the three imported proof modules and described in their
paired Markdown. The target statement and its imported definitions are
preserved unchanged.
