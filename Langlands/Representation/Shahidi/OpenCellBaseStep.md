# The open-cell integral for the `(1, n)` parabolic: setup

Module `Langlands.Representation.Shahidi.OpenCellBaseStep`, namespaces
`Langlands.Shahidi.OpenCell` and `Langlands.Shahidi.OpenCell.Base`.

## Contents

- `lower_mem_integralSubgroup`: `lower(Z)` is integral for integral `Z`; since
  `lower(Y + Z) = lower(Y) lower(Z)`, `openCellDepth_add_integral` and
  `liftFunction_lower_add_integral` show that the depth and (for a Levi-invariant `Φ`) the lift
  at `lower(Y)` are unchanged when `Y` is translated by an integral matrix.
- `IsWhittakerType ψ Ψ`: left `(N, θ_ψ)`-equivariance and right `GL(𝒪)`-invariance of a function
  on `GL_(t+1)(K)`.
- `shellΦ d Ψ (m₁, m₂) = [|det m₁| = q^(-d)] Ψ(m₂)` on `GL_1 × GL_(t+1)`, Levi-invariant when `Ψ`
  is right `GL_(t+1)(𝒪)`-invariant (`isLeviInvariant_shellΦ`), and
  `baseIntegrand d Ψ Y = F(lower Y) conj ψ(Y_last)` for its lift `F`;
  `liftFunction_shellΦ_eq_zero`: for such `Ψ` the lift vanishes at `lower(Y)` unless
  `openCellDepth Y = d`.
- `standardCharacter_nondegenerate'`, `whittaker_torus_eq_zero`: for `ψ` of conductor `𝒪`, the
  standard character is nontrivial on every simple root group over `ϖ⁻¹𝒪`, so a Whittaker-type
  function vanishes at torus points `ϖ^ν` with `ν` not antitone.

## Provenance

Setup for the rank-one computation in
`Langlands.Representation.Shahidi.OpenCellBaseInduction`.
