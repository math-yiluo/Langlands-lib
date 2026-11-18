# Intertwining of a simple stratum (T4)

Source: Bushnell–Kutzko, *The admissible dual of GL(N) via compact open subgroups*
(1993), `bushnell-kutzko-1993-admissible-dual-gln`, Theorem (1.5.8), printed
p. 44 (PDF p. 56), and the scalar convention (1.4.6), printed p. 36.

`SimpleIntertwiningStatement` is an unproved proposition definition for
every nonarchimedean local field `F`, finite-dimensional vector space `V`
and simple stratum `S`. The universes for `F` and `V` are independent.
Its equality is exactly
`I_G(S) = (1 + 𝔔^{−(r+k)}𝔑_k) Bˣ (1 + 𝔔^{−(r+k)}𝔑_k)`.
Multiplication of subsets of `Aˣ` is pointwise set multiplication.

The two auxiliary definitions spell out the right-hand side:

- `centralizerUnits β` consists of the ambient units commuting with `β`.
  A unit commuting with `β` has inverse commuting with `β`, so this is
  precisely the image of the unit group of its centralizer.
- For finite critical exponent `k`, `simpleIntertwiningNeighborhood S`
  consists of the ambient units `g` with
  `g − 1 ∈ centralizerLattice S.chain S.b (−(r+k)) · adjointLattice … k`.
  The lattice product is the submodule spanned by products. It is
  exactly `1 + 𝔔^{−(r+k)}𝔑_k` as a subset of `G`; for a simple
  stratum the exponent `−(r+k)` is positive.

When `F[β] = F`, the source sets `k₀ = −∞`. We explicitly give the
neighborhood the value `{1}` in that case, interpreting the positive
infinite radical depth. Here `Bˣ = G`, and every `g` intertwines the
stratum since the scalar `β` belongs to both cosets. Thus the same
statement covers scalar simple strata without an extra exclusion.
This is an explicit extension of the notation in (1.5.8) to the
exceptional convention (1.4.6); it assumes no theorem.

The left-hand side is the formal self-intertwining definition of
(1.5.7). All orders, radical powers, adjoint lattices and critical
exponents are the existing definitions. No intertwining conclusion
is part of the hypotheses.
