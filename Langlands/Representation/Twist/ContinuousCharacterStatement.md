# Open kernels of continuous complex quasicharacters

`Langlands.ContinuousComplexCharacterOpenKernel` quantifies a group `G` with
a topology, an explicit instance of Mathlib's `NonarchimedeanGroup G`, and
every continuous homomorphism `chi : G →* ℂˣ`. It states that `chi.ker` is open.
The topology on complex units is Mathlib's standard units topology.

The nonarchimedean hypothesis includes the topological-group laws and requires
every identity neighborhood to contain an open subgroup. It is explicitly
quantified inside the proposition, so it cannot disappear as an unused section
instance. No local compactness, Hausdorffness of `G`, unitarity of `chi`, or
finite-dimensional representation is assumed.

This is the topological bridge needed to apply the separate open-kernel twist
smoothness target to continuous complex quasicharacters. It does not itself
assert that a particular p-adic group has a nonarchimedean topology, or prove
local Langlands.

## Provenance

This is an internal theorem from elementary complex analysis and Mathlib's
nonarchimedean group interface. A sufficiently small neighborhood of 1 in the
complex units contains no nontrivial subgroup. Pull continuity back to an
identity neighborhood in `G`, choose an open subgroup there, and show it lies
in the kernel. A subgroup containing an open subgroup is open.

Henniart's quasicharacter convention is a continuous complex homomorphism;
the additionally unitary ones are called characters. This motivating
convention is in Henniart 2000, Section 1.1, footnote 1, printed page 439
(PDF page 1), with the twisting use in Section 1.2(2), printed page 440
(PDF page 2). The general nonarchimedean-group theorem here is not attributed
to Henniart as a theorem from that passage.

- Literature ID: `henniart-2000-simple-proof`.
- Source SHA-256:
  `be283c3e8187f1eed365537c72379c3e06e7791756954c2ac783c6beea2979de`.
- Retained original:
  `C:/Central-Library/Henniart--Une preuve simple des conjectures de Langlands pour GL(n) sur un corps p-adique--2000.pdf`.

## Exact dependencies

There are no project definition dependencies. The environment is
`2ecc41bc-2901-4e34-96c5-6d98fbb3c74d` version 1, Lean 4.34.0,
Mathlib commit `5ed2965256430c3649e86755f9576b54eca72435`.
The main imported interfaces are `NonarchimedeanGroup`,
`NonarchimedeanGroup.is_nonarchimedean`, the topology on `Units`, and
`Subgroup.isOpen_of_openSubgroup`.

This proposition definition is a target, not an accepted proof.
