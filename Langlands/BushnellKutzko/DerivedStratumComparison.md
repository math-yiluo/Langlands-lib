# Comparison of derived strata through `𝔄/𝔓`

This module compares strata over extension fields whose chains have the
lattices of a fixed `𝒪_F`-lattice chain `L`. It works through the residue ring
`𝔄/𝔓` of `L`. All results are proved.

## The element `y_b`

For a stratum `S` over a ring `O` with period `e`, level `n ≥ 0`, prime element
`π` and `g = gcd(e,n)`:

- `RingPrimeElement.mem_jacobson`, `Stratum.primeElement_smul_mem`,
  `Stratum.primeElement_smul_mem_endFiltration`: `π^k` moves `L_i` into
  `L_{i+ke}`.
- `Stratum.fundamental_shift_zero`: the exponents of `y_b` cancel,
  `(e/g)·(−n) + (n/g)·e = 0`.
- `Stratum.fundamentalElement_eq_pow`: `y_b = π^{n/g} b^{e/g}` with a natural
  exponent of `π`.
- `Stratum.fundamentalElement_mem_order`: if `b ∈ 𝔓^{−n}` then `y_b ∈ 𝔄`.
- `Stratum.fundamentalElement_sub_mem`: if two strata on the same chain have
  congruent elements modulo `𝔓^{1−n}`, their `y_b` agree modulo `𝔓`.

## Fundamentality and residues

- `LatticeChain.not_isNilpotent_of_shift`: let `g` carry each `L_i` onto
  `L_{i−k}`. Then no element of `g + 𝔓^{1−k}` is nilpotent. This is BK93 (2.3.2)
  for an arbitrary shifting endomorphism. The argument is that of
  `LatticeChain.not_isNilpotent_of_fieldShift`, which treats field units.
- `residueRestrict` and `residueQuotientMap`: for a chain `C` over `E` with the
  lattices of `L`, restriction of scalars maps the order of `C` into `𝔄`. The
  map `residueRestrict` composes this with reduction modulo `𝔓`. Its kernel is
  the first filtration ideal of `C` (`residueRestrict_eq_zero_iff`). Hence the
  induced map `residueQuotientMap` from `𝔅/𝔔` to `𝔄/𝔓` is injective
  (`residueQuotientMap_injective`).

## Residue centralizers

Let `D₁` and `D₂` be strata over two fields `E₁`, `E₂`. Their chains have the
lattices of `L`, they have the same level `n`, and `bᵢ ∈ 𝔔ᵢ^{−n}`.

- `residueCentralizer_map_le`: suppose `b₁ ≡ b₂ (mod 𝔓^{1−n})` in `End_F(V)`,
  and each element of the first order is congruent modulo `𝔓` to one of the
  second. Then the image in `𝔄/𝔓` of `Stratum.residueCentralizer D₁` lies in that
  of `Stratum.residueCentralizer D₂`. A lift `x₁` with
  `b₁x₁ − x₁b₁ ∈ 𝔔₁^{1−n}` is replaced by a congruent `x₂`. The identity
  `b₂x₂ − x₂b₂ = (b₁x₁ − x₁b₁) − b₁(x₁ − x₂) + (x₁ − x₂)b₁ − (b₁ − b₂)x₂ +
  x₂(b₁ − b₂)` shows that `b₂x₂ − x₂b₂ ∈ 𝔓^{1−n}`.
- `isSemisimpleRing_residueCentralizer_of_map_eq`: when the two images are
  equal, the residue centralizers are isomorphic rings, by the injectivity of
  `residueQuotientMap`. So semisimplicity of one gives that of the other.
  `subalgebraToSubringEquiv` identifies a subalgebra with its underlying
  subring.

Source: Bushnell and Kutzko, *The admissible dual of GL(N) via compact open
subgroups* (1993), (2.3.2) and the definition of `φ_b`, printed pp. 57–58, and
the residue centralizer of (2.4.13), printed p. 75, literature ID
`bushnell-kutzko-1993-admissible-dual-gln`, SHA-256
`811693b94c03fcbc2cfe33955bc5a00b0fc0b5645ca343f8cc1a3c6511de9c73`. The
comparison of residue centralizers serves the matrix calculation before (5.5)
in Bushnell and Kutzko, *Simple types in GL(N): computing conjugacy classes*
(1994), printed p. 133, literature ID
`bushnell-kutzko-1994-simple-types-conjugacy-classes`, SHA-256
`fd2077476192d9db15188feea9ff73774fe96296a2a31412d612f2081581efaa`.
