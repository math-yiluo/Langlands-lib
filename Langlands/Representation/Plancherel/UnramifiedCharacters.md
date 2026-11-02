# Unramified characters from rational norm characters

Author: Worker 200.

Waldspurger, *La formule de Plancherel pour les groupes p-adiques (d'après
Harish-Chandra)*, I.1, printed p.239 (PDF p.5), defines `G¹` as the intersection
of the kernels of `|χ|_F` over the `F`-rational algebraic characters of `G`,
and `X(G) = Hom(G/G¹, ℂ×)`. Here `Hom` denotes continuous homomorphisms. He
identifies `Im X(G)` with the unitary characters in this group. Source ID:
`waldspurger-2003-plancherel`; SHA256:
`4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`.

This module gives a generic construction used by that definition. Its inputs
are a group `G` with a topology and a family `ν : I → (G →* ℝ≥0ˣ)` of positive
characters, with independent universes for `G` and the indexing type `I`.
It assumes neither continuity of these input characters nor topological group
operations on `G`. The complex character values have their usual topology.

- `commonNormKernel ν` is the actual intersection of the kernels of `ν i`.
  Its membership lemma gives the simultaneous norm-one condition; normality
  follows from normality of the kernels.
- `unramifiedCharacters ν` is the subgroup of continuous complex characters
  trivial on this intersection. Its multiplication and inverse are pointwise.
- `unitaryCharacters G` consists of continuous characters whose complex values
  have norm one everywhere. `unitaryUnramifiedCharacters ν` is its intersection
  with `unramifiedCharacters ν`.
- `commonNormQuotientMap ν` is the actual quotient projection.
  `quotientCharacterPullback`, `unramifiedCharacterDescend` and
  `quotientCharacterEquiv` identify the constructed group with the continuous
  character group of `G / commonNormKernel ν`. Descent continuity follows from
  the quotient topology; the inverse laws are checked on representatives.
- `unramifiedCharacter_isOpen_ker` reuses the published
  `Langlands.isOpen_ker_of_continuous_complex_character` when
  `NonarchimedeanGroup G` supplies an identity neighborhood basis of open
  subgroups. This hypothesis is displayed and is not inferred from the
  algebraic family `ν`.

The quotient equivalence and open-kernel comparison are internal adapters for
the source definition, rather than new source assertions. They use Mathlib's
actual quotient group and the Library's continuous character theorem.

For the reductive specialization, `I` must enumerate all rational algebraic
characters and `ν i` must be their actual normalized absolute values. That
comparison, openness of `G¹`, and all rational-point topology realizations
remain separate obligations. No replacement reductive-group or representation
category is introduced.

This file supplies the underlying character groups only. It does not supply
the lattice or complex algebraic torus structure, the real-part map, compactness
of the unitary group, the finite-kernel restriction to the split center, or
Haar measures. In particular, it makes no probability-measure choice on
`Im X(G)`: the source instead fixes the measure locally preserved by the
restriction to `Im X(A_G)` after normalizing the latter to total mass one.
