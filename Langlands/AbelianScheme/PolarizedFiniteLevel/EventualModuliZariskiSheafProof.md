# Proof: the ordinary polarized full-level moduli functor is a Zariski sheaf for large levels

Module `Langlands.AbelianScheme.PolarizedFiniteLevel.EventualModuliZariskiSheafProof`. The
theorem

```lean
theorem Langlands.AbelianScheme.PolarizedFiniteLevel.eventualModuliZariskiSheaf :
    EventualModuliZariskiSheafStatement
```

proves `EventualModuliZariskiSheafStatement` (module `EventualModuliZariskiSheafStatement`; the
statement has no universe parameter). Unfolded, the statement is

```lean
∀ (P : Prerequisites.{0}) (g d : ℕ) (_hg : 0 < g) (hd : 0 < d),
  ∃ N : ℕ, ∀ (n : ℕ), N ≤ n → ∀ (hn : 3 ≤ n),
    LevelBase.IsZariskiSheaf (moduliFunctor P g d n hd hn)
```

In words: for the published prerequisites `P : Prerequisites.{0}` and natural numbers `g d` with
`0 < g` and `0 < d`, there is a bound `N` such that for every level `n` with `N ≤ n` and
`3 ≤ n` the ordinary polarized full-level moduli functor `moduliFunctor P g d n hd hn` satisfies
the Zariski sheaf condition for open covers of level bases: compatible isomorphism classes of
data over the members of an open cover of a locally noetherian scheme on which `n` is a unit come
from exactly one class over the whole scheme.

## Proof as implemented

The proof is a single term.

1. `eventualModuliZariskiSheaf_of_cubicFieldEmbedding` (module
   `ModuliZariskiSheafOfRigidityProof`) is a proved definition of type
   `CubicFieldEmbeddingStatement.{0} → EventualModuliZariskiSheafStatement`. It is
   `eventualModuliZariskiSheaf_of_rigidity hL moduliZariskiSheafOfRigidity`: Lefschetz's
   embedding over fields gives, for large levels, the rigidity of polarized automorphisms that
   fix the level sections (the torsion points are too many to lie in the eigenspaces of a
   non-scalar projective automorphism), and `moduliZariskiSheafOfRigidity` turns this rigidity
   into the Zariski sheaf property by gluing data and isomorphisms along the cover.
2. `cubicFieldEmbedding.{0}` (module `CubicFieldEmbeddingProof`) proves
   `CubicFieldEmbeddingStatement.{0}`, Lefschetz's theorem for the canonical cubic bundle of an
   ordinary polarized datum over a field.

## Declarations

- `eventualModuliZariskiSheaf : EventualModuliZariskiSheafStatement` (theorem).

## Provenance

The statement is derived; its page combines two classical facts, uniqueness of level-preserving
polarized isomorphisms at large level and gluing. D. Mumford, J. Fogarty and F. Kirwan,
*Geometric Invariant Theory*, 3rd enlarged edition (1994), registered as
`provided-ec58cb66687d0d54d9e39b6ec21281b651fe3a6d039f9b5d099c79791671233f` (PDF page = printed
page + 13):

- Chapter 7, §3, Proposition 7.7, printed p. 138 (PDF page 151): for an abelian variety
  `A ⊂ P_m` of dimension `g` and degree `r` not contained in a hyperplane and `n > √((m+1)·r)`
  prime to the characteristic, the `n^{2g}` points of order `n` form a stable point; the proof
  shows that fewer than `n^{2g}/(m + 1)` of them lie on any hyperplane (printed pp. 138–139).
- Corollary 7.8, printed p. 139 (PDF page 152): the case `n > 6^g · d · √(g!)` for the moduli of
  linearly rigidified abelian schemes.
- Chapter 6, Corollary 6.2, printed p. 116 (PDF page 129): the rigidity lemma; over a connected
  base, if `f : X → G` and `g` agree on one fibre, then `f = (η ∘ p) · g` for a section `η` of `G`.

The Library obtains the large-level bound from its own rigidity results
(`CanonicalCubicRigidity`, `TorsionConfigurationRigidity`) through the cubic embedding over
fields, as described on the page of `EventualModuliZariskiSheafStatement`.
