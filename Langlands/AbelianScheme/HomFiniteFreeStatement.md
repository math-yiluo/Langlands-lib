# Finite freeness of actual integral Hom groups

`Langlands.AbelianScheme.HomFiniteFreeStatement.{u}` states that, for every
field `k : Type u` with `IsAlgClosed k` and `CharZero k`, and every pair
`A B : AbelianScheme (Spec (CommRingCat.of k))`, the conclusion is

```lean
Module.Free ℤ (A ⟶ B) ∧ Module.Finite ℤ (A ⟶ B)
```

Here `A ⟶ B` is the actual group of homomorphisms of the underlying commutative
group schemes, as defined in `Langlands.AbelianScheme.Basic`. Its addition is
the existing pointwise group law on homomorphisms. The integer scalar action
is the canonical module structure supplied by that additive commutative group:
an integer acts by repeated addition and additive inversion. No module
structure or basis is supplied as a hypothesis. `Module.Free` asserts existence
of a basis; `Module.Finite` means finite generation as a module, rather than
finiteness of the set of homomorphisms. Together they assert finite freeness.

The objects retain the Library's geometric meaning: actual commutative group
schemes whose structure morphisms are smooth, proper and geometrically
connected. The proposition does not require a chosen relative dimension,
projective embedding, polarization, positivity form, Tate action or
faithfulness theorem. It quantifies over an arbitrary universe `u`; it does
not restrict the field to a chosen algebraic closure or to a subfield of
the complex numbers.

The source is J. S. Milne, *Abelian Varieties*, the 1986 article in the author's
revision dated 2 January 2022, Theorem 12.5, printed/PDF p.21, with its proof on
p.22. Milne works over an arbitrary ground field (see the conventions on p.2).
His theorem states finite freeness of `Hom(A,B)`, bounds its rank by
`4 dim(A) dim(B)`, and asserts injectivity with torsion-free cokernel of its
natural map after tensoring with the prime-adic integers to the Hom group of
Tate modules for primes different from the field characteristic. The Lean
target retains only finite freeness and restricts the field to the
algebraically closed, characteristic-zero case. Neither the rank bound nor
the Tate-module assertion is included. This restriction and omission make
the target a weaker consequence of the source statement.

Source identifier: `milne-abelian-varieties-1986-author-2022`; PDF SHA256:
`bffdf81c57c77420b5454b31270007989d12f332abea62424be15c424079fc7c`.
The registered author errata snapshot
`J. S. Milne - Abelian Varieties (1986 article errata, HTML snapshot 2026-10-25).html`
specifically notes a correction to the proof of Theorem 12.5 and says it is
incorporated in the author's corrected online version. The cited 2022
revision is that corrected version.

This module defines a proposition and supplies no proof or global freeness
instance. It is proved as `homFiniteFree` in
`Langlands.AbelianScheme.HomFiniteFreeProof`.
