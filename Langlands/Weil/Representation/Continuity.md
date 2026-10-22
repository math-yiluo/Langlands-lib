# Continuity and inertia kernels

`Langlands.Weil.RepresentationContinuity` is a proposition target about actual
finite-dimensional complex representations `Representation ℂ W V`. The group
`W` is a topological group, and `I` is an open subgroup, with its inherited
topology, assumed compact and nonarchimedean. Here nonarchimedean means that
every identity neighborhood contains an open subgroup. The two universes of
`W` and `V` are independent. The zero-dimensional representation is allowed.

The representation space is a finite-dimensional normed complex vector space.
Every linear action operator is continuous. The first continuity condition
uses the usual operator-norm topology on continuous linear endomorphisms.
Since every action operator is invertible and dimension is finite, this is the
usual complex topology used for a representation into `GL(V)`. Choosing a norm
does not select a new mathematical notion of continuity: all norms on a
finite-dimensional complex vector space give the same topology.

The declaration asserts five equivalences:

1. Operator continuity is equivalent to continuity of every orbit map.
2. Operator continuity is equivalent to joint continuity of the action on
   `W × V`.
3. Operator continuity is equivalent to openness of the kernel on `I`, measured
   in the inherited topology on `I`.
4. Operator continuity is equivalent to openness of the whole kernel in `W`.
5. The inertia kernel is open if and only if its image is finite and its kernel
   is closed in `I`.

In particular a continuous representation has finite inertia image. The
closed-kernel condition in the converse is intentional. An arbitrary
homomorphism from a profinite group to a finite group need not be continuous;
finite image by itself cannot replace open kernel. Compactness gives finiteness
of the quotient by an open subgroup. Finiteness of the image and closedness of
the kernel give openness because the complement of the kernel is a finite
union of closed cosets.

No surjective degree map, Frobenius lift, irreducibility, unitarity, or finite
image of the whole representation is required. No normality of `I` is required
for this topological fact. It is therefore applicable to the inertia subgroup
of a constructed local Weil group once that subgroup's compact,
nonarchimedean and open properties have been established. It neither
constructs that local Weil group nor proves its identification with a Galois
pullback.

## Original-source correspondence

| Declaration and clauses | Original locator | Correspondence |
| --- | --- | --- |
| `RepresentationContinuity`, clauses 1 and 2 | Tate, section 2 opening, printed p. 9, retained PDF p. 18 | The source uses continuous homomorphisms into `GL(V)` for finite-dimensional complex `V`. The orbit-map and joint-action formulations are elementary finite-dimensional reformulations, stated explicitly here. |
| `RepresentationContinuity`, clauses 3 and 4 | Henniart 1980, sections 2.1 and 2.5, printed pp. 158-159, PDF pp. 5-6; Tate, section 2.1, printed p. 9, PDF p. 18; section 4.1.2(a), printed p. 20, PDF p. 29 | Henniart uses the open inherited inertia topology and observes that continuity forces triviality on an open subgroup of inertia. Tate explains the absence of small subgroups in `GL(V)` and defines the Weil part of a WD representation by an open inertia kernel. The declaration isolates the general topological hypotheses behind this bridge. |
| `RepresentationContinuity`, clause 5 | Henniart 1980, section 2.5, printed p. 159, PDF p. 6 | The source passes from an open inertia kernel to a finite inertia quotient. The converse with a closed kernel is an explicitly derived topological supplement, not a quoted assertion that finite image alone suffices. |

The no-small-subgroups argument in the originals is about the full
finite-dimensional general linear group. This target is not a restatement of
the existing scalar-character open-kernel theorem.

- Guy Henniart, *Representations du groupe de Weil d'un corps local*,
  L'Enseignement Mathematique (2) 26 (1980), 155-172.
  Literature ID `henniart-1980-weil-representations`.
  SHA-256 `451a8bd31a58be9bf5ce49588503c2d229b1a73bf3e65ae0c7b2f491c1c4e017`.
  Retained original:
  `C:/Central-Library/Henniart--Representations du groupe de Weil dun corps local--1980.pdf`.
- John Tate, *Number theoretic background*, in *Automorphic Forms,
  Representations and L-Functions*, Proc. Sympos. Pure Math. 33, Part II
  (1979), 3-26.
  Literature ID `tate-1979-number-theoretic-background`.
  SHA-256 `c890894fe19783890cc4def2c5bf92a18d71619acf8ba7005aefce4984fe70d6`.
  Retained original:
  `C:/Central-Library/Borel-Casselman--Automorphic Forms, Representations and L-Functions (Corvallis)--1979/Part II.pdf`.

## Dependencies and status

There are no project mathematical imports. The declaration uses the actual
Mathlib `Representation`, restriction by `MonoidHom.comp`, `MonoidHom.ker`,
`OpenSubgroup`, `NonarchimedeanGroup`, `CompactSpace`, `FiniteDimensional`, and
`LinearMap.toContinuousLinearMap` interfaces in environment
`2ecc41bc-2901-4e34-96c5-6d98fbb3c74d` version 1: Lean 4.34.0,
Mathlib commit `5ed2965256430c3649e86755f9576b54eca72435`.

The existing generic Weil pullback, inertia topology, and character-twist
artifacts are not redefined. This proposition is independent of their proofs;
later specialization must reuse their exact accepted interfaces and supply the
additional compactness and nonarchimedean hypotheses. This file contains a
statement definition, not a proof of the five equivalences.
