# Factoriality of the coordinate ring of a split simply connected group

This module contains one Prop-valued definition,
`SplitSimplyConnectedFactorialStatement.{u}`. It proves nothing.

## The Lean statement

The statement quantifies over every field `k : Type u` and every group scheme
`G` over `Spec k` such that

- `IsSimplyConnected G` holds: `G` is semisimple, and every central isogeny
  `H ⟶ G` from a semisimple group `H` over `k` is an isomorphism (see
  `SimplyConnected/Basic.md`); and
- `HasSplitMaximalTorus G` holds: some maximal torus `i : T ⟶ G` has split
  source `T` (see `Torus/FiniteGaloisSplitMaximal.lean`).

It asserts two facts about the ring `Γ(G.X.left, ⊤)` of global sections of the
scheme underlying `G`:

1. `IsDomain Γ(G.X.left, ⊤)`: the ring is an integral domain;
2. `UniqueFactorizationMonoid Γ(G.X.left, ⊤)`: every nonzero element factors
   into irreducibles, uniquely up to order and units.

Mathlib's `UniqueFactorizationMonoid R` takes the ring's existing
`CommMonoidWithZero R` structure and needs no domain instance. The class
extends `IsCancelMulZero`, so the second conjunct already includes
cancellation. The first conjunct adds that the ring is nontrivial. Together
the two conjuncts say exactly that `Γ(G.X.left, ⊤)` is a unique factorization
domain.

A semisimple group over a field is affine (`IsConnectedReductive.isAffineHom`),
so `Γ(G.X.left, ⊤)` is its coordinate ring `k[G]` and `G.X.left ≅ Spec k[G]`.
The statement has no assumption on characteristic, perfectness or the size of
the universe `u`.

## Sources

Provenance: derived. The statement is a classical theorem. Over algebraically
closed fields it appears verbatim in Popov. Over an arbitrary field, for split
groups, it follows from Milne's Picard-triviality theorem by a standard
commutative-algebra argument, given below.

**Popov 1974.** V. L. Popov, *Picard groups of homogeneous spaces of linear
algebraic groups and one-dimensional homogeneous vector bundles*, Izv. Akad.
Nauk SSSR Ser. Mat. 38:2 (1974), 294–322. It is registered as
`popov-1974-picard-groups-homogeneous-spaces-ru`, SHA-256
`bb3f5116ac2c1968a4249cfb27ccaad262e59391e58113aa809050d258bc6dc7`. The
Introduction, printed p. 296 (PDF p. 3), states two results:

- Proposition 1: the Picard group of a simply connected semisimple algebraic
  group is trivial.
- Its Corollary: in the ring of regular functions on a simply connected
  semisimple algebraic group, factorization into primes is unique.

The proof of Proposition 1 is at the end of §1. Popov works over an
algebraically closed field `k` of arbitrary characteristic. There, every
semisimple group is split. Popov uses the usual notion of a simply connected
semisimple group: its universal covering, from the Chevalley seminar that he
cites in the Remark after Theorem 3 on the same page, is an isomorphism.
Milne, *Algebraic Groups* (2017), Proposition 19.15 and the sentence after it
(printed p. 401, PDF p. 417), identifies this usual notion with the
central-isogeny formulation used by `IsSimplyConnected`. So over an
algebraically closed field the Lean statement is Popov's Corollary.

**Milne 2017.** James S. Milne, *Algebraic Groups* (2017), is registered as
`milne-2017-algebraic-groups`, SHA-256
`899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`. Section 18d
assumes a split connected group variety `G` over an arbitrary field. Corollary
18.24, printed p. 393 (PDF p. 409), states that `Pic(G) = 0` when `G` is
simply connected. A semisimple group with a split maximal torus is a split
connected group variety (Proposition 21.64, as recorded in
`SplitPicardInputsStatement.md`). The registered errata snapshot
`milne-2017-algebraic-groups-errata-2026-11-02` (SHA-256
`a0c3a10dc376e1c9bd1de05b33beaf7d54e5f1ea7b408d594cfd70231a7ba0cf`) has no
correction to 18.22, 18.24, 19.15, A.78 or A.79. Its Chapter 18 entries
concern 18.4, Exercise 18-1 and 18.8 only.

**From `Pic(G) = 0` to factoriality.** Let `A = k[G]`.

- `G` is smooth and connected, hence integral, so `A` is a Noetherian integral
  domain of finite type over `k`.
- `A` is regular because `G` is smooth. A regular local ring is a unique
  factorization domain (Auslander–Buchsbaum). So every height-one prime `p` of
  `A` is locally principal, which makes `p` an invertible ideal.
- Invertible sheaves on `Spec A` correspond to finitely generated projective
  `A`-modules of rank one (Milne A.79, printed p. 584, PDF p. 600). Since
  `Pic(G) = 0`, the module `p` is free of rank one, so `p` is principal.
- A Noetherian domain whose height-one primes are all principal is a unique
  factorization domain. In Mathlib this is
  `UniqueFactorizationMonoid.iff_forall_isPrincipal_of_height_eq_one`
  (Stacks 0AFT).

Milne A.78 (same page) records the related fact that the Picard group of a
smooth variety equals its Weil divisor class group. The converse direction,
from unique factorization to `Pic = 0`, is Milne A.79 and is not needed here.

## Intended use

Factoriality gives `Pic(Γ(G.X.left, ⊤)) = 0` (Mathlib instance for GCD
domains in `RingTheory/PicardGroup.lean`). Through
`Picard/AffineLineBundlePicard`, every line bundle on the affine scheme
`G.X.left` is then trivial. Combined with the published simply connected
cover `splitSimplyConnectedCoverExistence`, this reduces
`SplitSemisimplePicardTrivialCoverStatement` to the present statement. This
paragraph describes intended use only; no reduction is proved here.
