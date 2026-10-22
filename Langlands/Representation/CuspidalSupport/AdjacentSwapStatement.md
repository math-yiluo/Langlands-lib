# Adjacent block swaps and factors of cuspidal induction

Authors: Worker 289, using the statement specification supplied by Workers 242
and 34.

This pair states
`Langlands.CuspidalSupport.AdjacentBlockSwapCuspidalInductionFactorsTheorem.{uF,uV,uW}`
as a proposition-valued definition. It supplies a statement target only.

The statement quantifies every prime `p`, actual `PadicField.{uF} p`,
compatible topological realization `T`, and positive rank `n`. After installing
the topology and topological group instances supplied by `T`, it quantifies:

- Two ordered positive block shapes `B C : BlockShape n`, an actual coordinate
  permutation `w : Equiv.Perm (Fin n)`, and
  `hw : ConjugatesLevi (F := F.Carrier) B C w`. Thus conjugation by the
  permutation matrix of `w` takes the whole embedded source Levi onto the target
  Levi.
- A natural block index `j` satisfying `j + 1 < B.length`, with the equation
  `∀ a, (Geometric.blockIndex C (w a) : ℕ) =
  Equiv.swap j (j + 1) (Geometric.blockIndex B a : ℕ)`.
  Block indices are zero-based. This exchanges source blocks `j` and `j + 1`
  and fixes every other block index.
- `Geometric.IsMinimalRepresentative B C w`, meaning that `w` preserves the
  coordinate order within each source block and its inverse preserves the
  coordinate order within each target block.
- Smooth complex representations
  `σ : SmoothRep.{0,uF,uV} ℂ (B.Levi F.Carrier)` and
  `τ : SmoothRep.{0,uF,uW} ℂ (C.Levi F.Carrier)`, each irreducible and
  `IsLeviCuspidal`. Here cuspidality is the existing admissible
  quasicuspidality predicate on the actual product Levi.
- An actual representation equivalence, expressed as
  `Nonempty ((transport B C w hw σ.representation).Equiv τ.representation)`.
  The action of `transport` uses inverse Levi conjugation.

The conclusion is exactly

```lean
HaveSameJordanHolderFactors
  (Rep.of (T.normalizedParabolicInduced B σ.representation))
  (Rep.of (T.normalizedParabolicInduced C τ.representation))
```

The canonical normalized induction uses the standard upper block parabolic,
its positive half-modulus and right translation. The factor-matching predicate
asserts existence of actual finite composition series, irreducibility of their
graded representations, and a permutation matching the graded representations
by actual equivalences. Repeated factors retain their multiplicities.
There is no added finite-length or existence-of-series hypothesis. The field
universe `uF` and the two inducing carrier universes `uV`, `uW` are independent.

## Original source and scope

I. N. Bernstein and A. V. Zelevinsky, *Induced representations of reductive
p-adic groups I*, Annales scientifiques de l'École Normale Supérieure (4),
10 (1977), 441–472, §2.16(2) and §2.17, printed page 450 (PDF page 11).
Literature ID: `bernstein-zelevinsky-1977-induced-i`.
Retained source:
`/home/taskhub/central-library/Bernstein-Zelevinsky--Induced representations of reductive p-adic groups I--1977.pdf`.
SHA-256: `8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`.
PDF pages 9–11 were read directly on 2026-10-22, including Theorem 2.9(a)(iii)
and the two-step argument of §2.16.

Section 2.16(2) obtains equality of Jordan–Hölder factors for data related by
an elementary map, using the preceding two-block step and induction
transitivity and exactness. Section 2.17 factors an associating Weyl map
into elementary maps and identifies an elementary map for general linear
groups with a transposition of neighbouring cells. This pair expresses that
adjacent-step specialization using the existing actual permutation, Levi
transport, normalized induction and factor predicates. Replacing the exact
transport by an isomorphic representation `τ` is the isomorphism-invariant
form of the source's assertion.

The explicit minimality, adjacency, and target irreducibility and cuspidality
hypotheses are inputs to this step. They are to be supplied by the
arbitrary-rank reduction to adjacent swaps; this pair does not establish
those inputs or the decomposition into swaps. The reduction can compose the
resulting factor matchings by transitivity. The statement permits arbitrary
block count and does not impose `B.length = 2`. Its proof, including the
induction-in-stages passage from the two-block case, is a separate obligation.
