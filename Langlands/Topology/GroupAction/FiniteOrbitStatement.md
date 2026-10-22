# Finite orbit ordering for continuous group actions

Worker 112 states `Langlands.Topology.FiniteOrbitOrdering`, an internal
prerequisite for the published `Langlands.Geometric.ClosedSubgroupOrbitOrdering`.
This file defines a proposition and supplies no proof.

The group `H` has a topology making multiplication and inversion continuous and
is sigma compact. It acts continuously on an arbitrary locally compact Hausdorff
space `X`. The group and space have independent universes. If the actual Mathlib
orbit quotient is finite, the conclusion supplies a natural number `n` and points
`r : Fin n → X`. Their actual orbits form a pairwise disjoint cover, and the union
of the first `k` orbits is open for each `k : Fin (n + 1)`. The empty space is
allowed, in which case `n = 0` is possible. Orbit local closedness and an existing
ordering are not premises.

## Provenance and proof obligation

The motivating originals are Bernstein and Zelevinsky, *Representations of the
group GL(n,F) where F is a non-Archimedean local field* (1976), section 1.5,
printed/PDF page 7, and *Induced representations of reductive p-adic groups I*
(1977), section 5.1, printed pages 459–460 (PDF pages 20–21). These passages were
read from the retained originals. Registered source IDs and SHA-256 values are:

- `bernstein-zelevinsky-1976-representations-gln`,
  `72dc22eb9991112936a88327f00d0f02a16a2bf8747518ca0ecfeeadd188e50c`.
- `bernstein-zelevinsky-1977-induced-i`,
  `8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`.

The present formulation is an internal generalization, not a verbatim source
statement. BZ76 assumes an l-group acting on an l-space and proves existence of
an open orbit, together with openness of a suitable orbit map. BZ77 records the
resulting finite ordering. The present statement drops the zero-dimensional and
locally compact group assumptions, and asserts only the finite ordering, not
openness of orbit maps.

A proposed complete proof is to cover each orbit by countably many compact images
of compact subsets of `H`. With finitely many orbits these sets cover `X`. The
Baire theorem gives one compact image with nonempty interior in a nonempty `X`.
Translations move this interior throughout its orbit, making that orbit open.
Remove it and apply the same argument to the closed invariant complement, which
remains locally compact and Hausdorff. Induction on the number of orbits gives
the finite enumeration and open initial unions. This is a proof plan, not a
claimed Lean theorem. A separate proof must implement these steps, including
induction, empty cases, and the exact disjoint cover.

For the intended consumer, `H` is a closed subgroup `Q` of a sigma-compact group,
`X` is the actual quotient `P \\ G` by a closed subgroup, and the action is right
translation by inverse elements. Transferring the quotient topology, identifying
this action's orbits with `cosetOrbit P Q w`, and deriving finiteness from the
actual double-coset quotient remain separate obligations. This prerequisite
makes no assertion about Mackey graded pieces or representations.
