# Fixed-vector detection and fixed-vector dimension descent

Authors: Worker 260, from the interface designed by Worker 196. This file
defines seven propositions. It proves none of them and assumes no theorem as
data.

The six clauses are the public lemmas of Worker 196's draft module
`Langlands.Representation.Smooth.FixedVectors.Detection`, in public draft
revision 4 of task `fe734e49-26a6-457a-89e8-3b8e66d5cd39`. Each clause keeps the
draft lemma's hypotheses and scope. After the type and instance parameters,
its objects and hypotheses come in the draft lemma's order. The bundle
`Langlands.FixedVectorDetectionDescentStatement.{uR, uG, uV, uW}` is the
conjunction of the six clauses, in the order below.

## Terms used

All terms are the published ones; nothing is redefined here.

- `fixedVectors ρ K` (`Smooth/Definitions`) is the submodule of vectors fixed
  by every element of the subgroup `K`.
- `fixedVectorsMap f K` (`Smooth/FixedVectors/Definitions`) is the restriction
  of an intertwiner `f` to a linear map between the `K`-fixed submodules.
- `SmoothRep.{uR, uG, uV} R G` (`Category/Basic`) is the full subcategory of
  Mathlib's `Rep` on smooth representations. A morphism `f : A ⟶ B` has
  underlying intertwiner `SmoothRep.hom f`.
- `SmoothRep.kernel f`, `SmoothRep.image f` and `SmoothRep.cokernel f`
  (`Category/Subquotients`) are the actual invariant kernel, the actual
  invariant image inside the target, and the actual module quotient of the
  target by that image. Each carries the restricted or descended action.
- `Representation.IsSemisimpleRepresentation ρ` is Mathlib's
  `ComplementedLattice (Subrepresentation ρ)`: every subrepresentation has a
  complement.
- `IsAtom S` for `S : Subrepresentation ρ` means `S` is nonzero and has no
  subrepresentation strictly between `⊥` and `S`. These are the simple
  subrepresentations.
- `Module.finrank` is Mathlib's finite rank. Each clause that uses it also
  assumes that the ambient `K`-fixed space is finite dimensional.

## The six clauses

1. `Langlands.FixedVectorsGenerateSemisimpleStatement.{uR, uG, uV}`. Take any
   field `R`, any group `G`, any `R`-module `V`, any representation `ρ` of `G`
   on `V`, and any subgroup `K`. Assume `ρ` is semisimple. Assume also that
   every atom `S` of `Subrepresentation ρ` contains a vector `v ≠ 0` with
   `v ∈ fixedVectors ρ K`. Then every `T : Subrepresentation ρ` with
   `fixedVectors ρ K ≤ T.toSubmodule` equals `⊤`. So the `K`-fixed vectors
   generate `ρ`.

2. `Langlands.FixedVectorsDetectIntertwinerStatement.{uR, uG, uV, uW}`. Take any
   field `R`, any group `G`, and any two representations `ρ` on `V` and `σ` on
   `W`, with `V` and `W` in independent universes. Take any subgroup `K` such
   that every `S : Subrepresentation ρ` with `fixedVectors ρ K ≤ S.toSubmodule`
   equals `⊤`. Then every intertwiner `f : ρ.IntertwiningMap σ` with
   `fixedVectorsMap f K = 0` is `0`.

3. `Langlands.SmoothRep.FixedVectorsKernelFinrankLtStatement.{uR, uG, uV}`.
   Take any field `R`, any group `G` with any topology, any `A : SmoothRep R G`,
   and any subgroup `K` such that `fixedVectors A.representation K` is finite
   dimensional over `R`. Let `f : A ⟶ A` with
   `fixedVectorsMap (hom f) K ≠ 0`. Then the finite rank of the `K`-fixed
   vectors of `SmoothRep.kernel f` is strictly less than that of `A`.

4. `Langlands.SmoothRep.FixedVectorsImageFinrankLtStatement.{uG, uV}`. Take any
   topological group `G`, any `A : SmoothRep ℂ G`, and any open subgroup `K`
   with `IsCompact (K : Set G)`. Assume the `K`-fixed space of `A` is finite
   dimensional over `ℂ`. Let `f : A ⟶ A` such that
   `fixedVectorsMap (hom f) K.toSubgroup` is not injective. Then the finite
   rank of the `K`-fixed vectors of `SmoothRep.image f` is strictly less than
   that of `A`.

5. `Langlands.SmoothRep.FixedVectorsCokernelFinrankLtStatement.{uG, uV}`. Use
   the same setting as clause 4. Let `f : A ⟶ A` with
   `fixedVectorsMap (hom f) K.toSubgroup ≠ 0`. Then the finite rank of the
   `K`-fixed vectors of `SmoothRep.cokernel f` is strictly less than that of
   `A`.

6. `Langlands.SmoothRep.FixedVectorsSubquotientWitnessStatement.{uG, uV}`. Take
   any topological group `G`, any `A C D : SmoothRep ℂ G`, and any open
   subgroup `K` with `IsCompact (K : Set G)`. Assume the `K`-fixed space of `A`
   is finite dimensional and the `K`-fixed space of `D` is `Nontrivial`, that
   is, nonzero. Let `i : C ⟶ A` and `q : C ⟶ D` be morphisms. Assume
   `hom i` is injective and `hom q` is surjective. Let `fA : A ⟶ A` and
   `fC : C ⟶ C` satisfy `(hom i).comp (hom fC) = (hom fA).comp (hom i)` and
   `(hom q).comp (hom fC) = 0`. Then
   `fixedVectorsMap (hom fA) K.toSubgroup` is not injective.

## Scope

- No representation carrier is assumed finite dimensional. In clauses 3-6,
  only the `K`-fixed space of the ambient `A` is. No admissibility, finite
  length or finite generation is assumed.
- Clauses 1 and 2 are purely algebraic. They use no topology and no
  smoothness, and `K` is an arbitrary subgroup.
- Clause 3 holds over any field, for any topology on `G` and any subgroup `K`.
  It does not assume a topological group or a compact open `K`.
- Clauses 4-6 use exactly complex coefficients, a topological group, and a
  compact open subgroup. This matches the published averaging theorem
  `Langlands.Compact.FixedVectorSurjectivity`, which the intended proofs use
  for surjectivity onto fixed vectors.
- Clause 6 assumes no irreducibility, semisimplicity or cuspidality of any of
  `A`, `C` or `D`. It does not assume that `D` is a subquotient through the
  published `SmoothRep.IsSubquotient`. The maps `i` and `q` and their
  injectivity and surjectivity are the only presentation data.
- In clause 1 the semisimplicity hypothesis is an instance binder inside the
  proposition. Atoms are quantified inside the proposition. Nothing asserts
  that a subgroup with the atom hypothesis exists.

## Universes

Each clause quantifies its field, group and carriers inside the proposition,
at universe parameters of the definition. The coefficient universe `uR`, the
group universe `uG`, and the carrier universes `uV` and `uW` are independent.
Clause 2 has two independent carrier universes. In clauses 3-6 all smooth
representations lie in one category `SmoothRep.{uR, uG, uV}`, or
`SmoothRep.{0, uG, uV}` over `ℂ`. Morphisms of a category need a common carrier
universe. The bundle instantiates every clause at the shared parameters
`uR, uG, uV, uW`. A universe-polymorphic proof of the bundle therefore gives
every clause at every universe.

## Provenance

These are internal algebraic statements, not literature theorems. Worker 196
isolated them as inputs to the induction in Bernstein and Zelevinsky,
*Representations of the group GL(n,F) where F is a non-Archimedean local
field*, Russian Math. Surveys 31:3 (1976), Proposition 3.30, printed page 37
(PDF page 37). Registered source
`bernstein-zelevinsky-1976-representations-gln`, SHA-256
`72dc22eb9991112936a88327f00d0f02a16a2bf8747518ca0ecfeeadd188e50c`. Worker 260
read the statement and proof of 3.30 in this registered original.

Step (3) of that proof uses induction on `dim E^N`. It takes the nonzero
operator `A = π(z) − θ(z)`, which commutes with `G`. It uses the hypothesis
that `V^N` is a subfactor of `E^N` to see that `A` is not invertible on
`E^N`. Then it passes to `Ker A`, `Im A` and `E/Im A`, whose `N`-fixed spaces
have smaller dimension. Clauses 3, 4 and 5 state these dimension drops for the
actual kernel, image and cokernel. Clause 6 isolates the noninvertibility
step. Here `D` plays the role of `V`, and `fA` and `fC` play the role of the
operator on `E` and on the subrepresentation that maps onto `V`. Clauses 1
and 2 state when fixed vectors generate a semisimple representation and when
fixed vectors detect zero intertwiners. The source does not state these
general interfaces verbatim. The more general scope above (arbitrary groups,
fields or topologies where the argument allows) is deliberate and is explained
in the Scope section.

No proof is shipped here. Worker 196's draft lemmas inhabit each clause
exactly. A private development check by Worker 260 assigned each unapplied
draft lemma to its clause, and the six lemmas to the bundle. The check is
not a Library proof. The exact-target proof will be a separate submission.

## Dependencies

Project imports:

- `Langlands.Representation.Smooth.FixedVectors.Definitions`, which supplies
  `fixedVectors` through `Smooth/Definitions`, and supplies `fixedVectorsMap`.
- `Langlands.Representation.Category.Subquotients`, which supplies `SmoothRep`,
  `SmoothRep.hom`, and the actual `kernel`, `image` and `cokernel`.

Mathlib imports: `Mathlib.RepresentationTheory.Semisimple`,
`Mathlib.LinearAlgebra.FiniteDimensional.Defs` and
`Mathlib.Basic.Complex.Basic`. No published pair is modified. Lean service
environment `3b864ddf-f0af-4c18-8903-c6f813a0ce0f` (Lean 4.34.0, Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`).
