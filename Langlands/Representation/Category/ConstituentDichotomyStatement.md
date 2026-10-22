# Irreducible subquotients across an invariant subspace

Author: Worker 220. This file states a proposition; it proves nothing and
assumes no theorem as data.

`Langlands.SmoothRep.IrreducibleSubquotientDichotomy` quantifies over:

- every field `R` in universe `uR`;
- every group `G` in universe `uG`, with any topology;
- smooth representations `A` and `D` in the published category
  `SmoothRep.{uR, uG, uV} R G`;
- every actual invariant subspace `S : Subrepresentation A.representation`.

The three universes are independent. Suppose `D.IsIrreducible` and
`SmoothRep.IsSubquotient D A`. Then the statement says that
`SmoothRep.IsSubquotient D (SmoothRep.subrepresentation A S)` or
`SmoothRep.IsSubquotient D (SmoothRep.quotient A S)` holds.

## Exact meaning of the terms

- `SmoothRep.IsIrreducible` is Mathlib's `Representation.IsIrreducible` for
  the underlying action. This means the lattice of invariant submodules is
  simple, so `D` is nonzero. Finite dimension is not required.
- `SmoothRep.IsSubquotient B A` from `Category/Subquotients` requires an
  actual invariant submodule of `A`, an actual invariant submodule of that
  subrepresentation, and an isomorphism in the smooth category from `B` to
  the resulting module quotient.
- `SmoothRep.subrepresentation A S` is the restriction of the action to `S`.
- `SmoothRep.quotient A S` is the actual module quotient `A/S` with the
  descended action.

Both constructions are the published ones; nothing is redefined here.
There is no hypothesis of admissibility, finite dimension, finite length,
local compactness, a central character, or any further structure on the
group. The topology on `G` only determines which representations are smooth.

## Provenance

This is an internal, elementary algebraic statement, not a literature
assertion. The coefficients are restricted to fields because the published
`SmoothRep.IsIrreducible` in `Category/Basic` is defined over a field. The
smooth category is closed under the subrepresentations and quotients used.
The intended proof uses only irreducibility and the accepted characterization
`Langlands.SmoothRep.isSubquotient_iff_exists` in
`Classification/SupercuspidalSupport`:

1. Write `D` as a quotient of a representation `C` that embeds in `A`.
2. Let `K` be the inverse image of `S` in `C`.
3. The composite `K → C → D` is surjective or zero, because `D` is
   irreducible.
4. If it is surjective, `K` embeds in `S` and maps onto `D`.
5. If it is zero, the map `C → D` factors through `C/K`. The space `C/K`
   embeds in `A/S` and maps onto `D`.

This route is an explanation of the statement, not a proof shipped with it.
The proof is a separate task.

## Use in BZ76 Proposition 3.30

Bernstein and Zelevinsky, *Representations of the group GL(n,F) where F is a
non-Archimedean local field*, Russian Math. Surveys 31:3 (1976), Proposition
3.30, printed page 37 (PDF page 37). Registered source
`bernstein-zelevinsky-1976-representations-gln`, SHA-256
`72dc22eb9991112936a88327f00d0f02a16a2bf8747518ca0ecfeeadd188e50c`. Worker 220
read the statement and proof of 3.30 in the registered original.

The proposition says that an irreducible cuspidal subquotient `V` of an
admissible `E` is isomorphic to a submodule and to a factor module of `E`.
Step (3) of the proof uses induction on the dimension of the fixed vectors
`E^N`. It takes a nonzero, non-invertible intertwiner `A = π(z) − θ(z)`. It sets
`E' = Ker A` and `E'' = Im A ≅ E/E'`, and asserts that `V` is a subfactor of
`E'` or of `E''`. It then argues similarly with `E''` and `E/E''`, which is the
cokernel, for the factor-module half.

For an intertwiner `f : A ⟶ B`, both alternatives follow from this statement:

- Take `S` to be the kernel of `f`. Then the actual quotient by the kernel is
  isomorphic to the image `SmoothRep.image f`. The subquotient relation is
  invariant under isomorphism, so the image occurs as one of the two options.
  This gives the kernel/image alternative.
- Take `S` to be the image of `f` inside `B`. Then the quotient is exactly
  `SmoothRep.cokernel f`. This gives the image/cokernel alternative.

The present statement only isolates this algebraic step. It does not state or
replace Proposition 3.30, the published `LeviCuspidalConstituentTheorem`, or
any cuspidality, admissibility or semisimplicity result.

## Dependencies

The only import is `Langlands.Representation.Category.Subquotients`, which
in turn imports `Category/Basic` for `SmoothRep` and `SmoothRep.IsIrreducible`.
No published pair is modified. Lean service environment
`3b864ddf-f0af-4c18-8903-c6f813a0ce0f` (Lean 4.34.0, Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`).
