# Finite irreducible restriction to the determinant-unit subgroup

`Langlands.CuspidalSupport.LeviFiniteRestrictionTheorem` is a
proposition definition, not a proof. It records the reduced spanning
consequence of Bernstein–Zelevinsky (1976), Lemma 3.26.

## Mathematical statement and Lean correspondence

For every prime `p`, actual `PadicField F`, compatible topological data `T`,
natural rank `n`, and block shape `B`, put `G = B.Levi F.Carrier`, the
product of the general linear groups of the blocks of `B`, and
`H = determinantUnitSubgroup T B`. The declaration explicitly installs
`T.topology` with `letI`. The field universe `uF` and the
representation-carrier universe `uV` are independent universe parameters
of the definition.

Let `D : SmoothRep.{0, uF, uV} ℂ G` be an actual smooth complex
representation of `G`. The only hypothesis is `D.IsIrreducible`, which is
Mathlib's `Representation.IsIrreducible D.representation`: the lattice of
invariant subspaces is simple, so the carrier is nonzero and has no
invariant subspaces other than `0` and the whole carrier. Nothing else is
assumed: no cuspidality, admissibility, central character, finite
dimension, finite length, finite index of `H` in `G`, and no candidate
family or other witness.

Put `ρD = determinantUnitRestriction T B D.representation`. This is the
published restriction of the actual action along the inclusion of `H`,
on the same carrier as `D`. The conclusion says:

1. `Representation.IsSemisimpleRepresentation ρD`: every invariant
   subspace of the restricted action has an invariant complement.
2. There exist a natural number `m` and actual subrepresentations
   `V i : Subrepresentation ρD`, indexed by `Fin m`, such that every
   `(V i).toRepresentation` is irreducible and
   `(⨆ i, (V i).toSubmodule) = ⊤`. Thus finitely many irreducible
   `H`-invariant subspaces together span the whole carrier of `D`.

“Finite” refers only to the number `m` of subspaces in the family. Neither
the carrier of `D` nor any `V i` is required to be finite dimensional.
The family need not be pairwise nonisomorphic, and the sum is not asserted
to be direct. No positivity hypothesis on `m` is needed: the carrier of an
irreducible `D` is nonzero, so the spanning equation excludes `m = 0`.

## Original source and reduced conclusion

The source is I. N. Bernshtein and A. V. Zelevinskii,
*Representations of the group GL(n,F) where F is a non-Archimedean local
field*, Russian Mathematical Surveys 31:3 (1976), 1–68, English
translation. Registered source:
`bernstein-zelevinsky-1976-representations-gln`. The retained PDF has
SHA256 `72dc22eb9991112936a88327f00d0f02a16a2bf8747518ca0ecfeeadd188e50c`.
Printed and PDF page numbers coincide.

Section 3.20, p.34, defines `G°` for `G = G_α`, `α = (n_1, ..., n_r)`, as
the product of the subgroups `{g ∈ G_{n_i} | det g ∈ R*}`. Here `R*` is the
group of units of the ring of integers. This is the published
`determinantUnitSubgroup T B`: its members are the elements whose block
determinants have normalized absolute value one. Lemma 3.26, p.36, says:
if `(π, G, E)` is an irreducible representation in `Alg G`, that is, an
irreducible smooth representation, then `π|G°` is the direct sum of
finitely many irreducible representations. A direct sum of finitely many
irreducible subrepresentations is semisimple, and its summands form a
finite spanning family of irreducible subrepresentations. Item 1 and
item 2 above record exactly these two consequences. The present statement
does not assert that the sum is direct.

The source proof uses three ingredients, none of which is a hypothesis
of the Lean proposition:

- Lemma 2.9(b), p.17 (restriction to a normal subgroup of finite index):
  the restriction of an irreducible representation to a normal subgroup
  `H` of finite index is a direct sum of at most `|G/H|` irreducible
  representations.
- Property 3.20(b), p.34: `G°` is an open normal subgroup of `G`, and
  `G/G°·Z` is finite, where `Z` is the centre of `G`. With 2.9(b), this
  decomposes `E` into finitely many irreducible `G°·Z`-modules.
- Schur's lemma, Proposition 2.11, p.18, for `l`-groups countable at
  infinity: the endomorphisms of an irreducible smooth representation are
  scalars. Hence every central `π(z)` is scalar, and the irreducible
  `G°·Z`-modules are already irreducible `G°`-modules.

The scalar central action is thus a consequence of irreducibility, not an
additional hypothesis. The general admissibility theorem 3.25 on the same
page is proved using Lemma 3.26, so it is not a prerequisite of this
statement. When `B` has at least one block, `G°` itself does not have
finite index in `G`: the valuation of one block determinant maps `G/G°`
onto `ℤ`. Only `G°·Z` has finite index, which is why the centre enters.

The published statement `Langlands.CuspidalSupport.LeviCuspidalBlockIsolationTheorem`
contains the same two clauses for irreducible cuspidal `D`. The present
proposition has the stronger scope of Lemma 3.26 itself, with irreducibility
as the only hypothesis.

## Rank zero

The quantifier over `n` includes zero. This is an elementary
empty-product extension of the source, which treats positive ranks.
Block sizes are positive, so a rank-zero block shape has no blocks. Then
`G` is an empty product and therefore trivial, and so is `H`. Every
subspace is invariant under a trivial group, so an irreducible complex
representation `D` of the trivial group has a one-dimensional carrier, and
its restriction `ρD` is irreducible. It is semisimple, and `m = 1` with
`V 0 = ⊤` is a spanning family. This paragraph explains why the extension
is reasonable; it does not assert a Lean proof.

## Scope

The module defines only this proposition. It imports the published
determinant-unit subgroup, its actual restriction construction, and the
smooth-representation category without changing their Lean or Markdown
files. It does not import or restate any proof. The internal module
`Langlands.Representation.CuspidalSupport.DeterminantUnitFiniteRestriction`
contains a theorem, `FiniteRestriction.leviFiniteRestriction F T B`, whose
displayed conclusion has the same form for fixed `p`, `F`, `T`, `n` and `B`;
a proof of the present target is separate work.
