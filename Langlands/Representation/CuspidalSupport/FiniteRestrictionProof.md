# Finite irreducible restriction to a determinant-unit product Levi

`Langlands.CuspidalSupport.leviFiniteRestrictionTheorem` proves exactly the
published proposition `Langlands.CuspidalSupport.LeviFiniteRestrictionTheorem`
from `Langlands.Representation.CuspidalSupport.FiniteRestrictionStatement`.
The field universe `uF` and representation-carrier universe `uV` remain
independent.

For any prime `p`, `p`-adic field `F`, compatible topological data `T`, rank
`n`, block shape `B`, and irreducible smooth complex representation `D` of
`B.Levi F.Carrier`, the actual restriction
`determinantUnitRestriction T B D.representation` is semisimple and has a
finite spanning family of irreducible subrepresentations. The rank may be
zero. No cuspidality, admissibility, central character, finite dimension, or
finite length is assumed. The sum of the irreducible subrepresentations is
not asserted to be direct.

## Implemented proof

The proof introduces `p`, its prime instance, `F`, `T`, `n`, and `B` from the
published proposition. It then applies the already published theorem
`Langlands.CuspidalSupport.FiniteRestriction.leviFiniteRestriction F T B`
from `Langlands.Representation.CuspidalSupport.DeterminantUnitFiniteRestriction`.
That theorem has exactly the remaining type, including the local installation
of `T.topology`, the quantification over `D`, and both conclusions. Its
unrestricted natural rank also handles rank zero. This module supplies the
quantifier assembly for the named proposition; the imported theorem supplies
the mathematical argument. The statement and all imported files are unchanged.

The imported proof first obtains scalar central action from smoothness,
irreducibility, and the countable-rank Schur theorem, using the product-Levi
Cartan decomposition to bound the rank. It combines the finite index of the
determinant-unit subgroup joined with the centre with the generic finite-index
restriction theorem to obtain semisimplicity and the finite spanning family.

## Provenance

This is the reduced spanning consequence of I. N. Bernshtein and
A. V. Zelevinskii, *Representations of the group GL(n,F) where F is a
non-Archimedean local field*, Russian Mathematical Surveys 31:3 (1976),
1–68, English translation, Lemma 3.26, printed/PDF p.36. Registered source:
`bernstein-zelevinsky-1976-representations-gln`, retained PDF SHA256
`72dc22eb9991112936a88327f00d0f02a16a2bf8747518ca0ecfeeadd188e50c`.
The source treats positive ranks; the imported Lean theorem also proves the
empty-product case uniformly. The source's direct-sum conclusion implies the
semisimplicity and finite spanning conclusions recorded by the target.

Worker 276 supplied the adapter proof route and term in the task context.
Worker 418 checked the current published declarations and prepared this module.
