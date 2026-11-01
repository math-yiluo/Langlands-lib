# Renard C.I: actual simultaneous generalized eigenspace blocks

This pair exposes the actual subspaces, original restricted actions
and scalar-subtracted generators used in David Renard,
*Représentations des groupes réductifs p-adiques*, French edition dated
9 July 2026, Appendix C.I, printed p.275 / one-based PDF281.
The construction covers the opening reduction to commuting nilpotent
generators. It supplies short intrinsic compatibility laws; independence,
finite support, spanning, dimension assembly and the reduction theorem
remain separate statement and proof obligations.

The governing registered original is
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`,
at
`/home/taskhub/central-library/Renard--Representations des groupes reductifs p-adiques (2026 version)--2026.pdf`.
Worker 709 read PDF281–282 and visually checked PDF281, including
the successive characteristic-space refinements and replacement
of each restricted generator by its nilpotent part. The supplementary
source `renard-2010-corrections-complements`, SHA256
`fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`,
was read on PDF18–19. The 2026 original governs this reduction.
Worker 1044 reread the text of PDF281–282 before staging this pair.

## Actual spaces and actions

All new declarations are in `Langlands.Renard.CommutingReduction`.
The carrier `V : Type u` is an arbitrary complex module, with
`AddCommGroup V` and `Module ℂ V`. A tuple
`a : Fin l → Module.End ℂ V` has any natural length. No invertibility
or original nilpotence is assumed.

For a tuple of complex eigenvalues `χ : Fin l → ℂ`,
`jointSpace a χ` is the actual complex submodule

```text
⨅ i, (a i).maxGenEigenspace (χ i).
```

Mathlib's `maxGenEigenspace` is the union of the kernels of the
powers of the corresponding scalar-subtracted operator.
In the source's finite-dimensional setting, the nonzero blocks of the
successive refinement by the characteristic subspaces of the source's
`a₁, …, a_l` (the Lean entries `a i` for `i : Fin l`) are exactly the nonzero intersections above, since each refinement step
intersects with the next generator's characteristic subspace. This
identification is explanatory provenance; the Lean definition is the
intersection itself, formed from the original endomorphisms rather than
a supplied family of subspaces.
`jointBlockIndex a` is precisely the subtype of `χ` for which
this actual submodule is not bottom. The definition asserts no
finiteness, independence or spanning property.

Assume `hcomm : ∀ i j, Commute (a i) (a j)` for the action
constructions. The imported `NilpotentFiltration.generatedAlgebra a`
is the actual unital algebra `R = Algebra.adjoin ℂ (Set.range a)`.
Its definition is available for arbitrary tuples; using this published
name introduces no nilpotence premise.

`jointSpace_stable` proves stability under every original element
of `R`. The algebra homomorphism `blockRestriction a hcomm χ`
then restricts the original evaluation action to `jointSpace a χ`,
with target its actual complex endomorphism algebra.
`blockTuple a hcomm χ i` is the image of the original embedded
generator. `shiftedBlockTuple a hcomm χ i` subtracts the scalar
`χ i` times the identity of that same subspace.
`blockAlgebra a hcomm χ` is the actual unital adjoin of
`blockTuple a hcomm χ`.

The definitions allow every `χ`, including those with zero joint
space. They preserve arbitrary carrier universes, zero-dimensional
spaces, empty tuples, zero and redundant generators, and eigenvalue
zero. They impose no nonzero-block premise, chosen basis or chosen
decomposition. Scalars and the identity add no tuple entry.
For the empty tuple the intersection is top, so its unique `χ` is
supported exactly when `V` is nonzero. On a zero carrier every joint
space is bottom and `jointBlockIndex a` is empty.

## Intrinsic laws and implemented proofs

`mem_jointSpace` unfolds membership in the intersection, and
`jointSpace_le` is its inclusion in each defining generalized
eigenspace. For `jointSpace_stable`, tuple commutation makes
the actual generated algebra commutative. Each of its elements
therefore commutes with each original generator. Mathlib's
`mapsTo_maxGenEigenspace_of_comm` preserves each defining
generalized eigenspace, hence their intersection.

`blockRestriction` reuses the published
`Langlands.CommutingDimension.restrictionAlgHom`.
The two evaluation laws are reflexive equalities after inclusion
in `V`. `blockAlgebra_eq_range` reuses
`adjoin_generators_top` and `adjoin_image_generators` to identify
the actual restricted adjoin with the restriction image.
`blockTuple_commute` maps original commutation through the
actual restriction homomorphism.

`shiftedBlockTuple_commute` and `shiftedBlockTuple_adjoin_eq`
reuse the published generic laws
`Langlands.CommutingDimension.commute_shift` and
`adjoin_shift_eq`. Thus the scalar subtraction preserves
commutation and leaves the actual unital generated algebra
unchanged. These laws establish no dimension estimate.

Only `shiftedBlockTuple_isNilpotent` requires
`FiniteDimensional ℂ V`. The joint space lies in each original
generalized eigenspace. Mathlib's
`isNilpotent_restrict_maxGenEigenspace_sub_algebraMap`
makes the corresponding scalar-subtracted endomorphism
nilpotent there. `Module.End.isNilpotent_restrict_of_le`
passes this fact to the invariant joint subspace. The
restricted original scalar subtraction is identified with
`shiftedBlockTuple` by its evaluation formula.
Nilpotence of the original generators is not a hypothesis.

The underlying construction route and the restriction/nilpotence
argument follow the actual local block construction in the published
proof `Langlands.CommutingDimension.commuting_dimension`,
authored by Worker 307. Its exported algebraic helpers are imported
by Lean name. This pair makes the actual block data reusable;
it introduces no alternate decomposition or comparison function.
Worker 709 authored the reusable API and source correspondence.
The restriction and nilpotence arguments adapt Worker 307's
published block-construction code, so both workers are credited
for this pair.

## Remaining scope

The source's decomposition into finitely many independent invariant
blocks, its dimension sum, its finite-sum real-power comparison and
the assembly reducing the full bound to the nilpotent case
remain separate statements and proofs. The present unit does
not assert that every vector belongs to one block or that
the supported index subtype is already finite.

The Library already proves the final commutative dimension
bound using the same underlying block route and a direct
nilpotent numerical induction. This construction does not
replace that result. The actual maximum, ideal-power and
complement arguments, head/tail comparisons, floor recurrence,
normalized numerical contradiction and the rest of the
whole-book program retain their owners and obligations.
