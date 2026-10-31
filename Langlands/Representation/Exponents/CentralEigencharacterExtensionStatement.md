# Extending generalized eigencharacters of a central action

Author: Worker 828.

This module states one proposition,
`Langlands.CentralEigencharacterExtensionStatement.{uG,uA,uB,uX}`. It is a
statement only; the module contains no proof of it. The four universes
`uG` (group), `uA` (acting commutative group), `uB` (parameter monoid) and
`uX` (representation carrier) are independent.

## Quantifiers and hypotheses

The proposition is closed. It quantifies over

- a group `G : Type uG` with a topology (`[Group G] [TopologicalSpace G]`),
  with no further topological condition;
- a commutative group `A : Type uA` with a topology in which multiplication
  is separately continuous (`[CommGroup A] [TopologicalSpace A]
  [SeparatelyContinuousMul A]`);
- a monoid `A' : Type uB`, with no topology;
- a complex vector space `X : Type uX`, with no topology or finiteness
  condition, and an actual representation `π : Representation ℂ G X`;
- the hypothesis `IsAdmissible π`, the project predicate of
  `Langlands.Representation.Smooth.Definitions`: every vector is fixed by
  some open subgroup, and the space of `K`-fixed vectors is a finitely
  generated (hence finite-dimensional) complex vector space for every open
  subgroup `K`;
- a continuous homomorphism `φ : A →* G` whose values commute with every
  element of `G` (`∀ a g, Commute (φ a) g`): `A` acts through the centre;
- a homomorphism `β : A' →* A`, with no condition;
- a character `χ : A' →* ℂˣ`, with no continuity condition.

The final hypothesis is `IsGeneralizedEigencharacter ((π.comp φ).comp β) χ`,
the published predicate of `Langlands.Representation.Exponents.Jacquet`.
By `isGeneralizedEigencharacter_iff` it means: there exist one natural
number `k` and one nonzero vector `v : X` such that
`((π (φ (β b)) - (χ b : ℂ) • 1) ^ k) v = 0` for every `b : A'`.

## Conclusion

There is a character `ψ : A →* ℂˣ` such that

- its kernel `ψ.ker` is an open subset of `A`;
- `IsGeneralizedEigencharacter (π.comp φ) ψ`: some nonzero vector and one
  power `k` satisfy `((π (φ a) - (ψ a : ℂ) • 1) ^ k) w = 0` for every
  `a : A`;
- `ψ.comp β = χ`: `ψ (β b) = χ b` for every `b : A'`.

So a generalized eigencharacter of the pulled-back action along `β`
extends, along `β`, to a generalized eigencharacter of the whole central
action of `A`, and that extension is smooth. The statement asserts nothing
about uniqueness of `ψ`, about the size of the generalized eigenspace, or
about any decomposition of `X`.

## Intended proof route (not part of this statement)

This is the route of the proof module
`Langlands.Representation.Exponents.CentralEigencharacterExtensionProof`,
not an extra premise. Pick a nonzero vector `v` of the generalized
character space of `χ` and an open subgroup `K` fixing it. Intersect that
character space with the `K`-fixed vectors. The result is
finite-dimensional by admissibility, contains `v`, and is stable under
every `π (φ a)` because `φ a` is central. The commuting restrictions have a
common eigenvector `w` (`EndomorphismBound.exists_common_eigenvector`), and
its eigenvalues form a character `ψ`
(`EndomorphismBound.exists_character_of_forall_eigen`). Since `w` is fixed
by `K`, `ψ` is trivial on the open subgroup `φ⁻¹ K`, so its kernel is open.
Since `w` lies in the generalized character space of `χ`, its eigenvalue
for `π (φ (β b))` equals `χ b`.

## Provenance

The statement is project-internal and derived; it is not a translation of
one literature statement. It isolates a finite-dimensional linear-algebra
step: a generalized eigencharacter on a sub-monoid of a central group
action extends to a smooth generalized eigencharacter of the whole action.
Exponents of admissible representations along a split centre, to which it
is applied, are defined in Waldspurger 2003, I.3 (registered
`waldspurger-2003-plancherel`). It was extracted from the
spectral step of the proof of `Langlands.GLInductionWeakJacquetBoundsStatement`
(task `5c9a0e18-0039-4f00-81bc-e103757b5a3a`, shared draft revision 2,
module `InductionWeakJacquetBoundsSpectral`), where `A` is a group of
flattened block scalars and `β` is restriction along a chamber index. It is
published separately because Worker 526 needs the same extraction in a
different context.

This statement supplies no Jacquet admissibility theorem, no geometric
lemma, no exponent bound, and no statement about the inducing or Jacquet
functors.
