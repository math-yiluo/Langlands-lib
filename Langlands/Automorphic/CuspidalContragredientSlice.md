# Irreducible admissible finite slices of supplied unitary cuspidal duals

Module: `Langlands.Automorphic.CuspidalContragredientSlice`. Author: Worker 1827.

## Main theorem

`CuspidalOperatorRealization.exists_irreducibleAdmissible_finiteSlice_of_contragredient`.
Its inputs are a number field `F : Type uF` with `[CompactSpace (AdeleQuotient F)]`, `r : ℕ`,
actual cuspidal realizations `T T' : CuspidalOperatorRealization F r`, a proof of
`Langlands.ClassField.Global.RelativeWeilGroup.HasUnitaryCentralCharacter T`, and the
full-operator relation `T'.realization.IsContragredientOf T.realization`. It gives

```text
∃ A : T'.FiniteSlice, A.subspace.IsIrreducible ∧ Langlands.IsAdmissible A.subspace.representation.
```

So the supplied dual `T'` contains a nonzero actual finite slice of automorphic forms,
inside its actual finite image, on which `GL_{r+1}` of the finite adeles acts irreducibly and
admissibly. The hypotheses are exactly those of the published
`CuspidalContragredientPresentationExistenceStatement`, apart from its input presentation.
No admissibility, factorization, countability, unitarity of `T'` or irreducibility of the
whole finite restriction is assumed. This is the finite-slice step of that statement. The
Flath assembly of a spectral presentation from the slice is separate work and is not
claimed here.

The module also defines
`CuspidalOperatorRealization.contragredientIrreducibleSlice T T' hT hdual : T'.FiniteSlice`,
a slice chosen (`Classical.choose`) from this existence theorem. Its two properties are
`contragredientIrreducibleSlice_isIrreducible` and `contragredientIrreducibleSlice_isAdmissible`.
The definition has no further content; it names the slice so that later presentation
assembly can refer to it.

## The implemented proof

1. `CuspidalOperatorRealization.exists_compactInvariantForm`
   ([CuspidalUnitaryCompactForm](CuspidalUnitaryCompactForm.md)) gives a positive definite
   Hermitian form `b` on `T`, invariant under the finite and the standard infinite compact
   actions.
2. Unpack the relation: the pairing `B`, its invariance, injectivity of `B.flip` and
   surjectivity onto contragredient functionals (smooth for the finite action, finite for
   the compact action).
3. `OperatorRealization.rank_contragredientFunctionals_le`: every space of such functionals
   on `T` lies in the range of `B.flip`. Its rank is therefore at most that of `T'.Space`,
   which is `≤ ℵ₀` by `OperatorRealization.rank_le_aleph0`
   ([OperatorRealizationCountable](OperatorRealizationCountable.md)) applied to the
   irreducible `T'`.
4. `CountableDual.exists_irreducible_admissible`
   ([CountableDualAdmissible](../Representation/Unitary/CountableDualAdmissible.md)) is
   applied to the finite action `ρ` and the compact action `κ` of `T`. The commutation is
   the Library's `finiteRepresentation_compactRepresentation`, compact finiteness is
   `compactRepresentation_isFiniteVector`, and finite smoothness is
   `finiteRepresentation_isSmooth`. `finiteAdelicGL_exists_compact_le` gives compact open
   refinements by intersecting with the compact open subgroup
   `FiniteAdelicGL.standardIntegral` (compact by `isCompact_standardIntegral`). The result
   is an irreducible admissible nonzero subrepresentation `A₀` of the finite action of `T`.
5. `OperatorRealization.isContragredientFunctional_conjFunctional`: for every `h`, the
   functional `⟪h, ·⟫` is smooth, because the form is finite-invariant. It is compact-finite,
   because compact translates of it are `⟪κ k h, ·⟫` and lie in the conjugate-linear image of
   the finite-dimensional compact orbit span of `h`. So it is a contragredient functional and
   is attained by `B.flip`.
6. `CountableDual.exists_dual_subrepresentation` transfers `A₀` along the resulting
   conjugate-linear injective equivariant map to an irreducible admissible nonzero
   subrepresentation `A'` of the finite action of `T'`. The equivariance of `B.flip` is the
   Library's `IsInvariantPairing.flip_finite`.
7. `CuspidalOperatorRealization.exists_finiteSlice_of_subrepresentation` realizes `A'` in
   automorphic forms through `formInclusion`, as `finiteRealizationImage`. This is a
   `FiniteSlice` (contained in the actual finite image, nonzero). The genuine equivalence
   `finiteRealizationImageEquiv` transports irreducibility (`CountableDual.isIrreducible_of_equiv`)
   and admissibility (`Langlands.isAdmissible_of_equiv`).

## Relation to the literature route

The target Markdown of `CuspidalContragredientStatement` sketches a route through cusp-form
admissibility (Borel–Jacquet 1979 §4.5; Getz–Hahn 2024 Theorem 6.3.4) and finite/infinite
separation (Getz–Hahn Lemma 6.3.6). The implemented proof does not use those results. It
uses instead the positive Petersson-type band form of `T` and the fact that the supplied
dual `T'` realizes all smooth compact-finite functionals while having countable dimension.
Together these force finite multiplicities of compact types in the fixed vectors of `T`.
This route is internal, and its admissibility and irreducibility conclusions concern only
the constructed slice.
