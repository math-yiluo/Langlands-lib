# Representations of free monoids given by generators

Author: Worker 3657.

Lean module: `Langlands.Representation.FreeMonoidGenerators`. It imports the
draft module `Langlands.Representation.CommutingFamilyUniqueness`, the
Library modules `Langlands.Representation.Archimedean.GKModuleDensity` and
`Langlands.Automorphic.OperatorSubquotientLocalComponentStatement` (for
`Archimedean.gkHoms` and `Archimedean.IsGKIsotypic`), and Mathlib's
`FreeMonoid`. It changes no published file.

A family of linear operators `act a` (`a : α`) on a vector space `V` over a
field `k` defines the representation `rep act := FreeMonoid.lift act` of the
free monoid on `α`. The module translates the hypotheses of
`Langlands.CommutingFamily.exists_linearEquiv_of_isotypic` for such
representations into statements about the generators. It is used to read
the place actions of an operator subquotient (local translations at finite
places, compact translations and Lie actions at infinite places) as one
commuting family of monoid representations indexed by the places.

## Generators (section `Generators`)

- `rep act`, `rep_of` (the generator `a` acts by `act a`, `rfl`).
- `rep_commute`, `rep_comm`: if the generators of two families commute, all
  words commute (induction on words with `FreeMonoid.inductionOn'`).
- `rep_mem`: a subspace stable under the generators is stable under all
  words.
- `rep_map`, `intertwiningMap f h`, `intertwiningMap_toLinearMap`: a linear
  map intertwining the generators is an intertwining map of the free-monoid
  representations, with the same underlying linear map.
- `map_generator`, `comm_of_rep`: conversely, an intertwining map (or a
  linear map commuting with every word) intertwines the generators.
- `isIrreducible_rep`: if `W` is nonzero and every subspace stable under the
  generators is `⊥` or `⊤`, the free-monoid representation is irreducible
  (Mathlib's `Representation.IsIrreducible`, i.e. `IsSimpleOrder` of
  subrepresentations).
- `scalar_rep`: if every linear map commuting with the generators is a
  scalar, every self-intertwiner is a scalar multiple of the identity.

## Spanning families and equivalence (sections `Span`, `Equivalence`)

- `iSup_range_eq_top_of_forall_exists`: if the ranges of a family of maps
  `W → V` span `V` and every member occurs in a second family, the ranges of
  the second family span `V`.
- `exists_apply_ne_zero_of_isotypic`: a nonzero representation spanned by
  the images of intertwining maps from `ρ` receives some `f` with `f u ≠ 0`.
- `nonempty_equiv_of_isotypic`: if a nonzero `σ` is `ρ`-isotypic and
  `τ`-isotypic for irreducible `ρ`, `τ`, and the self-intertwiners of `τ` are
  scalars, then `ρ` and `τ` are equivalent. Proof: take `f : ρ → σ` and `u`
  with `f u ≠ 0`; `CommutingFamily.exists_isImage` moves `f u` by a monoid
  algebra element `a` to a nonzero image of a vector of `τ`; the same vector
  `σ(a) (f u) = f (ρ(a) u)` is an image of a vector of `ρ`; by
  `nonempty_equiv_orbitSpan` both `ρ` and `τ` are equivalent to the cyclic
  subrepresentation it generates (Mathlib `Representation.Equiv.trans`,
  `symm`).
- `exists_fixed_line_of_equiv`: if the vectors of `τ` fixed by a set `K` lie
  on a line, the same holds for every `ρ` equivalent to `τ`.
- `IsCommonType τ σ σ'`: `τ` is irreducible with scalar self-intertwiners and
  both `σ` and `σ'` are `τ`-isotypic. These are exactly the per-index
  hypotheses of `exists_linearEquiv_of_isotypic`.

## Monoid representations (section `Monoid`)

For `ρ : Representation k G W` the generators are `⇑ρ`.

- `ofIntertwiningMap`, `toIntertwiningMap`: intertwining maps of `ρ, σ` and
  of `rep ⇑ρ, rep ⇑σ` correspond.
- `iSup_range_rep_eq_top`, `isIrreducible_rep_coe`, `scalar_rep_coe`:
  isotypy, irreducibility and scalar self-intertwiners pass from `ρ` to
  `rep ⇑ρ`.
- `isCommonType_monoid`: let `σ` be nonzero and `τ`-isotypic for an
  irreducible `τ` with scalar self-intertwiners; if `σ` and `σ'` are
  `ρ`-isotypic for an irreducible `ρ`, then `rep ⇑ρ` is a common type of
  `rep ⇑σ` and `rep ⇑σ'`, and `ρ ≃ τ`. Scalar self-intertwiners of `ρ` come
  from those of `τ` along `ρ ≃ τ` by `CommutingFamily.scalar_of_equiv`.

## `(𝔤, K)`-modules (section `GK`)

The generators are indexed by a type `Γ` with a surjection
`dec : Γ → K ⊕ 𝔤` (in the application `Γ` is `K ⊕ 𝔤` lifted by `ULift` to
the universe of the number field, so that all places have generators in one
universe).

- `gkGenerators dec ρ π a` acts by `ρ k` if `dec a = inl k` and by `π X` if
  `dec a = inr X`; `gkRep dec ρ π := rep (gkGenerators dec ρ π)`;
  `gkGenerators_of_eq_inl`, `gkGenerators_of_eq_inr`.
- `gkGenerators_map`, `iSup_range_gk_eq_top`: maps in `Archimedean.gkHoms`
  intertwine the generators, so `Archimedean.IsGKIsotypic` gives isotypy of
  the free-monoid representations.
- `isIrreducible_gk`: `Archimedean.IsIrreducibleGKModule` gives
  irreducibility (uses surjectivity of `dec`).
- `scalar_gk`: under the hypotheses `GKModuleDensity.Hyp` (irreducible,
  admissible, `K`-finite, continuous matrix coefficients), the Library's
  Schur lemma `GKModuleDensity.exists_eq_scalar` gives scalar
  self-intertwiners.
- `isCommonType_gk`: the `(𝔤, K)` analogue of `isCommonType_monoid`, with
  `τ` an irreducible admissible module satisfying `GKModuleDensity.Hyp`.

## Provenance

The module is internal infrastructure; its statements are elementary facts
about free monoids and isotypic modules and are not taken from a source.
`nonempty_equiv_of_isotypic` is the module-theoretic step "the class of `W_i`
is determined by that of `W`, for the restriction of `W` to `G_i` is
`W_i`-isotypic" in Flath, *Decomposition of representations into tensor
products* (1979), end of the proof of Theorem 1, p.180 (PDF 176)
(`flath-1979-tensor-products`, SHA256
`3b9fe0145da81d870ef8967be83635cd440a2581fe043e64e63324e22dec4db5`), here
with the scalar self-intertwiner hypothesis on one of the two types instead
of admissibility.

## Check

`lean_check` 37881b85 (module alone): 0 errors, 0 warnings; lake build
dbe84f71 of the full Task 6817 draft: 0 errors, 0 warnings.
