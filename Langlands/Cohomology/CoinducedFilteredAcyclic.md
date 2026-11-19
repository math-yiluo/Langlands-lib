# Coinduced modules and filtered colimits in group cohomology

Module `Langlands.Cohomology.CoinducedFilteredAcyclic`.

This module proves two pieces of algebra about group cohomology (`groupCohomology`, the
cohomology of Mathlib's inhomogeneous cochain complex of a `Rep k G`):

1. A representation whose elements are freely described by their translates has no
   positive cohomology. This is a coordinate form of Shapiro's lemma for the trivial
   subgroup.
2. For a **finite** group `G`, vanishing of `H^n` passes to filtered colimits of
   representations.

Combined, they show that for a finite group a filtered colimit of such "coinduced"
representations has no positive cohomology
(`isZero_groupCohomology_succ_of_isColimit_coinduced`).

## Provenance

This is a derived helper module written for Task 7634, the local acyclicity of restricted
smooth analytic point products. Both results are adapted from standard ones:

- Serre, *Local Fields* (GTM 67), Ch. VII §2, Proposition 1 (p. 112; source
  `serre-1979-local-fields`): a co-induced `G`-module `Hom_ℤ(ℤ[G], X)` has `H^q = 0` for
  `q ≥ 1`. The module of all functions `G → A` is co-induced in this sense. Here the
  coefficients are `k`-modules, and the proof goes through Mathlib's Shapiro isomorphism
  instead of Serre's Ext argument.
- Serre, *Galois Cohomology*, Ch. I §2.2, Proposition 8 (p. 11; source
  `serre-1997-galois-cohomology`): `H^q(G, lim→ A_i) = lim→ H^q(G, A_i)`, proved by
  identifying the cochain complexes. `isZero_groupCohomology_of_isColimit` is the
  vanishing-only case of this for a constant finite group `G`. It is stated for colimits
  over a filtered category instead of a directed set.

Neither Lean statement is a literal transcription of a published statement. The Lean
statements below are the exact content.

## Coinduced modules

- `coindBot k G A` (abbrev) is `Rep.coind (⊥ : Subgroup G).subtype (Rep.trivial k ⊥ A)`.
  Its underlying module is the module of all functions `f : G → A`, and `h` acts by
  `(h • f) g = f (g * h)`. `mem_coindV_bot` checks that every function `G → A` lies in the
  underlying submodule.
- `coordinates M π : M →ₗ[k] coindBot k G A` sends `m` to `g ↦ π (g • m)`, for a
  `k`-linear map `π : M → A` into a `k`-module `A`.
- `coordinatesEquiv M π hπ` is the linear equivalence given by `coordinates M π`, under the
  hypothesis `hπ` that `m ↦ (g ↦ π (g • m))` is bijective onto all functions `G → A`.
  `coordinatesEquiv_comm` states that it intertwines the `G`-actions.
- `isZero_groupCohomology_succ_of_bijective M π hπ n` states that if
  `m ↦ (g ↦ π (g • m))` is a bijection `M → (G → A)`, then `H^{n+1}(G, M) = 0` for every
  `n : ℕ`.
- `isZero_groupCohomology_succ_of_bijective_inv` is the same conclusion when instead
  `m ↦ (g ↦ π (g⁻¹ • m))` is bijective.

**Proof.** `coordinatesEquiv` is an isomorphism of representations. So
`groupCohomology.mapIso` (along the identity of `G`) identifies `H^{n+1}(G, M)` with the
cohomology of `coindBot k G A`. Mathlib's Shapiro isomorphism `groupCohomology.coindIso`
identifies that with `H^{n+1}` of the trivial subgroup with coefficients `A`. That group
vanishes by `isZero_groupCohomology_succ_of_subsingleton`. The `_inv` variant composes the
given bijection with the involution `f ↦ (g ↦ f g⁻¹)` of `G → A`.

## Exactness through cocones of complexes

`exactAt_of_cocone` takes:

- a functor `F : J ⥤ HomologicalComplex (ModuleCat R) c` (any category `J`),
- a cocone `C` over `F`, and
- a degree `n`.

Assume three things:

- (`hsurj`) every element of `C.pt.X n` comes from some `(F.obj i).X n`;
- (`hzero`) every element `y` of `(F.obj i).X (c.next n)` that maps to `0` in the cocone is
  already killed by `(F.map f).f (c.next n)` for some `f : i ⟶ j`;
- (`hex`) every complex `F.obj j` is exact at `n`.

Then `C.pt` is exact at `n`.

**Proof.** Write the cycle as the image of `y` from stage `i`. Its differential dies in the
cocone, so by `hzero` it dies along some `f : i ⟶ j`. Then `F.map f` of `y` is a cycle at
stage `j`, hence a boundary `d w` by `hex j`. The image of `w` in the cocone is the required
preimage, by the compatibility of the cocone maps with the differentials and with
`F.map f`.

## Filtered colimits of representations

In this section `J` is a small filtered category, `F : J ⥤ Rep k G`, and `hc` is a colimit
cocone `c` for `F`.

- `preservesColimit_forget_of_filtered`: the forgetful functor `Rep k G ⥤ Type` preserves
  the colimit of `F`. This holds because it is the composite of `forget₂` to
  `ModuleCat k`, which preserves colimits, with the forgetful functor of `ModuleCat k`,
  which preserves filtered colimits.
- `exists_family_rep hc x`: a family `x : ι → c.pt` indexed by a finite type comes from
  one stage `i`.
- `exists_family_eq_zero hc y hy`: a finite family `y : ι → F.obj i` that vanishes in
  `c.pt` already vanishes after some `f : i ⟶ j`.

Both use `Concrete.isColimit_exists_rep` / `Concrete.isColimit_exists_of_rep_eq` for each
member separately. Then `IsFiltered.sup`, `IsFiltered.toSup` and
`IsFiltered.toSup_commutes` merge the finitely many stages, and in the second lemma also
the finitely many killing morphisms.

- `isZero_groupCohomology_of_isColimit [Finite G] hc n h`: if
  `H^n(G, F.obj j) = 0` for every `j`, then `H^n(G, c.pt) = 0`.

**Proof.** Vanishing of `H^n` is exactness at `n` of the inhomogeneous cochain complex
(`HomologicalComplex.exactAt_iff_isZero_homology`). Apply `exactAt_of_cocone` to the image
of `c` under `groupCohomology.cochainsFunctor k G`. In every degree the cochains are the
functions `G^m → (−)`, and `G^m` is finite. So `hsurj` and `hzero` are exactly
`exists_family_rep` and `exists_family_eq_zero` with `ι = Fin m → G`.

- `isZero_groupCohomology_succ_of_isColimit_coinduced [Finite G] hc n h`: suppose each
  `F.obj j` admits a `k`-module `A` and a linear map `π : F.obj j → A` with
  `m ↦ (g ↦ π (g • m))` bijective. Then `H^{n+1}(G, c.pt) = 0`.

**Proof.** Combine the two previous results.
