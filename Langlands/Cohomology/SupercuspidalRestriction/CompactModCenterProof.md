# Proof of `CompactModCenterRestrictionStatement`

```lean
theorem compactModCenterRestrictionStatement_proof (G : Type) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G]
    [TotallyDisconnectedSpace G] [SigmaCompactSpace G] :
    CompactModCenterRestrictionStatement G
```

The theorem
`Langlands.Cohomology.SupercuspidalRestriction.compactModCenterRestrictionStatement_proof`
proves the Library statement
`Langlands.Cohomology.SupercuspidalRestriction.CompactModCenterRestrictionStatement G`
unchanged, with `G` explicit and the statement's instance binders.

Universes: everything is in universe `0`, as in the statement. The group is
`G : Type`. `π` and the summands `σ i` live in `SmoothRep.{0, 0, 0} ℂ G` and
`SmoothRep.{0, 0, 0} ℂ H`, so the coefficient ring, group and carrier
universes are all `0`. The auxiliary declarations of Steps 1–4 below also take
their groups and carriers in `Type`. The companion module
`CompactCoefficientRestriction` is universe polymorphic (its Markdown names
the universes `uG` and `uV`) and is used here at universe `0`.

Hypotheses: `G` is a Hausdorff, locally compact, totally disconnected,
σ-compact topological group. `H` is an open normal subgroup with
`H ∩ Z(G)` compact, and `Z(G) H` has finite index. Let `π` be an irreducible
smooth complex representation of `G` whose matrix coefficients are compactly
supported modulo the center. The theorem produces `m : ℕ` and smooth
representations `σ : Fin m → SmoothRep ℂ H`. Each `σ i` is irreducible and
has compactly supported matrix coefficients, and the restriction of `π` to
`H` is isomorphic to the finite biproduct `⨁ σ`.

The proof follows Bernstein–Zelevinsky (1976): Lemma 3.26 (p.36) for the
splitting, which uses Lemma 2.9 (p.17) and Schur's lemma 2.11 (p.18), and 3.28
(p.36) with Theorem 3.21 (pp.34–35) for compact coefficients. The Lean proof
works out these steps as follows. Auxiliary declarations live in the namespace
`Langlands.Cohomology.SupercuspidalRestriction.CompactModCenterProof`.

## Step 1: the center acts by scalars

`rank_le_aleph0` proves that an irreducible smooth representation `ρ` of a
σ-compact group has dimension at most `ℵ₀`. This is the counting argument in
the proof of BZ 2.11. Take a nonzero vector `v`
(`FiniteIndexRestriction.exists_ne_zero`), fixed by an open subgroup `K`. Each
compact set `compactCovering G n` has finite image in the discrete quotient
`G / K`. So the orbit `{ρ g v}` is a countable union of finite sets. The orbit
spans `V` (`FiniteIndexRestriction.span_orbit_eq_top`), and `rank_span_le`
bounds the rank by the orbit's cardinality.

`center_acts_by_scalars` applies the Library's Schur lemma for countable
dimension, `countableDimensionalSchur`, to the intertwining operator
`Representation.IntertwiningMap.centralMul ρ z` of a central element `z`. The
result is a scalar `c` with `ρ z v = c • v` for all `v`.

## Step 2: an internal direct sum of irreducible subrepresentations

`exists_independent_irreducible` takes a representation `ρ` of `G`, a normal
subgroup `H` with `Z(G) ⊔ H` of finite index, irreducibility, and the scalar
action of the center. It returns `m` and subrepresentations
`W : Fin m → Subrepresentation (ρ.comp H.subtype)`. Each `W i` is irreducible,
their underlying submodules are independent (`iSupIndep`), and their supremum
is `⊤`.

The Library's Clifford-type theorem `FiniteIndexRestriction.exists_finite_atoms`
(BZ 2.9 b) writes the restriction to `H ⊔ Z(G)` as the supremum of finitely
many atoms of its subrepresentation lattice. Because the center acts by
scalars, `FiniteIndexRestriction.supCenterOrderIso` identifies that lattice
with the subrepresentation lattice of the restriction to `H`. So these are
also atoms for `H`; this is the argument of BZ 3.26.
`FiniteIndexRestriction.isIrreducible_toRepresentation_of_isAtom` makes each
of them irreducible.

The lemma `exists_supIndep_subset` selects an independent subfamily with the
same supremum. It is a greedy induction in a modular lattice: a new element
is kept when it is disjoint from the supremum of the elements already kept,
and dropped when it lies below that supremum. An atom always satisfies one of
the two alternatives. The kept indices are reindexed by `Fin m` via
`Finset.equivFin`.

## Step 3: the decomposition as a biproduct

Section `Projection` fixes a representation `ρ` of `H` and a family
`W : Fin m → Subrepresentation ρ` with independent submodules whose supremum
is `⊤`. `isCompl_iSup_ne` shows that `W k` is complementary to the supremum
of the other summands. `proj k` is the linear projection onto `W k` along
that complement (`Submodule.projectionOnto`). The lemmas are:

- `proj_of_mem`: `proj k` is the identity on `W k`.
- `proj_of_mem_ne`: `proj k` vanishes on `W j` for `j ≠ k`.
- `sum_proj`: `∑ k, proj k x = x`.
- `proj_apply`: `proj k` is `H`-equivariant.

The last two are proved by induction over the supremum
(`Submodule.iSup_induction`), using the first two.

Section `Biproduct` works in the category `SmoothRep ℂ H`.
`subSmooth X S` is a subrepresentation `S` of a smooth representation `X`,
viewed as a smooth representation (vectors of `S` are fixed by the same open
subgroups as in `X`). `incl` is its inclusion. `projHom k : X ⟶ subSmooth X (W k)`
is the equivariant projection. `nonempty_iso_biproduct` builds the
isomorphism `X ≅ ⨁ k, subSmooth X (W k)` with `hom := biproduct.lift projHom`
and `inv := biproduct.desc incl`, for the biproducts given by
`Abelian.hasFiniteBiproducts`, the instance used in the statement.
`inv ∘ hom = 𝟙` is `sum_proj` (via `biproduct.lift_desc` and `hom_sum`, which
says `SmoothRep.hom` commutes with finite sums). `hom ∘ inv = 𝟙` is checked
on each pair of biproduct components with `proj_of_mem` and `proj_of_mem_ne`.
`hom_ext'` reduces equality of morphisms to equality of the underlying maps
on vectors.

## Step 4: compact coefficients of the summands

`hasCompactCoefficients_summand` proves `HasCompactCoefficients` for each
summand `subSmooth X (W k)`, where `X` is the restriction of `π` to `H`. First,
the whole restriction `X` has compactly supported coefficients for every
smooth functional (`HasCompactSmoothDualCoefficients`). This is
`hasCompactSupport_restrict_matrixCoefficient` from the companion module
`Langlands.Cohomology.SupercuspidalRestriction.CompactCoefficientRestriction`;
it uses that `H` is open and `H ∩ Z(G)` is compact (BZ 3.21, 3.28). Then the
Library lemma `HasCompactSmoothDualCoefficients.of_surjective` passes this
property to the summand along the surjective intertwining projection
`projHom k`. The projection is surjective by `proj_of_mem`.

## Step 5: assembly

`compactModCenterRestrictionStatement_proof` introduces the hypotheses and
installs the normality and finite-index hypotheses as instances. Let
`X := (restriction ℂ G H).obj π`. Its representation is definitionally
`π.representation.comp H.subtype`. Step 1 gives the scalar action of the
center. Step 2 gives `W`. The witness is `σ k := subSmooth X (W k)`:
irreducible by Step 2, with compact coefficients by Step 4, and
`X ≅ ⨁ σ` by Step 3.

## Source

I. N. Bernstein and A. V. Zelevinsky, *Representations of the group GL(n,F),
where F is a non-Archimedean local field*, Russian Mathematical Surveys 31:3
(1976), 1–68: Lemma 2.9, p.17; Proposition 2.11, p.18; Theorem 3.21,
pp.34–35; Lemma 3.26 and Proposition 3.28, p.36. Registered literature ID
`bernstein-zelevinsky-1976-representations-gln`, source SHA-256
`72dc22eb9991112936a88327f00d0f02a16a2bf8747518ca0ecfeeadd188e50c`. BZ state
3.26 for `G = GL_n(F)` and `G°`. The Lean proof uses only the hypotheses of
the Library statement for a general `G` and `H`.
