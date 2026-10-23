# Total complexes of ℓ-divisible systems of double complexes

Author: Worker 61. Built on `Langlands.Cohomology.DivisibleSystem` (the
`ℓ`-divisible systems `DivisibleSystem C ℓ`, their images `T.map F` under
additive functors preserving finite limits and finite colimits, and
`mapFunctor`), on `Langlands.Cohomology.DivisibleSystem.StandardResolution`
(the double complexes `standardResolutionDoubleComplexes` and their
augmentation, and the group case `indResBot`) and on Mathlib's total
complexes (`Mathlib.Algebra.Homology.TotalComplex`), restriction of complexes
along embeddings of complex shapes
(`Mathlib.Algebra.Homology.Embedding.Restriction`) and exactness of finite
coproducts (`Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic`). Names
in the first two sections are in the namespace `Langlands.Cohomology`, and
the others in `Langlands.Cohomology.DivisibleSystem`.

On p.306 Harris lets (2.5) be "the canonical free resolution of `M_m^{q,H}`
obtained via (2.4)", and lets `C_m^{•,H}` be "the simple complex associated
to the double complex `K_m^{-•,•,H}` for each `m`. Then another snake lemma
argument shows that `C_m^{•,H}` is an ℓ-divisible system of complexes of free
`ℤ/ℓ^mℤ[S(e)/H]`-modules as `m` varies."

This module forms the total (simple) complexes of the double complexes of the
StandardResolution module, with rows restricted to a finite range, and shows
that totalization carries `ℓ`-divisible systems of double complexes to
`ℓ`-divisible systems of `ℤ`-graded cochain complexes. It totalizes the
augmentation too. It proves no quasi-isomorphism and no freeness.

## The shape of the rows and the total complex shape

- `upFin N : ComplexShape (Fin N)` is the cochain complex shape on
  `Fin N = {0, …, N - 1}`: `(upFin N).Rel i j` holds exactly when
  `i + 1 = j` as natural numbers (`upFin_rel_iff`, by `rfl`). There is no
  differential out of `N - 1`.
- `upFinEmbedding N : (upFin N).Embedding (ComplexShape.up ℕ)` is the
  inclusion `Fin N ⊆ ℕ`, built with Mathlib's `ComplexShape.Embedding.mk'`.
  The instance `(upFinEmbedding N).IsRelIff` says that `i ⟶ j` is a
  differential in `upFin N` exactly when `i ⟶ j` is one in `ℕ`. Mathlib's
  `restrictionFunctor` needs this.
- `upFinTotalComplexShape N` is Mathlib's `TotalComplexShape` data for
  totalizing double complexes with rows `q ∈ Fin N` in the cochain direction
  (`upFin N`) and columns `r ∈ ℕ` in the chain direction
  (`ComplexShape.down ℕ`) into `ℤ`-graded cochain complexes
  (`ComplexShape.up ℤ`). The total degree of `(q, r)` is
  `π (q, r) = q - r` (`upFin_π`, by `rfl`). The signs are `ε₁ = 1` on the
  row differential `(q, r) ⟶ (q + 1, r)` and `ε₂ (q, r) = (-1)^q` on the
  column differential `(q, r) ⟶ (q, r - 1)`. Both differentials raise
  `q - r` by one (`rel₁`, `rel₂`), and Mathlib's sign rule
  `ε₂ (q, r) ε₁ (q, r') = -ε₁ (q, r) ε₂ (q + 1, r)`, for `q + 1 < N` and
  `r = r' + 1`, holds because `(-1)^(q+1) = -(-1)^q` (`ε₂_ε₁`). In Mathlib's
  total complex the differential on the summand `(q, r)` is then the row
  differential plus `(-1)^q` times the column differential; the row part is
  absent for `q = N - 1` and the column part for `r = 0`.
- `upFinFiber N n` is the set of `(q, r)` with `q - r = n`. The instance
  `upFinFiber_finite` says that it is finite: `r = q - n` is determined by
  `q`, and there are `N` values of `q`. `upFinFiber_eq_empty` says that it is
  empty for `n ≥ N`, because `q - r ≤ q < N`.

Restricting the rows is what makes the fibers finite. With `q` ranging over
all of `ℕ`, the pairs `(n + r, r)`, `r ∈ ℕ`, all have total degree `n`, and
the total complex would need infinite coproducts.

## Totalization is exact

`A` is an abelian category and `N : ℕ`.

- `hasTotal_upFin`: every double complex
  `K : HomologicalComplex₂ A (upFin N) (ComplexShape.down ℕ)` has a total
  complex, since the coproducts over the finite fibers exist in `A`.
- `totalSummands A N n` is the functor sending such a double complex to its
  family of summands of total degree `n`, a functor on the discrete category
  of `upFinFiber N n`. `totalSummandsEvalIso` identifies each summand with
  evaluation of the double complex at `(q, r)`, and the instances
  `totalSummands_preservesFiniteLimits` and
  `totalSummands_preservesFiniteColimits` follow, because limits and colimits
  of functors and of complexes are computed pointwise.
- `totalEvalIso A N n` is an isomorphism between the degree-`n` part of
  Mathlib's total complex functor and `totalSummands A N n ⋙ colim`. Mathlib
  defines the degree-`n` term of the total complex as the chosen coproduct of
  the summands of total degree `n`, so the components are identities. Its
  naturality is Mathlib's `ιTotal_map` together with `colimit.ι_map`, checked
  on each summand.
- `totalFunctor_upFin_preservesFiniteLimits`: totalization preserves finite
  limits. Limits of complexes are computed degreewise, and in degree `n`
  totalization is `totalSummands` followed by the colimit over the finite
  discrete category `upFinFiber N n`. Over a finite discrete category the
  colimit functor preserves finite limits in `A`, since finite coproducts are
  biproducts (Mathlib's `hasExactColimitsOfShape_discrete_finite`, used with
  Mathlib's `Abelian.hasFiniteBiproducts`). `totalFunctor_upFin_preservesFiniteColimits`
  is the colimit version, where the colimit functor preserves colimits in any
  case. `totalFunctor_upFin_additive` comes from preserving binary products
  (`Functor.additive_of_preserves_binary_products`).
- `isZero_total_X`: the total complex is zero in every degree `n ≥ N`, since
  the fiber is then empty.
- `upFinRestrictionEvalIso` identifies Mathlib's restriction of a double
  complex in `HomologicalComplex₂ A (ComplexShape.up ℕ) (ComplexShape.down ℕ)`
  along `upFinEmbedding N`, evaluated at `q`, with evaluation at `q`. The
  instances `upFinRestriction_preservesFiniteLimits` and
  `upFinRestriction_preservesFiniteColimits` follow degreewise.
- `upFinTotalFunctor A N` is restriction of the rows to `q < N` followed by
  totalization, a functor
  `HomologicalComplex₂ A (ComplexShape.up ℕ) (ComplexShape.down ℕ) ⥤ CochainComplex A ℤ`.
  It is additive and preserves finite limits and finite colimits by the
  instances above and Mathlib's instances for composites.
- `upFinTotalι A N K q r` is the inclusion of the summand `(K.X q).X r`, for
  `q < N`, into the degree `q - r` term of `(upFinTotalFunctor A N).obj K`
  (Mathlib's `ιTotal`). `isZero_upFinTotalFunctor_obj_X` is the vanishing in
  degrees `n ≥ N`.

## Total complexes of ℓ-divisible systems

`ℓ : ℕ`.

- `totalSystem N K`, for an `ℓ`-divisible system `K` of double complexes in
  `HomologicalComplex₂ A (ComplexShape.up ℕ) (ComplexShape.down ℕ)`, is
  `K.map (upFinTotalFunctor A N)`, an `ℓ`-divisible system of `ℤ`-graded
  cochain complexes. The parent module's `map` needs exactly the three
  instances of `upFinTotalFunctor`: the inclusions and projections of the
  system are totalized, and the torsion, short exactness and flatness
  conditions carry over. `totalSystemMap N f` is the induced morphism of
  systems (`mapFunctor`). `isZero_totalSystem_obj_X` is the vanishing of
  every member in degrees `n ≥ N`.

Now `P : A ⥤ A` is additive and preserves finite limits and finite colimits,
and `ε : P ⟶ 𝟭 A`.

- `standardTotalSystem N P ε K`, for
  `K : DivisibleSystem (CochainComplex A ℕ) ℓ`, is the `totalSystem N` of
  `K.standardResolutionDoubleComplexes P ε`. At level `m`, its degree-`n` term
  is the coproduct of `P^(r+1)` of the degree-`q` term of `K m` over the pairs
  with `q - r = n` and `q < N`. By Mathlib's definition of the total
  differential, its differential on the summand `(q, r)` is the sum of
  `P^(r+1)` of the differential `(K m).X q ⟶ (K m).X (q + 1)`, present only
  when `q + 1 < N`, and, for `r ≥ 1`, `(-1)^q` times the standard-resolution
  differential `P^(r+1)((K m).X q) ⟶ P^r((K m).X q)`.
- `standardTotalSystemι N P ε K m q r` is the inclusion of the summand
  `P^(r+1)((K m).X q)` into the degree `q - r` term of level `m`.
- `standardTotalSystemAugmentation N P ε K` is the totalized augmentation,
  `totalSystemMap N` of the StandardResolution module's
  `standardResolutionDoubleComplexesAugmentation`. Its target is exactly the
  `totalSystem N` of `K.map ((ChainComplex.single₀ A).mapHomologicalComplex (ComplexShape.up ℕ))`:
  the total complex, with rows `q < N`, of the system `K` placed in resolution
  degree `0`. In degree `n` every summand of that target other than `(n, 0)`
  is zero, so mathematically it is the restriction of `K` to degrees `q < N`,
  extended by zero to `ℤ`. This identification, and hence a morphism to `K`
  itself, is not constructed.

## The group case

`k` is a commutative ring and `Γ` a finite group, with representations in
Mathlib's `Rep.{max w u v} k Γ` as in the StandardResolution module.

- `groupStandardTotalSystem N K` and `groupStandardTotalSystemAugmentation N K`
  are `standardTotalSystem` and its augmentation for `P = indResBot k Γ` and
  `ε = indResBotCounit k Γ`, induction after restriction to the trivial
  subgroup and its counit.

## Provenance and interpretation

Harris, *Galois properties of cohomological automorphic forms on GL(n)*,
J. Math. Kyoto Univ. 39-2 (1999), section 2, printed pp.305–306. Worker 61
read (2.5) and the following paragraph on p.306 in the scanned original.

1. The simple complex. Harris's `C_m^{•,H}` is the simple complex of the
   double complex `K_m^{-•,•,H}` of the resolutions (2.5) of the complexes
   `M_m^{•,H} = G_m^•(U(ẽ)_F̄)^H`. `standardTotalSystem` is this
   construction for an `ℓ`-divisible system `K` of `ℕ`-graded cochain
   complexes in place of `M_m^{•,H}`, and `groupStandardTotalSystem` uses the
   group-ring functor of (2.4) in the form explained in the StandardResolution
   module. The module does not apply it to the H-invariants systems of the
   Invariants module (for `Γ = S(ẽ)/H`); that application is a separate
   step.
2. Indexing. The total degree of the `(q, r)` term `P^(r+1)((K m).X q)` is
   `q - r`. This is our indexing convention. With Harris's labels the same
   term is `K_m^{-(r+1),q,H}`, of total degree `q - r - 1` (the
   StandardResolution module, item 6). In our convention `P((K m).X q)`, the
   term next to `M_m^{q,H}` in (2.5), has total degree `q`, so the totalized
   augmentation preserves degrees.
3. Signs. Harris does not state a sign rule for the simple complex. Mathlib's
   total complexes require one, and the module uses `ε₁ = 1` and
   `ε₂ (q, r) = (-1)^q`.
4. Finite rows. Harris's complexes `M_m^{•,H}` have finite length (p.305: "an
   ℓ-divisible system of finite-length complexes"). For the truncated smooth
   Godement systems of the Truncation and Sections modules, the terms vanish
   above `D + 1`, and with `N = D + 2` the restriction to `q < N` drops only
   zero rows. The module does not prove this comparison: it does not show
   that restricting the rows of a system that vanishes in degrees `≥ N`
   loses nothing, and it does not compare the totals for different `N`. For
   `K` with nonzero terms in degrees `≥ N`, `standardTotalSystem N P ε K`
   sees only the rows `q < N`.
5. Divisibility. Harris obtains the `ℓ`-divisibility of `C_m^{•,H}` from
   "another snake lemma argument". Here it is derived from the exactness of
   totalization (finite coproducts are exact in an abelian category) and the
   parent module's `map`, which carries `ℓ`-divisible systems along exact
   additive functors.

The vanishing in degrees `≥ N`, the exactness instances, the systems and the
augmentation are derived.

## Scope

The module does not prove that the totalized augmentation is a
quasi-isomorphism, that any term is free or projective (Harris's "complexes of
free `ℤ/ℓ^mℤ[S(e)/H]`-modules"), or that the target of the augmentation is
isomorphic to the restriction of `K`. It does not compare different `N`, or
the restricted rows with the unrestricted double complex. It does not form the
isomorphism `C_m^{•,H} = [C_m^{•,H'}]^H`, the direct limit over `H`, the
quasi-isomorphism (2.6), the isomorphism (2.7) or Lemma 2.8, and it does not
connect to the H-invariants module.

Source registration: Harris 1999,
`harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`, SHA-256
`525a222c4489ee9d3fe86a52c6c17ffb30fcc7c31f24c16a64669e9615085b26`.

Dependencies are the modules named above, pinned to Lean 4.34.0 and Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`.
