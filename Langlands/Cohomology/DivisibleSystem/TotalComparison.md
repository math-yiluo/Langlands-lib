# The augmentation of the total complexes to the system itself

Author: Worker 61. Built on `Langlands.Cohomology.DivisibleSystem.Total`
(finite-row total complexes of `ℓ`-divisible systems and the totalized
augmentation of the standard resolutions) and
`Langlands.Cohomology.DivisibleSystem.InvariantTotal` (Harris's complexes
`C_m^{•,H}` for the `H`-invariants systems), and through them on the earlier
modules of the series. From Mathlib it uses the extension of complexes along an
embedding of complex shapes (`HomologicalComplex.extend`,
`ComplexShape.Embedding.extendFunctor`, `extendXIso`, `extend_d_eq`,
`extendMap`) for the embedding `ComplexShape.embeddingUpNat` of `ℕ` into `ℤ`.
Names in the first two sections are in the namespace `Langlands.Cohomology`,
the others in `Langlands.Cohomology.DivisibleSystem`.

The Total module's `standardTotalSystemAugmentation N P ε K` has as target the
total complex, with rows `q < N`, of the system `K` placed in resolution
degree `0`; that module neither identifies this target with `K` nor maps it to
`K`. This module constructs that comparison. For `K` vanishing in degrees
`q ≥ N` it is a chain map, and in fact an isomorphism of `ℓ`-divisible
systems, onto `K` extended by zero to `ℤ`-graded complexes. Composing with the
totalized augmentation gives a morphism from the total complexes of the
standard resolutions to `K` extended to `ℤ`. The vanishing hypothesis is
discharged for the truncated smooth Godement systems with `N = D + 2`. The
morphism is not shown to be a quasi-isomorphism.

## Extension by zero is exact

`A` is an abelian category.

- `extendFunctor_preservesFiniteLimits` and
  `extendFunctor_preservesFiniteColimits` (instances): for any embedding
  `e : c.Embedding c'` of complex shapes, Mathlib's `e.extendFunctor A`
  preserves finite limits and finite colimits. Limits and colimits of
  complexes are checked degreewise. In a degree `i'` of the form `e.f i`,
  evaluation after extension is isomorphic to evaluation in degree `i`
  (`extendFunctorCompEvalIso`), which preserves them. In any other degree it
  is a functor to zero objects (`isZero_extend_X`), and such a functor
  preserves all limits and colimits.

## The comparison for one complex

`N : ℕ` and `L : CochainComplex A ℕ`. The abbreviations are:

- `columnZero A`: `(ChainComplex.single₀ A).mapHomologicalComplex (up ℕ)`,
  which places a cochain complex in resolution degree `0` as a double complex,
  the functor applied to `K` in the Total module's augmentation target.
- `columnRestriction N L`: the rows `q < N` of `(columnZero A).obj L` (the
  restriction along `upFinEmbedding N`), and `columnTotal N L`:
  `(upFinTotalFunctor A N).obj ((columnZero A).obj L)`, its total complex.
- `extendInt L`: `L.extend ComplexShape.embeddingUpNat`, the complex with
  `L.X q` in degree `q ≥ 0`, zero in negative degrees, and the differentials
  of `L`.

The constructions:

- `isZero_columnZero_X_X_succ`: the term `(q, r + 1)` of `(columnZero A).obj L`
  is zero.
- `columnSummand N L n q r h`, for `q < N` and `q - r = n`, is the map from
  the term `(q, r)` to the degree `n` term of `extendInt L`: for `r = 0` it is
  the inverse of Mathlib's identification `extendXIso` of `L.X q` with the
  degree `n = q` term of the extension, and for `r ≥ 1` it is `0` (its source
  is zero).
- `columnComparisonF N L n` is the map from the degree `n` term of the total
  complex of `columnRestriction N L` to the degree `n` term of `extendInt L`
  induced by these components (Mathlib's `totalDesc`);
  `ιTotal_columnComparisonF` and `columnSummand_zero` record its components.
- `columnComparisonF_comm`: if `L.X N` is zero, these maps commute with the
  differentials. On the summand `(q, 0)` the total differential is the row
  differential `L.d q (q + 1)` into the summand `(q + 1, 0)` when `q + 1 < N`,
  and there is no column part: the column shape is `ComplexShape.down ℕ`, so a
  column differential out of `(q, 0)` would go to some `(q, r')` with
  `r' + 1 = 0`, which does not exist (Mathlib's `d₂_eq_zero`). The summands
  `(q, r)` with `r ≥ 1` are zero, so the square holds on them trivially. When
  `q + 1 = N` the total complex has no row differential out of `(q, 0)`,
  while the differential of `extendInt L` is `L.d q N`, whose target `L.X N`
  is zero. This is the only place where the hypothesis is used: in degree
  `N - 1` the square compares `L.d (N - 1) N` with `0`.
- `columnComparison N L hL : columnTotal N L ⟶ extendInt L` is the chain map,
  for `hL : ∀ q, N ≤ q → IsZero (L.X q)` (only `q = N` is used for the chain
  map; `columnComparison_f` gives its components).
- `columnComparisonF_naturality`: the components are natural in `L`, against
  the totalized restricted map and Mathlib's `extendMap`.
- `isZero_columnTotal_X_of_neg`: the total complex is zero in negative
  degrees (its only possibly nonzero summands `(q, 0)` have degree `q ≥ 0`).
- `isIso_columnComparisonF` and the instance `isIso_columnComparison`: under
  `hL`, every component, and hence the chain map, is an isomorphism. In degree
  `n < 0` both sides are zero. In degree `n = q` with `q < N`, the inverse is
  `extendXIso` followed by the inclusion of the summand `(q, 0)`; every other
  summand of degree `q` is zero. In degree `n = q ≥ N` the total complex is
  zero (the Total module's `isZero_total_X`) and so is `L.X q` by `hL`.

## The comparison for ℓ-divisible systems

`ℓ : ℕ`.

- `isIso_of_isIso_tower_app`: a morphism of `ℓ`-divisible systems whose
  components at every level are isomorphisms is an isomorphism. The inverse
  has the inverse components; naturality and compatibility with the
  inclusions follow from those of the morphism.
- `extendSystem K`, for `K : DivisibleSystem (CochainComplex A ℕ) ℓ`, is
  `K.map (ComplexShape.embeddingUpNat.extendFunctor A)`, the system extended
  by zero to `ℤ`-graded complexes, using the exactness instances above and the
  parent module's `map`.
- `columnTotalSystemComparison N K hK`, for
  `hK : ∀ m q, N ≤ q → IsZero ((K.obj m).X q)`, is the morphism of
  `ℓ`-divisible systems
  `(K.map (columnZero A)).totalSystem N ⟶ K.extendSystem` with component
  `columnComparison N (K.obj m) (hK m)` at level `m`
  (`columnTotalSystemComparison_tower_app`). Its source is exactly the target
  of the Total module's `standardTotalSystemAugmentation N P ε K`. Naturality
  in `m` and compatibility with the inclusions are both
  `columnComparisonF_naturality`.
- `isIso_columnTotalSystemComparison` (instance) and
  `columnTotalSystemIso N K hK`: this morphism is an isomorphism of
  `ℓ`-divisible systems.

Now `P : A ⥤ A` is additive and preserves finite limits and finite colimits,
and `ε : P ⟶ 𝟭 A`, as in the Total module.

- `standardTotalSystemToExtend N P ε K hK` is
  `K.standardTotalSystemAugmentation N P ε ≫ K.columnTotalSystemComparison N hK`:
  a morphism from the total complexes, rows `q < N`, of the standard
  resolutions of `K` to `K` extended to `ℤ`. Unwinding the definitions, at
  level `m` and on the summand `(q, 0)`, `P((K m).X q)`, it is `ε` at
  `(K m).X q` followed by the inverse of `extendXIso`, and on the summands
  with `r ≥ 1` it is zero; this description is not stated as a lemma.

## Specializations

- `groupStandardTotalSystemToExtend N K hK`, for a commutative ring `k`, a
  finite group `Γ` and `K` in `Rep.{max w u v} k Γ`, is
  `standardTotalSystemToExtend` for `P = indResBot k Γ` and
  `ε = indResBotCounit k Γ`, with source the Total module's
  `groupStandardTotalSystem N K`.
- `quotientInvariantsTotalSystemToExtend N K H hK hN`, for `K` a system of
  complexes of smooth representations, `H` normal of finite index and `hK` the
  epi-on-invariants hypothesis of the Invariants module, is the previous map
  for the `H`-invariants system `K.quotientInvariantsComplexes H hK`, from the
  InvariantTotal module's `quotientInvariantsTotalSystem N K H hK`. The
  hypothesis `hN` is the vanishing of `K` itself in degrees `q ≥ N`; the
  invariants then vanish there because the additive functor of
  `H`-invariants preserves zero objects (`Functor.map_isZero`).
- `smoothGodementInvariantTotalSystemToExtend h T D H hterm hres`, with the
  hypotheses of the InvariantTotal module, is the morphism from
  `smoothGodementInvariantTotalSystem h T D H hterm hres` (Harris's
  `C_m^{•,H}` for the Library's stand-ins) to the `H`-invariant section
  complexes `smoothGodementTruncatedQuotientInvariantSectionsSystem h T D H
  hterm hres` extended to `ℤ`. The vanishing hypothesis, for `N = D + 2`, is
  the InvariantTotal module's
  `isZero_smoothGodementTruncatedQuotientInvariantSectionsSystem_obj_X`, so
  this morphism has no hypothesis beyond those of its source.

## Provenance and interpretation

Harris, *Galois properties of cohomological automorphic forms on GL(n)*,
J. Math. Kyoto Univ. 39-2 (1999), section 2, printed pp.305–306. Worker 61
read both pages in the scanned original.

1. The augmentation. Harris resolves each `M_m^{q,H}` by (2.5), which ends
   `⋯ → K_m^{-1,q,H} → M_m^{q,H} → 0`, and lets `C_m^{•,H}` be the simple
   complex of `K_m^{-•,•,H}` (p.306). The augmentation of (2.5) induces a
   morphism of complexes from `C_m^{•,H}` to `M_m^{•,H}`, which Harris does
   not write down; the quasi-isomorphism (2.6) `C_m^• → G_m^•(U(ẽ)_F̄)` is
   stated after the direct limit over `H`. `standardTotalSystemToExtend` and its
   specializations are the formal counterpart of this morphism: the
   totalized augmentation of the Total module followed by the comparison of
   this module. Since our complexes `K m` are `ℕ`-graded and the totals are
   `ℤ`-graded, the target is `K m` extended by zero to `ℤ`.
2. Indexing. The total degree `q - r` of the Total module puts
   `P((K m).X q)` in degree `q`, so the morphism preserves degrees; with
   Harris's labels this term `K_m^{-1,q,H}` would have degree `q - 1` (Total
   module, item 2).
3. The vanishing hypothesis. The comparison is a chain map only if the
   omitted row `N` contributes no differential, which the module ensures by
   requiring `K` to vanish in degrees `q ≥ N`; the same hypothesis makes the
   comparison an isomorphism. Harris's complexes have finite length (p.305),
   and for the truncated smooth Godement systems the hypothesis holds with
   `N = D + 2`. For the augmentation target this settles the Total module's
   point (its item 4) that the row restriction loses nothing when `K`
   vanishes in degrees `≥ N`: the restricted total is isomorphic to `K`
   extended to `ℤ`. The module proves nothing of this kind for the totals of
   the standard resolutions.

The comparison, its inverse, the exactness instances, the isomorphism of
systems, the composite morphisms and the discharge of the vanishing
hypothesis are derived. No hypothesis beyond those of the cited modules and
the vanishing in degrees `≥ N` is introduced.

## Scope

The module does not prove that `standardTotalSystemToExtend` or any of its
specializations is a quasi-isomorphism (this would need the exactness of the
standard resolutions, which the StandardResolution module does not prove),
that any term
is free or projective, or anything about different subgroups `H' ⊂ H`, the
direct limit over `H`, (2.6), (2.7) or Lemma 2.8. For systems with nonzero
terms in degrees `≥ N` it constructs no comparison, and it does not compare
the total complexes for different `N`.

Source registration: Harris 1999,
`harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`, SHA-256
`525a222c4489ee9d3fe86a52c6c17ffb30fcc7c31f24c16a64669e9615085b26`.

Dependencies are the modules named above, pinned to Lean 4.34.0 and Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`.
