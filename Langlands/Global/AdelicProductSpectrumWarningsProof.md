# Proof of the support warnings for spectra of products and adelic levels

`Langlands.Global.adelicProductSpectrumWarnings.{u}` proves the published
`Langlands.Global.AdelicProductSpectrumWarningsStatement.{u}` from module
`Langlands.Global.AdelicProductSpectrumWarningsStatement`. The statement records Conrad's
warnings in the proof of Theorem 3.6, printed pp.7–8 of *Weil and Grothendieck
approaches to adelic points*. They concern the spectrum of an infinite product
of rings, and Moret-Bailly's example. The proof below follows the Lean route.
It does not reproduce Conrad's text, which only asserts these facts in passing.
The registered source is `conrad-2011-weil-grothendieck-adelic-points`, SHA256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.

## A ring presented as a product

The section `General` works with a commutative ring `A`, a family of
commutative rings `B i`, a ring isomorphism `e : A ≃+* ∀ i, B i` and maps
`p i : A →+* B i` satisfying `p i a = e a i` (hypothesis `hp`). The same
lemmas therefore apply to the literal product, with `e` the identity and
`p = Pi.evalRingHom`, and to the published adelic levels.

- `productSpectrum_p_surjective`: each `p i` is surjective, because
  `e.symm (Pi.single i b)` maps to `b`.
- `productSpectrum_p_idem`: the idempotent `e.symm (Pi.single i 1)` maps to `1`
  under `p i` and to `0` under `p j` for `j ≠ i`.
- `productSpectrum_isOpenImmersion`: `ofHom (p i)` is the composite of the ring
  isomorphism `e.toCommRingCatIso.hom` and `Pi.evalRingHom B i`. Hence
  `Spec.map (ofHom (p i))` is the spectrum map of the evaluation followed by
  the spectrum isomorphism induced by `e`.
  Mathlib already proves that the evaluation map is an open immersion
  (`Mathlib/AlgebraicGeometry/Limits.lean`).
- `productSpectrum_disjoint`: if a prime of `A` were the pullback of primes
  along both `p i` and `p j` with `i ≠ j`, it would contain the idempotent for
  `i`, because `p j` sends it to `0`. Pulled back along `p i`, the same
  idempotent maps to `1`, so the prime would contain `1`.
- `productSpectrum_range_nonempty`: a nontrivial factor has a prime ideal, and
  its pullback lies in the range.

## Covering and compactness

- `productSpectrum_finite_support_of_mem_span`: every element of the ideal
  spanned by the idempotents has only finitely many nonzero coordinates. The
  proof is by induction on the span.
- `productSpectrum_iUnion_ne_univ`: suppose infinitely many factors are
  nontrivial. Then `1` has infinitely many nonzero coordinates, so the ideal of
  idempotents is proper. A maximal ideal containing it lies in no factor range.
  If it were the pullback of a prime of `B i`, it would contain the idempotent
  for `i`, whose image under `p i` is `1`.
- `productSpectrum_iUnion_eq_univ`: if the set `T` of nontrivial factors is
  finite, the idempotents indexed by `T` sum to `1`, because every other factor
  is the zero ring. Every prime `z` therefore omits some idempotent `ε_i` with
  `i ∈ T`. By `productSpectrum_mem_range_iff_ker_le`, the range of a
  surjection's spectrum map is the zero locus of its kernel; that lemma uses
  Mathlib's `range_comap_of_surjective`. Every `a` in the kernel of `p i`
  satisfies `a ε_i = 0 ∈ z`, and `ε_i ∉ z`, so `a ∈ z`. Hence `z` lies in the
  range of the `i`th factor.
- `not_isCompact_iUnion_of_pairwise_disjoint` is a general topological lemma.
  Infinitely many pairwise disjoint nonempty open sets have a noncompact union,
  because a finite subcover would miss one of the nonempty sets.
  `productSpectrum_not_isCompact` applies it to the factor ranges. These ranges
  are open by `IsOpenImmersion.isOpen_range`.

## Scheme-theoretic density

`productSpectrum_eq_zero_of_factor` turns a factorization
`f ≫ Spec.map (Ideal.Quotient.mk I) = Spec.map (ofHom q)` into a ring
factorization. `Spec.preimage f` composed with the quotient map equals `q`,
which is checked after `Spec.map_injective`. So `q` kills `I`.
`productSpectrum_dense` applies this to every `p i`. Every coordinate of an
element of `I` then vanishes, so `I = ⊥` by injectivity of `e`.

## The cofinite-irreducible ideal for local factors

In the section `Local`, every `B i` is local. Cofinitely many of them have a
maximal ideal spanned by an irreducible element.

- `productSpectrum_mem_span_iff`, forward direction: by span induction,
  irreducible elements are nonunits, and the set of elements with cofinitely
  nonunit coordinates is closed under the ideal operations.
- `productSpectrum_mem_span_iff`, reverse direction: choose a coordinatewise
  factorization `p j a = γ j * β j`. At each coordinate where `p j a` lies in a
  maximal ideal spanned by an irreducible `ϖ`, take `β j = ϖ`. Elsewhere take
  `β j = 1` and `γ j = p j a`. Then `e.symm β` is one of the generators, and
  `a = e.symm γ * e.symm β`.
- `productSpectrum_map_eq_top`: at a fixed `i`, modify the chosen
  irreducibles `β` by `Function.update β i 1`. The resulting element is still a
  generator, since only one coordinate changed, and its image under `p i` is
  `1`.
- `productSpectrum_not_fg`: suppose the ideal were spanned by a finite set `s`.
  By the membership characterization, each element of `s` has cofinitely
  nonunit coordinates. `Filter.eventually_all_finset` and an infinite index give
  one index `j` at which all of them are nonunits. Their images then span an
  ideal inside the maximal ideal of `B j`, while `productSpectrum_map_eq_top`
  says the image ideal is the unit ideal.
- `localFactorSpectrumWarnings_of_ringEquiv` assembles the nine clauses of
  `LocalFactorSpectrumWarnings`. Local rings are nontrivial, so an infinite
  index gives infinitely many nontrivial factors.

`productFactorSpectrum` and `localProductSpectrumWarnings` specialize these
results to the literal product, with `e = RingEquiv.refl` and `hp` by `rfl`.

## Moret-Bailly's example

`closedSubschemeSupportWarning_of` proves `ClosedSubschemeSupportWarning` for
any element `r` of a product that satisfies three conditions. Each coordinate is
nilpotent, the coordinates indexed by `N` are nonzero, and `r` itself is not
nilpotent.

- The range of the quotient map's spectrum is the zero locus of `r`, by the
  kernel description above and `Ideal.mk_ker`.
- Every factor point lies in it, because a prime of `R i` contains the nilpotent
  `r i`.
- A factorization at `i ∈ N` would make `r i = 0` by
  `productSpectrum_eq_zero_of_factor`.
- If the zero locus of `r` were everything, `r` would lie in every prime ideal,
  hence in the nilradical (`nilradical_eq_sInf`), so `r` would be nilpotent.
- The zero locus is closed, since the quotient's spectrum map is a closed
  immersion (`IsClosedImmersion.spec_of_surjective`) and closed immersions have
  closed range. It contains the union of the factor ranges, so it contains the
  closure of that union. Since the zero locus is not everything, neither is the
  closure.

`moretBaillyDiagonal` applies this lemma with
`R n = k[X]/(X^(n+1))` and `r n` the class of `X`.

- The class of `X` has `(n+1)`st power zero.
- For `n ≥ 1` the class is nonzero, because `X^(n+1)` does not divide `X`
  (`moretBailly_not_dvd`, by comparing degrees).
- If `r^m = 0`, then at coordinate `m` the polynomial `X^(m+1)` would divide
  `X^m`, which is impossible.

## Adelic levels

`numberFieldLevelSpectrumWarnings` uses the published ring isomorphism
`numberFieldLevelFactorRingEquiv K S` together with
`numberFieldLevelFactorProjection K S`. The compatibility `hp` holds by `rfl`.
The finite places outside `S` form an infinite type
(`numberField_finitePlaces_infinite`). The factors at infinite places and at
places in `S` form the range of a map from a finite type. Every remaining factor
is `v.adicCompletionIntegers K`, a discrete valuation ring. There
`IsDiscreteValuationRing.exists_irreducible` and
`IsDiscreteValuationRing.irreducible_iff_uniformizer` supply an irreducible
generator of the maximal ideal. `curvePlaceLevelSpectrumWarnings` follows the
same steps with `curvePlaceLevelFactorRingEquiv k F S`,
`functionField_places_infinite` and `curvePlaceCompletionIntegers`. It uses no
hypothesis on the constant field `k` beyond those in the statement.

`adelicProductSpectrumWarnings` is the conjunction of these five theorems.
It retains arbitrary commutative factor rings and index types in universe `u`,
every field in the diagonal example, every number field and finite level set,
and every function field over an arbitrary constant field with a finite level
set. The proof adds no perfectness, separability, finiteness of constants,
noetherian or characteristic hypothesis. It uses the published level rings,
factor types and factor projections, with their product presentations only
serving to prove the assertions about those actual rings and maps.
