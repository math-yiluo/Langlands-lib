# Cartan decomposition at the standard integral points of `GL_N`

The theorem `Langlands.BruhatTits.SpecialCompact.generalLinearIntegralCartan`
has exactly `GeneralLinearIntegralCartanStatement.{u}` as its type, the
specialization of Renard V.5.1(4) to `GL_N` over a nonarchimedean local field
`F` with the standard integral subgroup `K = GL_N(𝒪_F)`.
[Statement](GeneralLinearIntegralCartanStatement.md)
For a generic cocharacter `ν` of the diagonal torus, the theorem shows that
each double coset `K g K` contains exactly one element of the representative
set `C0Plus`. This set consists of the points `ϖ^c`, where `ϖ` is the common
order-one uniformizer and `c` runs over the cocharacters whose pairings with
the `ν`-positive roots are all nonnegative. The proof adds no hypothesis and
uses only the axioms `propext`, `Classical.choice` and `Quot.sound`.

The proof does not follow Renard's argument through Bruhat–Tits theory. It
moves the question into matrix coordinates and applies the Library's
elementary matrix Cartan decomposition, `Langlands.GeneralLinear.Cartan`.
[Matrix Cartan proof](../../Group/GL/CartanProof.md)
There `Iwasawa.torus ϖ a` is the diagonal matrix
`diag(ϖ^(a 0), …, ϖ^(a (N - 1)))` and `Iwasawa.integralRange v N` is the
subgroup of matrices that come from invertible matrices over the valuation
ring.

## Two public comparison lemmas

- `uniformizerUnit_isUniformizingElement`: the unit
  `SplitTorusValuation.uniformizerUnit F`, the uniformizer used by the
  uniformizer section, satisfies `Iwasawa.IsUniformizingElement`. Its
  valuation is below one, and every nonzero `x` has valuation equal to an
  integer power of it. The proof sends the valuation through the
  normalization `IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt` to
  `ℤₘ₀`. Order one of the uniformizer (`LocalField.ord_uniformizer`) puts it
  at `exp (-1)`. The exponent for `x` is then minus the logarithm of the
  normalized valuation of `x`.
- `rationalPointsEquiv_diagonalUniformizerSection`: for a cocharacter `c` of
  the split torus, the image of its uniformizer point in `GL_N(F)` under
  `rationalPointsEquiv` is `Iwasawa.torus ϖ (weights c)`. Here the weights are
  the integer coordinates `cocharacterCoordEquiv (Fin N) F c`. The proof
  rewrites the section as `SplitTorusValuation.cocharacterPoints`
  (`uniformizerSection_splitTorus`). It then reads the diagonal entries with
  `pointsEquiv_diagonalTorus` and `coords_cocharacterPoints`. The
  off-diagonal entries are zero.
  [Uniformizer and chamber](../../Representation/Plancherel/RenardUniformizerSection.md)

## Sorting the generic weights

The private lemmas prepare the permutation that orders the coordinates.

- `nonnegative_iff_antitone`: let `p` be a permutation of `Fin N` with
  `weights ν ∘ p` strictly decreasing. A cocharacter `c` pairs nonnegatively
  with every `ν`-positive relative root if and only if `weights c ∘ p` is
  antitone. The relative roots of the diagonal torus are the roots
  `e_i - e_j` (`i ≠ j`) of the root datum `GeneralLinear.rootDatum`, by
  `isRootDatumOf_rootDatum`. Each pairs with a cocharacter as a difference of
  two weights (`latticePairing_rootDatum_root`). For `i < j` the root at
  `(p i, p j)` is `ν`-positive, which gives the forward direction. A positive
  root at `(p i, p j)` forces `i < j` by strict monotonicity, which gives the
  converse.
  [Relative roots](../../GroupScheme/Rational/GeneralLinearSimpleRootsProof.md)
- `permGL_mem_integralRange`: a permutation matrix over `F` is the image of
  the same permutation matrix over `𝒪[F]` (`map_permGL`), so it lies in the
  integral subgroup.
- `permGL_conj_torus`: for `P = permGL F p.symm`, conjugation
  `P * Iwasawa.torus ϖ c * P⁻¹` equals `Iwasawa.torus ϖ (c ∘ p)`. This is
  `permGL_conj_diagonalTorusUnits`.

## The bijection

The private theorem `cartan_bijective` carries the main argument. Let `p`
be `Tuple.sort (fun i => -weights ν i)`. By `Tuple.monotone_sort` the tuple
`weights ν ∘ p` is antitone. A cocharacter of the diagonal torus is generic
exactly when its weights are injective
(`isGenericCocharacter_diagonalTorus_iff`), so this tuple is strictly
decreasing.

Let `E` be `rationalPointsEquiv` followed by conjugation by
`P = permGL F p.symm`. An element `g` lies in `K` if and only if `E g` is
integral. This uses `mem_standardIntegralModel_integralPoints_iff` and the
integrality of `P` and `P⁻¹`.
[Integral points](../../GroupScheme/IntegralModel/GeneralLinearStandardPoints.md)
By the two comparison lemmas, `E` maps the uniformizer point of `c` to
`Iwasawa.torus ϖ (weights c ∘ p)`.

- Injectivity. Take two representatives with cocharacters `c` and `d` and
  the same double coset. Then `ϖ^d = k ϖ^c l` with `k, l ∈ K`. Applying `E`
  gives an equation between two sorted diagonal matrices with integral
  factors. Both exponent tuples are antitone by `nonnegative_iff_antitone`.
  `Cartan.exponent_unique` gives `weights c ∘ p = weights d ∘ p`. Since `p`
  is surjective and the weight map is an equivalence, `c = d`.
- Surjectivity. For `g`, `Cartan.exists_cartan` writes
  `E g = k * Iwasawa.torus ϖ a * l` with `a` antitone and `k, l` integral. Let
  `c = cocharacterOfWeights F (a ∘ p.symm)`. Then `weights c ∘ p = a`, so `c`
  is nonnegative on the positive roots by `nonnegative_iff_antitone`. Its
  uniformizer point lies in the representative set. Applying `E⁻¹` gives
  `g = E⁻¹ k · ϖ^c · E⁻¹ l` with both outer factors in `K`. Hence `g` lies in
  the double coset of `ϖ^c`.

The closing theorem `generalLinearIntegralCartan` introduces the field, its
instances, `N` and `ν`, and then applies `cartan_bijective`.

The statement follows David Renard, *Représentations des groupes réductifs
p-adiques*, French edition dated 9 July 2026, Theorem V.5.1(4), printed
p. 122 / PDF p. 128, with the representative set of V.3.23, printed p. 117 /
PDF p. 123.
