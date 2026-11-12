# Freeness of the prime-adic Tate module from free torsion levels

This helper module works in `Langlands.GroupScheme.Tate.PrimeAdic` for an
arbitrary commutative group object `G : Grp (Over S)`, a test object
`T : Over S`, a prime `p` with `Fact p.Prime`, and a rank `r : ℕ`. It
concerns the published actual torsion levels `Level G T (p ^ n)` and the
published inverse limit `Integral G T p` and its rationalization
`Rational G T p` from [`PrimeAdic`](PrimeAdic.md). It proves that if every
prime-power level is a free `ZMod (p ^ n)`-module of rank `r` with
`(p ^ n) ^ r` elements, then the integral module is free of rank `r` over
`ℤ_[p]` and the rational module has dimension `r` over `ℚ_[p]`.

The two level hypotheses are

```text
hcard : ∀ n, Nat.card (Level G T (p ^ n)) = (p ^ n) ^ r
hfree : ∀ n, Nonempty ((Fin r → ZMod (p ^ n)) ≃ₗ[ZMod (p ^ n)] Level G T (p ^ n))
```

where the `ZMod (p ^ n)` action is the published `levelZModModule`. The
level equivalences in `hfree` are arbitrary and need not be compatible
with the transitions; compatibility is constructed here.

## Residue bases

`IsLevelBasis G T p n b` is an internal proposition-valued definition. For
`b : Fin r → Level G T (p ^ n)` it says that the coordinate map
`c ↦ ∑ i, c i • b i` from `Fin r → ZMod (p ^ n)` to the level is bijective,
that is, `b` is a basis of the level as a `ZMod (p ^ n)`-module, written
with the existing scalar action. `exists_isLevelBasis` shows that the
images `e (Pi.single i 1)` of the standard vectors under a linear
equivalence `e` form such a basis.

## Surjective transitions

`level_finite` derives finiteness of every level from `hcard`, since
`(p ^ n) ^ r` is nonzero.

`transition_succ_surjective` proves that the actual successive transition
`transition G T (pow_dvd_pow p (Nat.le_succ n))` is surjective. The proof
does not use `hfree`. The transition raises the underlying section to the
power `p ^ (n + 1) / p ^ n = p`. Hence every element of its kernel has an
underlying section killed by `p`, and the kernel injects into the level
`p ^ 1`, which has `p ^ r` elements. The index formula
`Nat.card ker * index ker = Nat.card source`, together with
`AddSubgroup.index_ker`, gives `p ^ r * (p ^ n) ^ r ≤ p ^ r * #range`. So
the range has at least `(p ^ n) ^ r = #target` elements and equals the
whole target by `AddSubgroup.eq_top_of_le_card`.

`isLevelBasis_transition` shows that applying the successive transition to
a residue basis at level `p ^ (n + 1)` gives a residue basis at level
`p ^ n`. The coordinate map is surjective: lift a target point through the
surjective transition, write the lift in the given basis, and reduce the
coefficients by `ZMod.castHom`, using the published `transition_zmod_smul`.
Since source and target of the coordinate map both have `(p ^ n) ^ r`
elements, `Function.Surjective.bijective_of_nat_card_le` gives
bijectivity.

## Compatible bases by Kőnig's lemma

`exists_compatible_isLevelBasis` produces residue bases `b n` at every
level with `transition (b (n + 1) i) = b n i` for all `n` and `i`. The
sets `X n` of residue bases at level `p ^ n` are finite by `level_finite`
and nonempty by `hfree` and `exists_isLevelBasis`.
`isLevelBasis_transition` supplies maps `X (n + 1) → X n`. They form a
functor `ℕᵒᵖ ⥤ Type u` through `Functor.ofOpSequence`. Mathlib's
`nonempty_sections_of_finite_inverse_system`, a form of Kőnig's lemma,
gives a compatible section. Its successive compatibility is read off with
`Functor.ofOpSequence_map_homOfLE_succ`.

## The integral equivalence

`linearEquivOfCompatibleBases` constructs, from compatible residue bases,
a `ℤ_[p]`-linear equivalence `(Fin r → ℤ_[p]) ≃ₗ[ℤ_[p]] Integral G T p`.
Its level maps are `Fintype.linearCombination ℤ_[p] (b n)`, which send `c`
to `∑ i, PadicInt.toZModPow n (c i) • b n i` for the published
`levelModule` scalar action. These maps are compatible with the
transitions by `transition_smul` and the compatibility of the bases. The
published universal property `lift` assembles them into a linear map `φ`.

- Injectivity: if `φ c = 0`, every level coordinate vanishes. Bijectivity
  of the residue coordinate map gives `PadicInt.toZModPow n (c i) = 0` for
  all `n`, so `c i = 0` by `PadicInt.ext_of_toZModPow`.
- Surjectivity: for `y` in the limit, let `c n` be the residue
  coordinates of `evaluation G T p n y` in the basis `b n`. Comparing
  `evaluation_transition` with the compatible bases and using uniqueness
  of residue coordinates shows that `ZMod.castHom` maps `c (n + 1) i` to
  `c n i`. Induction gives compatibility of all reductions `c k₂ i` to
  `c k₁ i` for `k₁ ≤ k₂`. The ring maps `ℤ[X] → ZMod (p ^ k)` that send
  `X` to `c k i` are then compatible, so `PadicInt.lift` gives
  `x i : ℤ_[p]`, the image of `X`, with `PadicInt.toZModPow n (x i) = c n i`
  by `PadicInt.lift_spec`. Then `φ x = y` coordinatewise.

`integral_linearEquiv_of_level` combines these steps:
`hcard` and `hfree` imply
`Nonempty ((Fin r → ℤ_[p]) ≃ₗ[ℤ_[p]] Integral G T p)`.

## The rational dimension

`rational_finrank_of_linearEquiv` takes such an equivalence and proves
`FiniteDimensional ℚ_[p] (Rational G T p)` and
`Module.finrank ℚ_[p] (Rational G T p) = r`. The integral module is free
and finite over `ℤ_[p]` by transport along the equivalence. The rational
module is by definition `ℚ_[p] ⊗[ℤ_[p]] Integral G T p`. Its finiteness is
the base-change instance, and `Module.finrank_baseChange`,
`LinearEquiv.finrank_eq` and `Module.finrank_fin_fun` compute its rank.

## Provenance and scope

This module is an internal derived construction. It contains no new
assertion from the literature. It is the inverse-limit step of the
argument behind Edixhoven–van der Geer–Moonen, *Abelian Varieties*
(preliminary draft built 2012-02-08), Chapter X (10.1)–(10.3), printed
pp.141–142 (registered source
`edixhoven-vandergeer-moonen-abelian-varieties-draft`). There, `T_ℓ` is
asserted to be isomorphic to `ℤ_ℓ^(2g)`, given the structure of the
finite torsion levels. This module supplies the passage from finite levels
to the inverse limit by choosing compatible bases with Kőnig's lemma. This
route need not match the argument in the source. The source
correspondence for the geometric statement is in
[`GeometricPrimeAdicRankStatement`](GeometricPrimeAdicRankStatement.md).

The hypotheses are on the actual torsion levels only. No abelian-scheme
structure, characteristic condition or field is used, and the
results hold for any commutative group object satisfying `hcard` and
`hfree`. The chosen equivalence is noncanonical. No continuity,
compactness, monodromy compatibility, or statement at levels other than
powers of `p` is asserted.
