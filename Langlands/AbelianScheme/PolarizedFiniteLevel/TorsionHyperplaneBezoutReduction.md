# Reduction of the torsion-hyperplane count to the Bezout count

This module defines the linear system of Mumford's argument and proves the
conditional theorem `card_torsionHyperplaneSections_le_of_bezout`, two variants, and
the conditional form `cubicTorsionHyperplaneBound_of_bezout` of the target. All of
them take the Bezout statement `Picard.LinearSystemBaseLocusBezoutStatement` as a
hypothesis `hC`. The last theorem, `cubicTorsionHyperplaneBound_of_symmetricPullback`,
discharges `hC` with the published proof `Picard.linearSystemBaseLocusBezout`.

## Definitions and base locus

Throughout, `a` is a datum over a field `K` with abelian scheme `A = a.abelian` and
cubic bundle `M = a.cubicBundle`. Also fixed are a morphism
`i : A.X.left ⟶ ProjectiveSpace K m` and an isomorphism `eM : i^* 𝒪(1) ≅ M`.

- `torsionHyperplaneSection a i eM f` is the section of `M = M^1` obtained by
  pulling back the linear section `f / 1` of `𝒪(1)` along `i` and transporting it
  through `eM`. By `mem_sectionOpen_torsionHyperplaneSection_iff`, a point `x` lies
  in its generation open exactly when `f ∉ (i x).asHomogeneousIdeal`. This is
  `mem_trivializationOpen_isoPullbackSection_twistOne_iff` from
  `ProjectiveSpace.LinearPullbackBaseLocus`.
- `torsionBezoutSystem a i eM eB` takes an isomorphism `eB : [n]^* M ≅ M^(n·n)`,
  where `[n]` is `GroupScheme.multiplication A.toGrp n` on underlying schemes. It is
  `linearPullbackSystem i M eM [n] eB (σ pt)` with `σ = η[A.X].left` the identity
  section. That is the set of sections of `M^(n·n)` obtained by pulling back, along
  `i` and then `[n]`, the linear forms through `i(σ pt)`.
- `baseLocus_torsionBezoutSystem` assumes that `i` is a closed immersion over `K`.
  It states that the common zero locus of `torsionBezoutSystem a i eM eB` is
  `TorsionPointFibre A n`. Proof: `σ ≫ i` is a `K`-point of `ℙᵐ` over `K`, because
  `η` is a morphism over the base. A closed immersion is injective on points.
  Then `baseLocus_linearPullbackSystem` identifies the base locus with
  `[n]⁻¹{σ pt}`, and that set is `TorsionPointFibre A n` by definition.

## Main theorem

Fix the following data:
- an algebraically closed field `K`, and `g d n : ℕ` with `0 < g` and
  `(n : K) ≠ 0`;
- a datum `a : Datum P (Spec K) g d n` with abelian scheme `A = a.abelian` and
  cubic bundle `M = a.cubicBundle`;
- a closed immersion `i : A.X.left ⟶ ProjectiveSpace K m` over `K`, that is,
  `i ≫ projectiveSpaceToSpec K m = A.X.hom`;
- an isomorphism `eM : i^* 𝒪(1) ≅ M`;
- an isomorphism `eB : [n]^* M ≅ M^(n·n)`, where `[n]` is
  `GroupScheme.multiplication A.toGrp n` on underlying schemes;
- the equation `hcoeff`: the degree-`g` coefficient of
  `lineBundleEulerPolynomial A.X.hom M g` is `6^g · d`;
- a degree-one form `f` such that `f ∉ (i x).asHomogeneousIdeal` for some
  point `x`.

Under these hypotheses the theorem gives

`Nat.card (TorsionHyperplaneSections i f n) ≤ 6^g · d · g! · n^(2g-2)`.

Here `TorsionHyperplaneSections i f n` is the published subtype of `n`-torsion
`K`-sections whose point lies on the hyperplane `f = 0`. That set is the one
counted in the target.

## Proof

1. The `FieldAbelianSchemeGeometry` results show that `A.X.left` is
   integral, Noetherian and separated, and that its topological Krull dimension
   is `g`. The structure morphism is proper because `A` is an abelian scheme.
   Mathlib supplies an `Infinite K` instance because `K` is algebraically
   closed.
2. Let `s = torsionHyperplaneSection a i eM f`. By its membership lemma, the
   nondegeneracy hypothesis on `f` makes the generation open of `s` nonempty.
3. Let `S = torsionBezoutSystem a i eM eB`. By `baseLocus_torsionBezoutSystem`,
   its base locus is `TorsionPointFibre A n`.
4. The two other hypotheses of the Bezout statement come from the module
   `TorsionPointFibre`, using `(n : K) ≠ 0`:
   - `torsionPointFibre_finite` shows the base locus is finite;
   - `torsionPointFibre_isClosed_singleton` shows each of its points is closed.

   `field_closedPoint_stalk_dimension` then gives stalk dimension `g` at each
   such point.
5. Apply `hC` with `e = g`, `p = 1`, `q = n·n` and rewrite with `hcoeff`. The
   points of the base locus outside the generation open of `s` are then bounded
   in number by `g! · 1 · (n·n)^(g-1) · 6^g · d`, and this equals
   `6^g · d · g! · n^(2g-2)`.
6. Send a torsion section `x` to the point `levelToTorsionPointFibre A n x`. That
   point lies in the base locus by step 3. If `x` is on the hyperplane, the point
   lies outside the generation open of `s` by step 2. The map is injective by
   `levelToTorsionPointFibre_injective`, so the target count is at most the
   bound from step 5.

## Variant with squared Euler characteristics

`card_torsionHyperplaneSections_le_of_bezout_of_eulerCharacteristic_sq` has the
same hypotheses and conclusion, except that `hcoeff` is replaced by two
assumptions:
- `hsq`: `χ(M^k)^2 = (6^g · d)^2 · k^(2g)` in `ℤ` for every positive `k` and
  every finite-cohomology witness;
- `hpos`: `χ(M) ≥ 0`.

Here `χ` is the actual `eulerCharacteristic` of `tensorPow M k` over `A.X.hom`.
The proof derives `hcoeff` from these two assumptions using
`lineBundleEulerPolynomial_coeff_eq_of_eulerCharacteristic_sq` from the module
`Picard.LineBundleEulerPolynomialSquare`. That lemma needs `A.X.left` Noetherian
and separated, with topological Krull dimension at most `g`, which the
`FieldAbelianSchemeGeometry` results supply. The variant then applies the main
theorem. These are the values that the Euler-square formula `χ(L)^2 = deg φ_L`
(Milne, *Abelian Varieties*, Thm. 13.3 (a)) supplies for `L = M^k`, together
with `deg φ_(M^k) = k^(2g) deg φ_M` and `χ(M) = 6^g · d`.

## Variant with the symmetric multiplication pullback

`card_torsionHyperplaneSections_le_of_bezout_of_symmetricPullback` has the hypotheses
of the main theorem, except that the isomorphism `eB` is replaced by a hypothesis
`hB : GroupScheme.FieldSymmetricMultiplicationPullbackStatement`. That statement says:
on a commutative smooth proper geometrically connected group scheme over a field, a
line bundle `L` with `[-1]^* L ≅ L` satisfies `[n]^* L ≅ L^(n·n)` for every `n > 0`.

Proof. `(n : K) ≠ 0` forces `0 < n`. The abelian scheme `A` is smooth, proper and
geometrically connected by its instances. The cubic bundle is symmetric by
`Datum.nonempty_pullback_neg_cubicBundle_iso` (module `CubicBundleSymmetry`). So `hB`
gives `eB : [n]^* M ≅ M^(n·n)`, and the main theorem applies.

## Conditional form of the target

`cubicTorsionHyperplaneBound_of_bezout` proves
`CubicTorsionHyperplaneBoundStatement` from three hypotheses:
- `hC : LinearSystemBaseLocusBezoutStatement`;
- `hB : GroupScheme.FieldSymmetricMultiplicationPullbackStatement`;
- `hA`: for every `P`, every algebraically closed field `K`, all `g d n` with `0 < g`
  and `0 < d`, and every datum `a : Datum P (Spec K) g d n`, the degree-`g`
  coefficient of `lineBundleEulerPolynomial A.X.hom a.cubicBundle g` is `6^g · d`.

Proof. Introduce the data of the target. The supplied `Nonempty` isomorphism gives
`eM`, and the nondegeneracy hypothesis of the target applied to the nonzero form `f`
gives a point off the hyperplane `f = 0`. The target counts exactly the subtype
`TorsionHyperplaneSections i f n` (by definition). Then apply the previous variant
with `hcoeff = hA P K g d n hg hd a`.

`cubicTorsionHyperplaneBound_of_symmetricPullback` takes only `hB` and `hA`. It
applies `cubicTorsionHyperplaneBound_of_bezout` with
`hC = Picard.linearSystemBaseLocusBezout`, the published proof of the Bezout
statement in the module `Picard.LinearSystemBaseLocusBezoutProof`.

## Scope and provenance

This is an internal reduction step for the published target
`Langlands.AbelianScheme.PolarizedFiniteLevel.CubicTorsionHyperplaneBoundStatement`
(Mumford–Fogarty–Kirwan, *Geometric Invariant Theory*, 3rd ed., Prop. 7.7). It
follows Mumford's argument: the `n`-torsion is the base locus of the pullback
under `[n]` of the hyperplanes through the origin, which lies in `|M^(n²)|`, and
the intersection with a hyperplane `f = 0` is then bounded by an intersection
number.

These theorems do not prove the target. Their remaining inputs are hypotheses:
- the Bezout statement `hC` (except in the last theorem, which uses its published
  proof);
- the isomorphism `[n]^* M ≅ M^(n·n)`, or the statement `hB` from which it follows;
- the Euler-coefficient equation `hcoeff` or `hA` (or, in the squared variant, the
  squared Euler characteristics `hsq` and the sign condition `hpos`).
