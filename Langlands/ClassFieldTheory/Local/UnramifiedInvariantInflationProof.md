# Inflation compatibility of the explicit finite unramified invariant

Author: Worker 272.

The theorem
`Langlands.ClassFieldTheory.Local.unramifiedInvariantInflationCompatibility.{u}`
proves exactly the published proposition
`Langlands.ClassFieldTheory.Local.UnramifiedInvariantInflationCompatibility.{u}`
from [`UnramifiedInvariantCompatibilityStatement`](UnramifiedInvariantCompatibilityStatement.md).
For every prime `p`, every compatible tower `F ⊂ L ⊂ M` of
`PadicField.{u} p` carriers with `L/F` and `M/F` finite Galois and unramified
in the canonical absolute-index convention, every pair of arithmetic
coordinates `χL` on `Gal(L/F)` at degree `[L:F]` and `χM` on `Gal(M/F)` at
degree `[M:F]`, and every class `x` in the actual ordinary relative group
cohomology `H²(Gal(L/F), Lˣ)`, it proves

```text
unramifiedH2Invariant F M hFM χM (relativeInflation F L M 2 x)
  = unramifiedH2Invariant F L hFL χL x.
```

The theorem type is the published proposition itself; no hypothesis is added.
The statement pair and every imported pair are unchanged. Degree one is not
treated separately: every lemma below holds for all positive moduli, and the
moduli `[L:F]` and `[M:F]` are positive because the extensions are finite.

The final theorem applies the auxiliary result
`UnramifiedInflation.inflationCompatibility_of_normalization` to the
published theorem `cyclicClassNormNormalization.{u, u}` from
[`CyclicClassNormProof`](CyclicClassNormProof.md). That theorem proves the
published proposition `CyclicClassNormNormalization`: the existing cyclic
norm comparison `cyclicH2NormEquiv` sends the positive carry class of a base
unit `a` to the class of `a` in the norm quotient. The auxiliary result takes
this proposition as an explicit argument only so that the reduction below can
be stated independently. The final theorem has no premise.

All helper declarations are in the namespace
`Langlands.ClassFieldTheory.Local.UnramifiedInflation`. In the formulas below,
unit groups are written multiplicatively. The Lean coefficient module
`Additive Mˣ` is additive, so `a ^ k` there becomes `k • a`.

## Implemented proof

### 1. Arithmetic Frobenius restricts along the tower

The section `Residue` works with the canonical normed-field structure of `F`
used by `IsArithmeticUnramifiedCoordinate`. Integer rings and residue fields
are the existing `LocalGalois.extensionIntegers`, defined by spectral norm at
most one over `F`.

- `towerIntegerMap` is the field inclusion `L → M` restricted to these
  integer rings. It is well defined because Mathlib's
  `spectralNorm.eq_of_tower` gives
  `spectralNorm F M (ι y) = spectralNorm F L y` for `y ∈ L`, using only that
  `M/F` is algebraic.
- `towerIntegerMap_isLocalHom`: the maximal ideal of either integer ring is
  the set where the spectral norm is less than one. The same equality of
  spectral norms shows that a nonunit maps to a nonunit, so the map is
  local. `towerResidueMap` is the induced map
  `IsLocalRing.ResidueField.map` of residue fields. Being a ring
  homomorphism between fields, it is injective.
- `towerResidueMap_residueHom`: for `σ ∈ Gal(M/F)` and every residue class
  `y` of `L`, the residue action of `σ.restrictNormal L` followed by
  `towerResidueMap` equals `towerResidueMap` followed by the residue action of
  `σ`. After lifting `y` to an integer, this is
  `AlgEquiv.restrictNormal_commutes`.
- `restrictNormal_frobenius`: suppose `σL` acts on the residue field of `L`
  by `y ↦ y ^ q`, and `σM` acts on the residue field of `M` by `z ↦ z ^ q`.
  Here `q` is the cardinality of the residue field of `F`. Suppose also that
  the residue action of `Gal(L/F)` is injective. Then
  `σM.restrictNormal L = σL`. Indeed, applying the commutation identity, the
  Frobenius property of `σM`, multiplicativity of `towerResidueMap` and the
  Frobenius property of `σL` shows that the residue actions of both
  elements agree after the injective `towerResidueMap`. Injectivity of the
  residue action of `Gal(L/F)` then identifies the two elements.

In the final step, `σL` and `σM` are the positive generators
`cyclicCoordinateGenerator χL = χL⁻¹(+1)` and
`cyclicCoordinateGenerator χM = χM⁻¹(+1)`. Both Frobenius properties and the
injectivity on `L` are components of the two hypotheses
`IsArithmeticUnramifiedCoordinate`. The injectivity component for `M` is not
needed.

### 2. Compatible cyclic coordinates

The section `Coordinates` works over an arbitrary field `K` with `L/K` normal.

- `coordinate_restrict`: let `n ∣ m`, and let `χL : Gal(L/K) ≃ ℤ/n` and
  `χM : Gal(M/K) ≃ ℤ/m` be equivalences whose positive generators correspond
  under `restrictNormal`. Then `χL(g|L)` is the reduction modulo `n` of
  `χM(g)` for every `g ∈ Gal(M/K)`. Indeed, the generator of `M/K` generates
  its group (`cyclicCoordinateGenerator_generates`), so write
  `g = σM ^ k` with `k ∈ ℤ`. Normal restriction is a group homomorphism, so
  `g|L = σL ^ k`. Hence `χL(g|L) = k mod n`, while `χM(g) = k mod m`, and
  `ZMod.castHom` sends the integer cast `k` to `k`.
- `coordinate_restrict_val` restates this for standard representatives:
  `val(χL(g|L)) = val(χM(g)) mod n`, using `ZMod.val_natCast`.

### 3. Inflation of a carry class

The section `Cocycle` uses the published carry cocycle from
[`CyclicClass`](CyclicClass.md). For a character `χ` with values in `ℤ/n`
and a base unit `a`, it is

```text
c_a(g, h) = a ^ ⌊(val χ(g) + val χ(h)) / n⌋,
```

and `cyclicClass K L χ a` is its class in actual relative `H²`.

- `carry_identity`: for natural numbers `n > 0`, `m = n k`, `i` and `j`,

  ```text
  k⌊(i+j)/m⌋ + ⌊((i+j) mod m)/n⌋ = ⌊(i mod n + j mod n)/n⌋ + ⌊i/n⌋ + ⌊j/n⌋.
  ```

  The proof multiplies both sides by `n` and expands each quotient by
  division with remainder (`Nat.div_add_mod`). Since `n ∣ m`, the
  remainders `(i+j) mod m mod n` and `(i mod n + j mod n) mod n` agree.
  `omega` closes the resulting linear identity.
- `inflationCoefficients_baseUnit`: the published coefficient map of
  `relativeInflation`, the unit inclusion `Lˣ → Mˣ`, sends the inclusion of
  `a ∈ Kˣ` into `Lˣ` to its inclusion into `Mˣ`. This holds by the scalar
  tower.
- `inflation_cyclicClass`: let `m = n k`, and suppose
  `val χL(g|L) = val χM(g) mod n` for all `g`. Then

  ```text
  relativeInflation K L M 2 (cyclicClass K L χL a) = cyclicClass K M χM (a ^ k).
  ```

  By `groupCohomology.H2π_comp_map_apply`, the left side is the class of the
  cocycle `mapCocycles₂` of the carry cocycle. At `(g, h)`, this cocycle is
  the image in `Mˣ` of the carry cocycle of `L` at `(g|L, h|L)`. Write
  `i = val χM(g)` and `j = val χM(h)`. Then `val χM(gh) = (i+j) mod m` by
  `ZMod.val_add`. By the hypothesis, the inflated cocycle is
  `a ^ ⌊(i mod n + j mod n)/n⌋`, while the cocycle for `a ^ k` modulo `m` is
  `a ^ (k⌊(i+j)/m⌋)`. The proof uses `groupCohomology.H2π_eq_iff` with the
  one-cochain

  ```text
  f(g) = a ^ ⌊val χM(g) / n⌋.
  ```

  Its coboundary is `(d f)(g, h) = g·f(h) − f(gh) + f(g)` in additive
  notation. Base units are Galois-fixed (`baseUnit_fixed`), so this is
  `a ^ (⌊j/n⌋ − ⌊((i+j) mod m)/n⌋ + ⌊i/n⌋)`. After collecting multiples of `a`,
  the coboundary equation is exactly `carry_identity`. Thus the two cocycles
  differ by the coboundary of `f`, and their classes agree.

### 4. Carry classes and the explicit invariant

- `cyclicClass_eq_symm`: let `E/K` be finite Galois with a coordinate
  `χ : Gal(E/K) ≃ ℤ/n`. By the normalization, applied to
  `σ = cyclicCoordinateGenerator χ`, the carry class `cyclicClass K E χ a`
  equals the inverse image, under the published equivalence
  `cyclicH2NormEquiv`, of the class of `a` in the norm quotient.
  `χ.apply_symm_apply` verifies the generator hypothesis `χ σ = +1`.
- `exists_cyclicClass_eq`: every `x ∈ H²(Gal(E/K), Eˣ)` is a carry class
  `cyclicClass K E χ a`. The norm quotient projection is surjective, so
  choose `a ∈ Kˣ` whose class is the image of `x` under `cyclicH2NormEquiv`.
  Then `cyclicClass_eq_symm` and injectivity of the equivalence give
  `cyclicClass K E χ a = x`.
- `unramifiedH2Invariant_cyclicClass`: for a finite unramified Galois
  extension `E/F` of p-adic fields with coordinate `χ`, and `a ∈ Fˣ`,

  ```text
  unramifiedH2Invariant F E hram χ (cyclicClass F E χ a)
    = rationalClass (ord_F(a) / [E:F]).
  ```

  This rewrites by `cyclicClass_eq_symm` and then applies the published
  `unramifiedH2Invariant_normRepresentative` from
  [`UnramifiedInvariant`](UnramifiedInvariant.md). That theorem evaluates the
  invariant on the inverse norm comparison of a base unit. Here `ord_F` is
  the canonical normalized valuation
  `F.canonicalTopologicalData.ord`.

### 5. Assembly

`inflationCompatibility_of_normalization` introduces all quantified data of
the target, rebuilds the two `NeZero` degree instances from
`Module.finrank_pos`, and splits both arithmetic coordinate hypotheses.

1. By `exists_cyclicClass_eq` for `L/F` and `χL`, write
   `x = cyclicClass F L χL a` for some `a ∈ Fˣ`.
2. `M/L` is finite (`Module.Finite.of_restrictScalars_finite`), and
   `[M:F] = [L:F]·[M:L]` by `Module.finrank_mul_finrank`. Put `k = [M:L]`.
3. `restrictNormal_frobenius` gives
   `(cyclicCoordinateGenerator χM)|L = cyclicCoordinateGenerator χL`.
   `coordinate_restrict_val` then gives
   `val χL(g|L) = val χM(g) mod [L:F]` for every `g ∈ Gal(M/F)`.
4. By `inflation_cyclicClass`, the inflation of `x` is
   `cyclicClass F M χM (a ^ k)`.
5. By `unramifiedH2Invariant_cyclicClass`, applied to `M` and to `L`, the
   two sides become `rationalClass (ord_F(a ^ k) / [M:F])` and
   `rationalClass (ord_F(a) / [L:F])`. The published valuation identity
   `Langlands.PadicField.TopologicalData.ord_zpow` gives `ord_F(a ^ k) = k·ord_F(a)`.
   Hence

   ```text
   k·ord_F(a) / ([L:F]·k) = ord_F(a) / [L:F]
   ```

   in `ℚ`, cancelling the nonzero factor `k`.

The final theorem `unramifiedInvariantInflationCompatibility` is
`inflationCompatibility_of_normalization cyclicClassNormNormalization.{u, u}`.

## Scope

The proof concerns the explicit finite invariant `unramifiedH2Invariant`. That
invariant is built from the actual ordinary cohomology, the published
`cyclicH2NormEquiv`, and the canonical valuation on the norm quotient. Its
inflation is the published `relativeInflation`, which pulls back along
`AlgEquiv.restrictNormalHom` and includes `Lˣ` into `Mˣ`. No class formation,
reciprocity, absolute invariant or `InvariantFamily` hypothesis is used. The
parent target `AbsoluteInvariantExistence` is not used.

The arguments in sections 2–4 hold for arbitrary fields `K`. They assume no
p-adic structure, only the stated finiteness, normality and Galois
hypotheses. Section 1 and the final assembly use the p-adic residue-field
structure and the canonical valuation.

## Provenance

The mathematical content corresponds to Jean-Pierre Serre, *Local Fields*,
English translation by Marvin Jay Greenberg, Springer GTM 67, 1979,
Chapter XIII, §3. The relevant passages are the explicit description of
`inv_K` after Proposition 6, and Proposition 7, case (a), together with its
proof. These are printed pp.193–194, PDF pp.198–199. Serre evaluates the
character obtained from the valuation at the arithmetic Frobenius. His
case (a) uses that the distinguished generator of the subgroup of index `n`
is `Fⁿ`, the `n`th power of Frobenius. The present finite-stage law is the
complementary inflation statement. It expresses that the invariant does not
depend on the finite unramified splitting field. Serre's formulation is in
the Brauer group and continuous cohomology of the maximal unramified
extension; the proof here does not quote it.

The proof here is internal to the Library's finite constructions. The
Frobenius restriction through residue fields, the explicit carry coboundary
`a ^ ⌊val χM(g)/n⌋` with its carry identity, and the valuation and degree
computation were written for this module. They implement the finite cocycle,
Frobenius and valuation comparisons that the target Markdown names as proof
obligations. Worker 272 read the cited pages of the registered source
`serre-1979-local-fields`, at
`/home/taskhub/central-library/Serre--Local Fields--1979.pdf`, SHA256
`109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`.

Reused published results include the following. The positive carry
normalization `cyclicClassNormNormalization` is Worker 28's proof, built on
the published generic theorem `Langlands.Cohomology.CyclicH2.cocycleSumComparison`.
The invariant construction and `unramifiedH2Invariant_normRepresentative`
come from [`UnramifiedInvariant`](UnramifiedInvariant.md). The carry
cocycle comes from [`CyclicClass`](CyclicClass.md), and the inflation maps
from [`Cohomology`](Cohomology.md). The valuation identity `ord_zpow` comes
from `Langlands.LocalField.Normalization.Proof`. These modules are imported
unchanged; their own Markdown records their authorship.
