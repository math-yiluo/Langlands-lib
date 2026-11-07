# Rational classes and extension of the geometric base field

This is a derived construction from the actual rational-component quotient,
its injective extension map, the chosen geometric-component injection and the
actual geometric base-field comparison. It introduces no external structural
assertion.

Let `k` and `K` be arbitrary fields in the same arbitrary universe, with a
specified `k`-algebra structure on `K`, and let `H` be an actual smooth affine
group scheme over `Spec k`. For comparisons between the two chosen geometric
component groups, supply an `AlgebraicClosure k`-algebra structure on
`AlgebraicClosure K` compatible with the canonical map through `k → K`.
This specified embedding is the same data used by
`geometricComponentBaseChangeEquiv`. No existence or independence assertion
for that embedding is made. There is no algebraicity, separability,
perfection, characteristic, connectedness or reductivity restriction.

`geometricComponentBaseChangeSectionHom_rationalPoint` computes the actual
section comparison on every `x : rationalPoints H`:

```
geometricComponentBaseChangeSectionHom k K H
    (baseChangeSectionHom (baseMap k (AlgebraicClosure k)) H x)
  = baseChangeSectionHom (baseMap K (AlgebraicClosure K)) (baseChanged k K H)
      (baseChangeSectionHom (baseMap k K) H x).
```

Thus starting with the pulled-back `k`-section in the chosen closure gives
the same actual section as pulling it back first to `K` and then to the
chosen closure of `K`. These are sections of the actual iterated pullback.
The proof applies the two injective coefficient equivalences from the
iterated pullback to the original group over `k`. On the left, the published
`geometricComponentBaseChangeSectionHom_coefficient` formula becomes
coefficient extension along the specified closure embedding. On the right,
a private `coefficient_section_extension` calculation uses the published
rational section and coefficient tower laws. Replacing the two original
section pullbacks with `rationalExtend`, the published
`GaloisPoint.relativeExtend_extend` law identifies both coefficient points
with the direct extension from `k` to `AlgebraicClosure K`. The proof obtains
affineness of the actual source from `IsAffineHom H.X.hom` for this last law.
The private tower calculation itself imposes no smoothness or affineness.

For every ordinary rational identity-component class
`c : RationalComponentQuotient H`,
`geometricComponentBaseChangeEquiv_rational` proves the commutative comparison

```
geometricComponentBaseChangeEquiv k K H
    (rationalGeometricComponentHom k H c)
  = rationalGeometricComponentHom K (baseChanged k K H)
      (rationalComponentBaseChange H (algebraMap k K) c).
```

This concerns the actual full geometric component groups, and the ordinary
group quotient of rational sections by the actual rational identity-component
subgroup. The proof chooses a rational section representing `c`, uses the
published projection formulas for both rational maps and the component
comparison, and applies the preceding section equality.

`rationalGeometricComponentBaseChangeToFixed k K H` is a group homomorphism

```
RationalComponentQuotient H
  →* geometricComponentFixedSubgroup K (baseChanged k K H).
```

It first applies `rationalComponentBaseChange H (algebraMap k K)`, then the
published `rationalGeometricComponentToFixed` over `K`. Its construction and
its injectivity theorem do not need any embedding of chosen closures.
`rationalGeometricComponentBaseChangeToFixed_injective` composes the two
published injectivity results. With the specified closure embedding supplied,
`rationalGeometricComponentBaseChangeToFixed_val` identifies its underlying
component with the left side of the preceding comparison.

Finally, `geometricComponentBaseChangeEquiv_rational_smul` states that every
such transported original rational class is fixed by every automorphism in
`Field.absoluteGaloisGroup K`. It rewrites by the component comparison and
uses the published fixedness of a class represented by a `K`-section. It does
not require an extension or restriction of that automorphism to the other
chosen closure.

The fixed-subgroup map here starts from original rational classes. This unit
constructs no map on the entire `k`-Galois-fixed component subgroup, no
absolute Galois restriction homomorphism, and no surjectivity or effective
descent statement. It does not identify these ordinary quotients with points
of an fppf quotient.
