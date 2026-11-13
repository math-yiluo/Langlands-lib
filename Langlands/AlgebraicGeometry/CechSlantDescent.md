# Descent of shuffle slant maps to all-sequence Čech cohomology

This internal construction descends the shuffle operator from
`CechSlant` to the homology of the all-sequence Čech complex.

For cochain complexes `K` and `Q` in a preadditive category, suppose that maps
`s n : K.X (n + 1) ⟶ Q.X n` satisfy

```text
K.d (n + 1) (n + 2) ≫ s (n + 1) = -(s n ≫ Q.d n (n + 1)),
K.d 0 1 ≫ s 0 = 0.
```

The definition `slantShortComplexMap n` is a morphism from `K.sc (n + 1)`
to `Q.sc n`. For positive `n`, its three components, after the canonical
identification with adjacent degrees, are `-s (n - 1)`, `s n`, and
`-s (n + 1)`. At `n = 0` its first component is zero. The second displayed
identity supplies the left commutative square in that case. The
anticommutation identity supplies the other squares.

`slantShortComplexMap_τ₂` identifies the middle component with `s n`.
When the two complexes have homology in the relevant degrees,
`slantHomologyMap n` is the map on their homology induced by this short-complex
morphism. The formula `slantCyclesMap_i` identifies the induced map on cycles
with `s n` after inclusion in cochains. The formula
`slantHomologyMap_homologyπ` expresses compatibility with passage from cycles
to homology classes.

For the Čech application, `R` is an arbitrary commutative ring and `P` is
supplied with a pullback square over `Spec R`, with projections to `X` and `Y`.
The section rings on all three schemes carry supplied `R`-algebra structures
identified with the scalar maps of their structure morphisms. The two
intersection families `U : ι → X.Opens` and `V : κ → Y.Opens` have index types
in the same universe, so their complexes and the product complex lie in the
same category of abelian groups. Only `ι` is assumed finite. All two-entry
intersections for `U` and all nonempty finite intersections for `V` must be
affine; neither family is required to cover its scheme.

The supplied `R`-linear functional `l` on the first-factor one-cochains must
kill first coboundaries. `LAddHom n` is the underlying additive morphism of
`LLinearMap n`. The definition `LHomologyMap n` has type

```text
(complex (ab P.presheaf) (prodCover p₁ p₂ U V)).homology (n + 1) ⟶
  (complex (ab Y.presheaf) V).homology n.
```

Its construction applies `slantHomologyMap`: `L_d` proves anticommutation
and `L_zero_d` proves the bottom boundary identity. The differential of the
alternating coface complex is explicitly identified with the cochain
differential before using `L_d`.

The provenance is internal homological algebra applied to the existing
section-cochain operator, using Mathlib's short-complex homology construction.
The output is an additive map on actual Čech homology. Identification with
right-derived sheaf cohomology, an `R`-linear map on that cohomology,
geometric creation-contraction relations, exterior generation, and the host
degree-two comparison remain separate obligations.
