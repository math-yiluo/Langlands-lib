# Residue degree of a local central division algebra

`Langlands.CentralDivision.LocalResidueDegreeStatement.{u}` states that
the residue field of a finite-dimensional central division algebra over
a nonarchimedean local field has degree equal to its reduced degree.
The common universe is arbitrary, and every characteristic is allowed.

For `K` with `Field`, `ValuativeRel`, `TopologicalSpace` and
`IsNonarchimedeanLocalField`, and `D` with `DivisionRing`, `Algebra K D`,
`FiniteDimensional K D` and `Algebra.IsCentral K D`, write

```
v = localReducedNormValuation K D,
k = 𝓀[K],
R = DivisionValuation.Residue v.
```

The statement is `Module.finrank k R = CentralSimple.reducedDegree K D`.
It uses the existing multiplication on the actual residue quotient, the
compatible field structure `localDivisionResidueField K D`, and precisely
the scalar action `localDivisionResidueAlgebra K D` obtained by reducing
the original integral scalars. The valuation is the valuation of the
canonical reduced norm, constructed from the supplied local field; no
valuation, residue field, degree equality or maximal subfield is an extra
hypothesis.

The source is Jacques Tits, *Groupes de Whitehead de groupes algébriques
simples sur un corps*, Séminaire Bourbaki, exposé 505 (1977), registered
as `tits-1977-whitehead-bourbaki-505`, SHA256
`293a1b0637af56694914a6a4999b3bb56ae69d41444f748ad3fca037cce2f229`.
Section 3.1, printed page 227 / PDF page 11, formula (1), gives

```
sqrt([D : K]) = sqrt([R : Z(R)]) * [Z(R) : k],
```

under completeness and discreteness and separability of the residue
center over the base residue field. Here the local field has finite
residue field and the actual division residue is finite by the imported
construction. Little Wedderburn makes `R` commutative, so `Z(R) = R`;
the extension `R/k` is separable because finite fields are perfect.
The source formula therefore becomes the displayed residue degree
identity. The canonical reduced degree satisfies the positive
degree-square formula, and the canonical reduced-norm valuation has the
same integer and residue rings as a positive normalization of the
extended valuation. This statement uses those existing concrete
constructions.

This module states the degree formula and does not prove it. The
already constructed full-residue subfield has degree `[R : k]`; this
additional formula would identify its degree with the reduced degree.
It supplies no cyclicity, arbitrary-element movement, norm-kernel
equality, local SK1 proof or local Kneser–Tits proof.
