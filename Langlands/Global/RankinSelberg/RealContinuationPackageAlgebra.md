# Algebra of continuation packages

`RealJacquet.ContinuationPackage Z Zd L Ld E sign` (Library module
`RealUniformContinuationReduction`) asserts meromorphic functions `M`, `Md`
on `ℂ` that agree with `Z` and `Zd` on a common right half-plane and satisfy
`L s · Md(1-s) = sign · E s · Ld(1-s) · M s` off a discrete set. It is the
form of the target `RealLocalUniformUnequalContinuationStatement`. This
internal module records how such packages combine. It is used for
Jacquet, *Archimedean Rankin–Selberg integrals* (2009), §8.3, p. 60. There
the corank-one integral becomes, after a compact projection, a finite sum of
products of smaller equal-rank integrals and matrix (Godement–Jacquet)
integrals.

The lemmas in namespace `RealJacquet.ContinuationPackage` are:

* `zero`: the zero functions satisfy every package.
* `mul`: products of two packages give a package for the pointwise
  products of `Z`, `Zd`, `L`, `Ld`, `E` and of the signs. The proof takes
  the larger half-plane, the product continuations, and the intersection of
  the two codiscrete sets. Multiplying the two equations gives the new one.
* `add`, `sum`: sums (binary, or over a finite set) of packages with the
  same `L`, `Ld`, `E` and sign. The continuations and the equations add.
* `const_mul`: multiplying both `Z` and `Zd` by one constant.
* `dual_const_mul`: multiplying only `Zd` by `c` multiplies the sign by `c`.
* `congr_right`: a package depends on `Z` and `Zd` only on some right
  half-plane.
* `congr_factors`: the factors and sign may be replaced off a discrete set
  whenever the old equation implies the new one there.
* `shift`: replacing `Z(s)`, `L(s)`, `E(s)` by their values at `s + w` and
  `Zd(s)`, `Ld(s)` by their values at `s - w` preserves the package. The
  half-plane bound is enlarged by `|Re w|`. Meromorphy is preserved by
  composition with the translation, and codiscrete sets pull back under
  translations.

The proposition `RealJacquet.ContinuationPackageSumProductStatement` packages
the case used in the recursion. Take a finite index set and two families of
packages `(A i, Ad i)` and `(B i, Bd i)`. Each family has common factors
`(L₁, Ld₁, E₁)` and `(L₂, Ld₂, E₂)` and common signs `sign₁`, `sign₂`. Let
`b`, `d` be constants. Then `s ↦ b Σ A i s · B i s` and
`s ↦ d (b Σ Ad i s · Bd i s)` form a package. Its factors are `L₁L₂`,
`Ld₁Ld₂` and `E₁E₂`, and its sign is `d · sign₁ · sign₂`. The theorem
`continuationPackageSumProduct` proves it from `mul`, `sum`, `const_mul`
and `dual_const_mul`.

No statement about specific integrals, `L`-factors or `ε`-factors is made
here. The factor identities matching the products with the Rankin–Selberg
factors of the larger pair are separate obligations.
