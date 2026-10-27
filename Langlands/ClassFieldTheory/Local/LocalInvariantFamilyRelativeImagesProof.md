# Relative images of the local invariant family

Author: Worker 272.

This module proves the published proposition
`Langlands.ClassFieldTheory.Local.LocalInvariantFamilyRelativeImagesStatement`
(module `Langlands.ClassFieldTheory.Local.LocalInvariantFamilyLawsStatement`).
The exact-target theorem is

```
theorem localInvariantFamilyRelativeImages :
    LocalInvariantFamilyRelativeImagesStatement.{u}
```

in the namespace `Langlands.ClassFieldTheory.Local`. Unfolded, it says: for
every proof `hEx : UnramifiedH2Exhaustion.{u}`, every prime `p`, every p-adic
field `F` and every finite Galois extension `L/F` (in universe `u`), the
relative invariant `(localInvariantFamily hEx p).relative F L` is injective,
and its range is `denominatorSubgroup (Module.finrank F.Carrier L)`, the
subgroup of `ℚ/ℤ` killed by `[L:F]`.

## Source

Jean-Pierre Serre, *Local Fields*, GTM 67, Springer, 1979 (registered source
`serre-1979-local-fields`, SHA256
`109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`),
Chapter XIII, §3, Proposition 7 and its Corollary 2 (printed pages 193–194,
PDF pages 198–199). Serre identifies `H²(L/K)` with the kernel of restriction
`Br(K) → Br(L)`. Proposition 7 says that restriction multiplies the invariant
by `n = [L:K]`. Corollary 2 concludes that `inv_K` maps `H²(L/K)`
isomorphically onto `(1/n)ℤ/ℤ`. The Lean proof follows this route, with
continuous cohomology of the algebraic closure in place of the Brauer group.

## The implemented proof

The module contains only the exact-target theorem. After introducing
`hEx`, `p`, `F` and `L`, the proof introduces the instance
`CharZero F.Carrier := Algebra.charZero_of_charZero (Padic p) F.Carrier` and
names the following objects.

- `f := closureEmbedding F.Carrier L`, the chosen embedding of `L` into
  `AlgebraicClosure F.Carrier`, and `E := f.fieldRange`. The Library instances
  `embeddedImage_finiteDimensional` and `embeddedImage_isGalois` make `E`
  finite and Galois over `F`.
- `invF := descendedEquiv F hEx closureInflationTowerCompatibility
  unramifiedInvariantInflationCompatibility`, the bijective descended absolute
  invariant of `F` (`AbsoluteInvariantAssembly`). Its underlying map is
  `localAbsoluteInvariant hEx F`.

By definition (`rfl`), the relative invariant of `L` is the Library map
`relativeInvariantFromAbsolute F.Carrier E invF` (module
`RelativeInvariantFromAbsolute`, which is `invF` after `closureInflation`)
composed with the transport `relativeH2Equiv f.equivFieldRange` from
`H²(L/F)` to `H²(E/F)`.

1. Injectivity. `AbsoluteH2Assembly.closureInflationExactness F.Carrier E`
   (module `AbsoluteH2InflationProof`) gives injectivity of
   `closureInflation F.Carrier E 2`. Then
   `relativeInvariantFromAbsolute_injective` gives injectivity of
   `relativeInvariantFromAbsolute F.Carrier E invF`. Compose with the
   injective transport.

2. Range. The transport is surjective, so the range of the composite is the
   range of `relativeInvariantFromAbsolute F.Carrier E invF`
   (`AddMonoidHom.range_comp`, `AddMonoidHom.range_eq_top`,
   `AddMonoidHom.range_eq_map`). The proof then builds the data needed by the
   Library theorem `relativeInvariantFromAbsolute_range`:
   - `E'` is the same field `E` packaged as a p-adic field,
     `FiniteIntermediateExtension.asPadicField ⟨E, _⟩`. Its carrier is `E`.
     The proof adds the local instance `E'.algebra` and the scalar tower
     `Padic p → F → E'` (`IsScalarTower.of_algebraMap_eq' rfl`).
   - `φ : AlgebraicClosure F.Carrier →ₐ[F.Carrier] AlgebraicClosure E` is
     `IsAlgClosed.lift`. Its ring map is the algebra
     `Algebra (AlgebraicClosure F.Carrier) (AlgebraicClosure E)`. The scalar
     tower `F → AlgebraicClosure F → AlgebraicClosure E` follows from
     `φ.commutes`.
   - `invE := descendedEquiv E' hEx ...`, the descended absolute invariant
     of `E'`.
   - `hExact` is the second half of the published `absoluteH2InflationExactness`
     (module `AbsoluteH2InflationProof`) for `E` and this closure algebra:
     the range of closure inflation is the kernel of `absoluteRestriction`.
   - `hDegree` is `descendedHom_restriction F hEx ... E' x`
     (`AbsoluteInvariantAssembly`), using the published proofs
     `unramifiedBaseChangeStageExistence`,
     `closureInflationBaseChangeCompatibility` and
     `unramifiedInvariantBaseChangeCompatibility`. It says that
     `invE (absoluteRestriction F E 2 x) = [E:F] • invF x`.

   `f.equivFieldRange.toLinearEquiv.finrank_eq` rewrites `[L:F]` as `[E:F]`,
   and `relativeInvariantFromAbsolute_range F.Carrier E invF invE hExact
   hDegree` closes the goal.

## Notes

- The closure algebra chosen by `IsAlgClosed.lift` is used only inside the
  proof. Both `hExact` and `hDegree` hold for every compatible closure
  algebra.
- Axioms used by the target theorem: `propext`, `Classical.choice`,
  `Quot.sound`.
