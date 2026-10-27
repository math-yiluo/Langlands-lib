# Continuous properties of the local invariant family

Author: Worker 272.

This module proves the published proposition
`Langlands.ClassFieldTheory.Local.LocalInvariantFamilyContinuousStatement`
(module `Langlands.ClassFieldTheory.Local.LocalInvariantFamilyLawsStatement`).
The exact-target theorem is

```
theorem localInvariantFamilyContinuous :
    LocalInvariantFamilyContinuousStatement.{u}
```

in the namespace `Langlands.ClassFieldTheory.Local`. Unfolded, it says: for
every proof `hEx : UnramifiedH2Exhaustion.{u}` and every prime `p`, the family
`localInvariantFamily hEx p` satisfies
`InvariantFamily.ContinuousInvariantProperties` (module `ClassFormation`).
This predicate is the conjunction of four clauses:

1. `LocalAbsoluteH1Vanishing p`: for every p-adic field `F`, the continuous
   cohomology `absoluteCohomology F.Carrier 1` is a subsingleton.
2. `AbsoluteIsomorphisms`: every absolute invariant
   `localAbsoluteInvariant hEx F` is bijective.
3. `AbsoluteRestriction`: for every finite extension `E/F` of p-adic fields
   and every compatible algebra between the algebraic closures, absolute
   restriction multiplies the absolute invariant by `[E:F]`.
4. `OrdinaryClosureCompatibility` (module `FiniteInvariantCompatibility`):
   for every finite Galois subfield `E` of `AlgebraicClosure F.Carrier` and
   every `x` in `H²(E/F)`, the absolute invariant of
   `closureInflation F.Carrier E 2 x` equals the relative invariant of `x`.

The module also proves the helper `localInvariantFamily_relative_eq`, which
later family-law proofs reuse.

## Source

Jean-Pierre Serre, *Local Fields*, GTM 67, Springer, 1979 (registered source
`serre-1979-local-fields`, SHA256
`109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`):

- Chapter X, §1, Proposition 2 (printed page 150, PDF page 156):
  `H¹(G, K*) = 0` for a finite Galois extension. The remark on printed
  page 151 calls it Hilbert's theorem 90. Chapter XIII, §4, Theorem 1
  (printed page 195, PDF page 200) uses it as axiom I of the local class
  formation.
- Chapter XIII, §3, Proposition 6 (printed page 193, PDF page 198):
  `inv_K : B_K → ℚ/ℤ` is an isomorphism.
- Chapter XIII, §3, Proposition 7 (same page): `inv_L ∘ Res_{K/L} = n · inv_K`
  for a finite extension `L/K` of degree `n`.
- Chapter XIII, §3, Corollary 2 of Proposition 7 (printed page 194, PDF
  page 199): Serre regards `H²(L/K)` as a subgroup of `B_K` and takes the
  restriction of `inv_K` to it as the relative invariant. Clause 4 is this
  convention.

The Lean statements use continuous cohomology of the algebraic closure in
place of the Brauer group.

## The implemented proof

### Helper `localInvariantFamily_relative_eq`

For `hEx`, a p-adic field `F`, a finite Galois extension `L/F`, a finite
normal subfield `E` of `AlgebraicClosure F.Carrier`, an `F`-isomorphism
`e : L ≃ₐ[F.Carrier] E` and `x` in `H²(L/F)`:

```
(localInvariantFamily hEx p).relative F L x =
  localAbsoluteInvariant hEx F
    (closureInflation F.Carrier E 2 (relativeH2Equiv e x))
```

By definition, `localInvariantFamily_relative` and
`embeddedRelativeInvariant_apply` (module `LocalInvariantFamily`) compute the
relative invariant through the image of the chosen embedding
`closureEmbedding F.Carrier L` and the isomorphism `equivFieldRange` onto that
image. The published theorem `closureInflationTransportIndependence` (module
`ClosureInflationIndependenceProof`) says that transport followed by closure
inflation does not depend on the isomorphism onto a normal finite subfield.
The proof rewrites with it, replacing the chosen embedding by `e`.

### Main theorem

After introducing `hEx` and `p`, the proof splits the conjunction.

1. Hilbert 90. For each `F`, the proof introduces the instance
   `CharZero F.Carrier := Algebra.charZero_of_charZero (Padic p) F.Carrier` and
   applies the published `absoluteH1Vanishing` (module `AbsoluteH1Proof`),
   which holds for every field of characteristic zero.
2. Bijectivity. The absolute invariant is
   `descendedHom F hEx closureInflationTowerCompatibility
   unramifiedInvariantInflationCompatibility` (module
   `AbsoluteInvariantAssembly`). The Library theorems `descendedHom_injective`
   and `descendedHom_surjective` give the two halves.
3. Degree law. `descendedHom_restriction` (module `AbsoluteInvariantAssembly`)
   with the published proofs `unramifiedBaseChangeStageExistence`,
   `closureInflationBaseChangeCompatibility` and
   `unramifiedInvariantBaseChangeCompatibility` is exactly the clause.
4. Closure compatibility. For a finite Galois subfield `E` of the closure and
   `x` in `H²(E/F)`, apply the helper with `L := E` and `e := AlgEquiv.refl`.
   The published `relativeH2Equiv_refl` (module
   `ClosureInflationIndependenceProof`) says transport along the identity is
   the identity. Both sides then agree by definition (`rfl`).

## Notes

- `OrdinaryClosureCompatibility` assumes `IsGalois F.Carrier E`. The helper
  needs only `Normal F.Carrier E`, which the `IsGalois` instance provides.
- Axioms used by the target theorem: `propext`, `Classical.choice`,
  `Quot.sound`.
