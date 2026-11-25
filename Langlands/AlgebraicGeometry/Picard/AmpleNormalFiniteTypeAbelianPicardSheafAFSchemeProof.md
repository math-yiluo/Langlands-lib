# The Picard scheme of a projective abelian scheme over a normal finite-type `ℤ`-domain (proof)

The proof composes two published results: the reduction
`ampleNormalFiniteTypeAbelianPicardSheafAFScheme_of_noetherianIntegralFibre` and the
proof `noetherianIntegralFibrePicardSheafAFScheme`.

## Result

The module `Langlands.AlgebraicGeometry.Picard.AmpleNormalFiniteTypeAbelianPicardSheafAFSchemeProof`
proves, in the namespace `Langlands.AlgebraicGeometry.Picard` and for an arbitrary universe `u`,

```lean
theorem ampleNormalFiniteTypeAbelianPicardSheafAFScheme :
    AmpleNormalFiniteTypeAbelianPicardSheafAFSchemeStatement.{u}
```

This is exactly the target statement. The theorem
assumes nothing beyond the hypotheses of the statement. Let `R : Type u` be an integral domain
that is integrally closed and of finite type over `ℤ`, and let `A` be a Library abelian scheme
over `Spec R` whose total space `A.X.left` has an ample line bundle. Then there is an object
`P` of `Over (Spec R)` with two properties:

- the Library's fppf Picard class sheaf `RelativePicard.classSheafPresheaf A.X.hom` is
  represented by `P` on the whole slice, in the sense of Mathlib's `RepresentableBy`;
- every finite set of points of `P.left` lies in one affine open subscheme
  (`PointTopology.HasFiniteAffineNeighborhoods`).

The sources cited for this statement describe this as Grothendieck's theorem for projective abelian
schemes: Faltings–Chai, *Degeneration of Abelian Varieties*, Chapter I §1 (proof of Theorem 1.9
and Theorem 1.9(b)), and Mumford–Fogarty–Kirwan, *Geometric Invariant Theory*, Chapter 0
§5(c),(d) and Chapter 6 §1.

## Proof

The proof is a single term that applies a published reduction to a published proof. Both are
imported by their Lean names.

1. `noetherianIntegralFibrePicardSheafAFScheme` (module
   `Langlands.AlgebraicGeometry.Picard.NoetherianIntegralFibrePicardSheafAFSchemeProof`) proves
   `NoetherianIntegralFibrePicardSheafAFSchemeStatement.{u}`. This is S. L. Kleiman, *The
   Picard scheme*, Theorem 4.8(2), extended from Kleiman's test schemes to all test schemes. Let
   `R` be a noetherian ring and `f : X ⟶ Spec R` proper and flat with geometrically integral
   fibres, with a section, such that `X` has an ample line bundle. Then the fppf Picard class
   sheaf of `f` is represented by a scheme over `Spec R` in which every finite set of points
   lies in an affine open subscheme.
2. `ampleNormalFiniteTypeAbelianPicardSheafAFScheme_of_noetherianIntegralFibre` (module
   `Langlands.AlgebraicGeometry.Picard.AmpleNormalFiniteTypeAbelianPicardSheafAFSchemeIntegralFibreReduction`)
   proves the implication from `NoetherianIntegralFibrePicardSheafAFSchemeStatement.{u}` to
   `AmpleNormalFiniteTypeAbelianPicardSheafAFSchemeStatement.{u}`. It applies the general
   statement to `R`, the scheme `A.X.left` and the structure morphism `A.X.hom`:
   - `R` is noetherian because it is of finite type over `ℤ`;
   - `A.X.hom` is proper because `A` is an abelian scheme, and flat because it is smooth;
   - it has geometrically integral fibres (`abelianScheme_geometricallyIntegral`, from
     smoothness and geometric connectedness of the fibres);
   - its section is the unit section of the group scheme `A.X`;
   - the ample line bundle is the one in the hypothesis.

   The conclusion of the general statement is then literally the conclusion of the target.

The theorem is `ampleNormalFiniteTypeAbelianPicardSheafAFScheme_of_noetherianIntegralFibre`
applied to `noetherianIntegralFibrePicardSheafAFScheme`. The development check reports no errors
or warnings. The theorem uses only the axioms `propext`, `Classical.choice` and `Quot.sound`.

## Dependencies

The import closure contains neither the following statements nor any proof of them:
`NormalFiniteTypeAbelianPicardSheafAFSchemeStatement`,
`FiniteTypeAbelianPicardSheafSchemeStatement`,
`FiniteTypeSmoothFamilyAbelianRepresentabilityStatement` and
`SmoothFamilyAbelianRepresentabilityStatement`. So the
result can be used by the proof `finiteTypeAbelianPicardSheafScheme` of
`FiniteTypeAbelianPicardSheafSchemeStatement` (module
`Langlands.AlgebraicGeometry.Picard.FiniteTypeAbelianPicardSheafSchemeProof`), through
`normalFiniteTypeAbelianPicardSheafAFScheme_of_ample`, without a dependency cycle; that proof
does so.
