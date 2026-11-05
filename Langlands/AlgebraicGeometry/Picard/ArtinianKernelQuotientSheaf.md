# Actual product-sheaf compatibility for an elementary kernel quotient

This internal construction globalizes the affine residue-coefficient comparison
in `ArtinianKernelQuotientResidue`. It constructs the coefficient map independently
of the ideal comparison, then proves equality with the actual ideal quotient.
All types have arbitrary common universe `u`. The data are a commutative ring
`k`, a field `K` over `k`, a scheme morphism `f : X → Spec k`, an elementary
surjection `q : A → B` of augmented Artinian tests, and a subspace
`W ⊆ Kernel q` for the already descended `K`-action. Elementary means the
kernel is annihilated by the maximal ideal and includes a zero kernel.

Write `AQ` for `ElementaryKernelSubspaceQuotient.test q W`, `π : A → AQ`
for its actual quotient projection, and `r : AQ → B` for its reduction.
The relative scheme map is `h : X_AQ → X_A`. The actual residue immersions
are `iA : X_K → X_A` and `iQ : X_K → X_AQ`, with `iQ ≫ h = iA`.
Choose finite bases `b : Basis ι K (Kernel q)` and
`c : Basis κ K (Kernel r)`. Empty basis types are allowed.

## Actual scalar and restriction laws

`quotientResidueTensorMap_smul` proves, on every open `U ⊆ X_A`,

```
Q_U (a • t) = h.app U a • Q_U t,
```

where `Q_U` is the existing actual residue-section restriction tensored with
the ordinary quotient map on kernels. The source scalars act through
`iA.app U`; target scalars act through `iQ.app (h⁻¹ U)`.
Tensor induction reduces this to the actual composite-section identity
`quotientResidueSectionMap_app`. No scalar section `K → A` is supplied.

`quotientResidueTensorMap_res` proves that `Q_U` commutes with the actual
restrictions for `V ≤ U`, on both source and target residue opens. Its proof
uses tensor induction. For pure tensors the structure presheaf's composition
law identifies the two paths around the restriction square; additive cases
follow from additivity.

## The coefficient sheaf map

Let `P_A = residueProductModule f ι` and
`P_AQ = residueProductModule f κ` with the indicated source tests. These
are finite products of the actual pushed-forward residue structure modules.
`productTensorEquiv` presents their sections as actual residue sections
tensored over `K` with the corresponding actual kernel.

`quotientProductSectionsAddHom` is the additive composite

```
Γ(P_A,U) → Γ(X_K,iA⁻¹ U) ⊗[K] Kernel q
        → Γ(X_K,iQ⁻¹(h⁻¹ U)) ⊗[K] Kernel r
        → Γ(P_AQ,h⁻¹ U).
```

The middle arrow is `Q_U`; the first and last arrows are the existing product
tensor equivalence and the inverse target equivalence. This definition never
uses either ideal-sheaf equivalence. `quotientProductSections` retains the
actual `Γ(X_A,U)`-linear structure on this composite, with the target scalars
restricted through `h.app U`. Its linearity follows from the scalar law above.

`quotientProductSections_res` uses `productTensorEquiv_res` twice and the tensor
restriction law to prove compatibility with the actual module-presheaf maps.
`quotientProductMap : P_A → h_* P_AQ` is formed directly by
`PresheafOfModules.homMk` from these additive maps, naturality and scalar
linearity. `quotientProductMap_app` gives exactly the composite displayed
above. `productTensorEquiv_quotientProductSections` records its tensor formula.
None of these constructions requires flatness or properness of `f`.

## Comparison with the ideal quotient

Assume `Flat f`. `affineProductIdealEquiv_quotient` states that on an affine
`U ⊆ X_A`, with affine inverse image `h⁻¹ U`, the actual `idealMap.app U`
commutes with `quotientProductSections` under the existing affine product/ideal
equivalences. The proof first compares underlying structure-section values,
using `affineKernelResidueEquiv_quotient` and the actual `idealMap_app` formula.
A general square-transfer lemma precomposes with the product tensor
coordinates. Subtype extensionality then recovers equality of ideal sections.

The global result `productToIdeal_quotient` is the sheaf equality

```
productToIdeal f q b ≫ idealMap f q W =
  quotientProductMap f q W b c ≫ h_*(productToIdeal f r c).
```

The actual projection `π` is elementary and hence induces a closed immersion
`h`. Every affine `U` therefore has affine inverse image. A general sheaf
comparison lemma applies `BasisHomGluing.hom_ext_of_basis` on the affine basis.
On each affine it substitutes the actual `productToIdeal_app` formulas and
uses the affine comparison. This proves equality of the independently
constructed sheaf maps on all opens. The statement needs no properness.

## Provenance and retained obligations

This is an internal consequence of the actual residue-section, coefficient,
ideal, quotient and product constructions already imported by Lean name.
The two quotient maps are not defined by conjugating the ideal map through an
isomorphism. Finite bases present the actual tensor coefficients as sheaves.
The result asserts neither the corresponding cohomology tensor naturality nor
obstruction naturality, a formal hull, effectivity, algebraization or the exact
`FieldPicardStackAtlasStatement`; those remain separate obligations.
