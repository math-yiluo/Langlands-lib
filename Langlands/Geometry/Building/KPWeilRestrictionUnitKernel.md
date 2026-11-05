# Unit coordinates in finite-separable Weil restrictions

Authors: Worker 706; tensor-unit point interfaces by Worker 1587.

Let `E/k` be a finite separable field extension and let `L/k` be any field
extension in the same arbitrary universe `u`. Assume that every minimal
polynomial of an element of `E` splits over `L`. Write `W` for the actual group
scheme `Res_{E/k} Gm` and `W_L` for its actual scalar extension.

`WeilGm.embedding_rational_coordinate` identifies the coordinates of the
published embedding splitting `embeddingCommIso` on rational points:

```text
split-coordinate τ of x =
  Units.map (tensorCoordinate (AlgHom.id k L) τ)
    (extensionUnitsEquiv k L E x).
```

The right side directly evaluates the tensor unit in `(E ⊗[k] L)ˣ` at the
embedding `τ : E →ₐ[k] L`. The left side is the unit coordinate of the
`L`-rational point obtained by the actual group-scheme splitting.

For any valuation `v : Valuation L Γ` into a linearly ordered commutative
group with zero, `WeilGm.mem_extension_characterValuationKernel` proves

```text
x ∈ characterValuationKernel v W_L ↔
  ∀ τ : E →ₐ[k] L,
    v (tensor-coordinate τ of extensionUnitsEquiv k L E x) = 1.
```

No Galois or valuation-invariance hypothesis is needed for this comparison
over `L`.

`tensorEmbeddingUnitKernel k E L v` is the subgroup of `(E ⊗[k] L)ˣ`
defined by these coordinate valuation conditions, as the intersection of
their kernels. `extensionCharacterKernelEquiv k E L hsplit v` restricts
`extensionUnitsEquiv` to a multiplicative equivalence from the actual
character-valuation kernel to this tensor-unit subgroup. Its inverse is the
inverse point-coordinate equivalence; the membership criterion above
supplies both restrictions. The inverse and multiplication laws follow from
the unrestricted multiplicative equivalence.

The auxiliary `Building.mem_split_characterValuationKernel` says that the
character kernel of a split torus consists exactly of the points with unit
valuation in each coordinate. Its forward implication applies each coordinate
projection and the multiplicative-group kernel criterion. For the reverse
implication, the published `splitPoint_decomposition` reconstructs a point as
the product of its coordinate cocharacters, each of which preserves the kernel.

The coordinate bridge is proved on the affine test scheme `Spec L`. The
published pullback-point adjunction and `pointE_baseChangeCoeffEquiv` identify
the rational-point and coefficient-point conventions. The all-test splitting
formula `embeddingCommIso_hom_points` and `embeddingPointsEquiv_apply` give
tensor evaluation with coefficients in the global sections of `Spec L`.
`Corepresented.map_affineSectionsIso_pointsEquiv` transports those sections
back to `L`. Its ring map is `Scheme.ΓSpecIso.hom`; tensor induction shows
that transport commutes with embedding evaluation. This yields the direct
tensor formula. The kernel criterion follows by the split-torus criterion and
preservation of the character kernel along both directions of the splitting.

Provenance: an internal deduction from the published canonical separable
tensor decomposition, actual Weil-restriction splitting, relative-spectrum
adjunction and character-kernel functoriality. Worker 1587 supplied the direct
tensor-unit interfaces in `WeilRestrictionGaloisPoints`; Worker 706 supplied
the coordinate bridge and kernel criteria. This is a supporting comparison for
the induced-torus Iwahori proof, not the proof of its exact target.
