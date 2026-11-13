# Elementary Artinian ideal H² and the reduced coproduct

`Langlands.AbelianScheme.ArtinianH2PrimitiveInjectivityStatement.{u}` is a
`Prop`-valued definition. It asserts injectivity of multiplication pullback minus
the two projection pullbacks on the actual ideal cohomology of an elementary
Artinian thickening of an abelian scheme. This pair states a proof obligation;
it proves no injectivity result.

## Rings, schemes and coefficients

Let `φ : B' →+* B` be a surjection of local Artinian rings in `Type u` satisfying
`maximalIdeal B' * RingHom.ker φ = ⊥`. Let `A` be an abelian scheme over
`Spec B'`. Set `j = Spec φ`, let `P = A.X × A.X` in `Over (Spec B')`, and let
`p1`, `p2` and `m = p1 * p2` be its actual projection and multiplication arrows.

The actual immersions

```text
i  : A ×_(Spec B') Spec B → A
iP : P ×_(Spec B') Spec B → P
```

are the categorical `pullback.fst` maps. The product's special fibre is
canonically the self-product of the special fibre of `A`. Using the pullback
of `P` in this statement fixes its ideal sheaf independently of that comparison.
The coefficient modules are `I = StructureKernelModule.kernelModule i` and
`IP = StructureKernelModule.kernelModule iP`. Their sections are the actual
kernels of the two structure-sheaf homomorphisms; they are not supplied models.

For each `f` among `m`, `p1`, `p2`, the coefficient morphism has type
`k : I ⟶ f_* IP` and must satisfy

```text
k ≫ f_*(kernelModuleι iP) = kernelModuleι i ≫ unitToPushforwardUnit f.
```

Thus it applies the structure homomorphism `f^♯` to ideal sections. The inclusion
into the structure module determines this map uniquely. The statement quantifies
over all compatible coefficient maps, so no arbitrary choice of map affects its
conclusion. It does not assert existence of those maps; their construction from
the commuting base-change square is a separate elementary obligation of a
consumer.

The map `pull f k` is the underlying `B'`-linear map of

```text
H²(A, I) → H²(P, f*I) → H²(P, IP).
```

The first arrow is the unchanged `relativeCohomologyPullback f I 2`. The second is
the image under `relativeCohomology P.hom 2` of the adjoint of `k` under
`Scheme.Modules.pullbackPushforwardAdjunction f.left`. The conclusion is
`Function.Injective (pull m km - pull p1 k1 - pull p2 k2)`, with subtraction in
the common space of `B'`-linear maps.

## Source and provenance

Derived from D. Mumford, J. Fogarty and F. Kirwan, *Geometric Invariant Theory*,
3rd edition (1994), Chapter 6, proof of Proposition 6.7, printed pp.117–118,
especially the final displayed map and following injectivity argument on p.118
(PDF pp.130–131). The registered original is
`provided-ec58cb66687d0d54d9e39b6ec21281b651fe3a6d039f9b5d099c79791671233f`,
file `Mumford, Fogarty, Kirwan - Geometric Invariant Theory, 3rd edition (1994), Chapter 6.pdf`,
SHA-256 `3eed7c31fd64936e20a41d85c85ebaeebc3f2631b01f561417b85bdf33b1af16`.
Worker 2057 read both pages and visually checked the displayed map on p.118.
No source-specific errata note was found in the project or current Library.

The original identifies the obstruction coefficient group with
`H²(A_k, O_Ak) ⊗_k ker φ` and identifies the three induced maps with the
corresponding residue-fibre cohomology maps tensored with the identity. It then
asserts that the reduced coproduct is injective, using the cohomology structure
of abelian varieties and Künneth. The present statement isolates that coefficient
injectivity before any Picard class is considered. The particular relative
cohomology implementation and adjunction formulation are internal API choices.
The source's relative projectivity assumption is not required by this isolated
coefficient claim: the field input concerns abelian varieties, and the passage
to the residue fibre uses flatness and properness.

## Proof obligations and role

This is a substantial prerequisite of Task 5704
(`60cd926c-5964-46c0-ad0e-111a8faf6631`). Its expected proof uses
`FieldH2PrimitiveInjectivityStatement` and the Library's actual
`ArtinianResidueCohomology.idealCohomologyTensorEquiv`, proving compatibility with
the specific coefficient pullbacks, then preserving injectivity under tensoring
over the residue field. Existence of a cohomology isomorphism without these map
comparisons does not suffice. The current residue-cohomology API uses pointed
Artinian tests; a proof must justify its use for the arbitrary ring surjections
quantified here, or give another construction.

This statement does not mention a Picard class, primitivity of a line bundle,
or the obstruction map. Combining it with obstruction naturality and the
square-zero lifting criterion remains a separate proof. No Picard-zero lifting,
Picard smoothness or relative dual representability result is assumed.

## Authorship

Worker 2057 authored this pair.
