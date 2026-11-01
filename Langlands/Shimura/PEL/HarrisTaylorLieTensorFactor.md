# The actual Harris–Taylor Lie tensor factors

Let `L` be an imaginary quadratic CM number field, let `K` be a number
field containing `L`, and let `s : S ⟶ Spec K` be an actual structure
morphism. Let `B` be an abelian scheme over `S`, and let
`i : A →ₐ[ℚ] End0 B` be a rational action of a `K`-algebra `A` on `B`.
The module uses the actual relative Lie sheaf and the differentiated central
`L`-action `imaginaryLieAction L s B i`. It constructs all global and local
scalar structures from `s` and restriction of regular functions.

The source is Harris–Taylor, *The Geometry and Cohomology of Some Simple
Shimura Varieties* (2001), III.1, printed pp.89–90 / PDF pp.97–98,
registered as `harris-taylor-2001-geometry-cohomology-simple-shimura`,
SHA256 `5be28164b61d6f6cc28dd9e6b990d669504f3470860b230ebbc97e3da10af56b`.
There the natural and conjugate Lie factors are defined by
`Lie A ⊗_(O_S ⊗_ℚ E) O_S`, with the natural or conjugate imaginary-field
embedding on the final factor. The source's imaginary field `E` is `L`
here, its CM field `F` is `K`, and its totally real field `F⁺` is not a
parameter of this module. The construction below supplies this tensor-factor
identification; the source's additional rank and compatibility conditions
remain separate obligations.

For an open `U`, put `R_U = Γ(S,U)` and `M_U = Γ(B.Lie,U)`.
`lieTensorSections` is the genuine original-order tensor module

```text
M_U ⊗_(R_U ⊗_ℚ L) R_U.
```

The left tensor-algebra action is induced by the actual differentiated
`L`-action on `M_U`. The right factor uses the selected coordinate algebra
map `factorEvaluation`: `false` is the structural embedding and `true` is
its composition with CM conjugation. The scalar towers and commuting
`R_U`-action are constructed explicitly. `lieTensorOrderEquiv` is tensor
symmetry, restricted to `R_U` scalars; it compares this tensor order with
the scalar-first generic construction.

`lieTensorSectionEquiv` composes that symmetry with the constructed generic
tensor/eigen equivalence. Its target is all sections of the full simultaneous
Lie eigensubsheaf, defined by the eigen equation for every element of `L`.
The proved pure-tensor formula sends `m ⊗ r` to
`r • moduleProjector conjugate m`. Its inverse sends an eigensection `x`
to `x.val ⊗ 1`; the inverse formula follows by applying the injective
comparison and using that the relevant projector fixes an eigenvector.

`lieTensorRestriction` transports the actual eigensheaf restriction through
these constructed section equivalences. The comparison commutes with
restriction, and `lieTensorRestriction_tmul` proves the formula

```text
m ⊗ r  ↦  (m restricted to U) ⊗ (r restricted to U)
```

for `U ⊆ V`. The proof applies the injective comparison, uses its pure-tensor
formula and semilinearity of actual Lie restriction, and then uses projector
naturality. Thus the restrictions have the canonical tensor formula.
Identity and composition follow by the same injective comparison from the
actual eigensheaf laws. `lieTensorPresheaf` has exactly these section modules
and restrictions, and `lieTensorPresheafIso` assembles their equivalences.

`lieTensorSheaf` transfers the sheaf condition from the full Lie eigensheaf
along that presheaf isomorphism. Its section modules are unchanged; no
sheafification is used. `lieTensorSheafIso` lifts the constructed presheaf
isomorphism to an isomorphism in actual `S.Modules`. The section formulas
for its forward and inverse maps are proved explicitly.

`lieTensorProjection` composes the actual Lie eigenprojection with the inverse
tensor comparison. The private projector comparison proves that evaluating
the sheaf projector on sections agrees with the module projector: decompose
a section into its two module-projector components, identify their full
eigenconditions with the sheaf eigenconditions, and use the sheaf projector's
identity and zero formulas on these components. Consequently
`lieTensorProjection_app` proves that the actual sheaf projection is the
canonical tensor map `m ↦ m ⊗ 1`.

Finally `lieTensorSplitting` composes the existing actual Lie eigensheaf
splitting with the two inverse tensor comparisons. It is an actual
isomorphism from `B.Lie` to the product of its two original-order tensor
sheaves, with forward morphism the pair of canonical tensor projections.
These are derived constructions using the existing tensor-idempotent and
Lie APIs; neither the tensor sheaves nor their comparisons are supplied as
inputs. No local freeness, prescribed rank, equality of the two totally real
field actions, arbitrary scheme pullback, or construction of representing
PEL schemes is asserted here.
