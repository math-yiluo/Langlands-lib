# Actual action classes with positive Lie compatibility and dimension

This module constructs the fixed-base rational action-class part of the
Harris–Taylor compatibility moduli problem. It uses the actual positive
Lie tensor sheaf, its local bases, its full rational algebra action, and
the structural scalar endomorphisms constructed in
`HarrisTaylorLieCompatibility`. The ambient quotient is
`RationalAlgebraAction.IsoClass S A`: actual abelian schemes with actual
unital rational algebra actions, modulo actual equivariant isomorphisms
in the rational category.

The inputs are an imaginary quadratic CM number field `L`, a number
field `K` containing `L`, a number field `E` with an algebra map to `K`,
an actual scheme map `s : S ⟶ Spec K`, a rational algebra `A` with a
`K`-algebra structure, and a natural number `n`. All types and the scheme
are in universe zero. No nonempty, reduced, connected, flat or locally
noetherian assumption on `S` is imposed.
The Lie quotient predicate and its representative laws only need `E`
to be a field; its number-field structure is used for the prescribed
dimension.

`lieCompatibility_actionIso` applies the proved Lie compatibility
invariance to the rational isomorphism underlying an actual equivariant
action isomorphism. This includes the actual rational inverse and both
inverse identities. Its intertwining equation holds for every element
of `A`.

`LieCompatibilityClassCondition` is a quotient lift to `Prop`, with
well-definedness proved by that invariance and propositional
extensionality. Its representative formula agrees with
`LieCompatibility L E s X.abelianScheme X.action n` for every actual
representative `X`. Thus it requires a local basis of rank `n` for the
positive tensor sheaf and equality of the central and structural `E`
actions on that sheaf.

`DimensionLieCondition` requires both

```text
PrescribedRelativeDimension E B n
  ∧ LieCompatibility L E s B i n.
```

The first conjunct is the actual relative-dimension predicate for the
abelian scheme's structure morphism, with dimension `[E : ℚ] * n²`.
`DimensionLieActionClassCondition q` requires one actual representative
of `q` satisfying this conjunction. The theorem
`dimensionLieActionClassCondition_iff` identifies this image with the
invariant Lie class predicate and the existential dimension image. In
the reverse direction, the Lie predicate is transferred to the very
representative witnessing dimension, so the conjunction is satisfied by
one actual abelian scheme.

Every representative of a class in this image satisfies positive Lie
compatibility. Membership of the ambient class of `X` is characterized
by an actual equivariantly rational-isomorphic action `Y` satisfying both
conditions. `DimensionLieActionClass` is the corresponding subtype of
the ambient quotient. Its constructor is surjective from the satisfying
representatives, and equality of constructed classes is exactly actual
equivariant rational isomorphism. The expanded equality criterion
retains the actual rational inverse and the full action equation.
Forgetting the condition is injective.

These proofs use quotient lifting, the constructed rational Lie
isomorphisms, the ambient quotient equality criterion, and subtype
extensionality. They do not assume geometric dimension invariance under
rational isomorphism: the dimension witness stays existential. Nor do
they identify Lie compatibility with the central trace or normalized
determinant conditions, provide arbitrary scheme pullback of positive
Lie compatibility, or construct representing schemes.

The original source is Harris and Taylor, *The Geometry and Cohomology
of Some Simple Shimura Varieties* (2001), III.1, printed pp.89–91 /
PDF pp.97–99, registered as
`harris-taylor-2001-geometry-cohomology-simple-shimura`, SHA256
`5be28164b61d6f6cc28dd9e6b990d669504f3470860b230ebbc97e3da10af56b`.
Printed p.89 prescribes dimension `d n²`; immediately before
Lemma III.1.2 on p.90, compatibility requires positive Lie rank `n` and
equality of the two totally real actions; p.91 uses these requirements
in the polarized level moduli problem and its isogeny relation.

In that source's notation the imaginary quadratic field `E` is this
module's `L`, its CM field `F` is `K`, its totally real field `F⁺` is `E`,
its acting algebra `B` is `A`, and its abelian scheme `A` is `B`.
The fixed-base quotient construction only needs the weaker field and
algebra hypotheses listed above. It is a derived prerequisite isolating
the action, dimension and positive Lie conditions; it does not claim
the source's full polarized level functor or identify the rational
isomorphism relation with geometric isogenies on arbitrary schemes.
The source's trace equivalences, polarization, level orbit,
geometric-point independence and representability remain separate
obligations.
